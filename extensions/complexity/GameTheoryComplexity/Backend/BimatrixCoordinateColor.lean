import GameTheoryComplexity.Backend.SpernerCoordinateColor
import GameTheoryComplexity.Backend.BimatrixRawCircuit

/-! Canonically compiled coordinate-color circuits are represented by paired game outputs.
Explicit relocated wire placements and input-error bounds connect raw circuit evaluation to
normalized color indicators. No circuit allocation or alternative coloring is assumed. -/

namespace GameTheory.Complexity.Backend.BimatrixCoordinateColor
open _root_.Complexity _root_.Complexity.CircuitCode
open GameTheory.Finite GameTheory.Finite.BimatrixAffineGate
open GameTheory.Finite.BimatrixGateProgram
variable {k : ℕ}

/-- An actually compiled color flag is approximated at its relocated output wire. -/
theorem output_correct (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (ε : ℚ)
    (hε : ε < 1 / 4) (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (source vertex : List Bool) (i : Fin 2) (offset : ℕ) (raw : RawCircuit)
    (hraw : raw.WellFormed vertex.length)
    (hquery : raw.eval? vertex = some (bitOf (gridCoordinateColor source vertex) i))
    (hsize : offset + vertex.length + raw.length ≤ k)
    (hplace : ∀ t : Fin raw.length, ∀ href : ((raw.get t).shift offset).WellFormedAt k,
      g ⟨offset + vertex.length + t.val, by omega⟩ =
        BimatrixRawGate.gate ((raw.get t).shift offset) href)
    (hinput : ∀ j : Fin k, ∀ hj0 : offset ≤ j.val, ∀ hj : j.val < offset + vertex.length,
      |(k : ℚ) * value c j - (if vertex[j.val - offset] then 1 else 0)| ≤ ε) :
    ∃ hlast : offset + (vertex.length + raw.length - 1) < k,
      |(k : ℚ) * value c ⟨offset + (vertex.length + raw.length - 1), hlast⟩ -
        (if bitOf (gridCoordinateColor source vertex) i then 1 else 0)| ≤ ε := by
  obtain ⟨bit, heval, hlast, herr⟩ := BimatrixRawCircuit.eval_correct_at H M hk g c hc
    hM hg hscale ε hε hδ offset raw vertex hraw hsize hplace hinput
  have hbit : bit = bitOf (gridCoordinateColor source vertex) i :=
    Option.some.inj (heval.symm.trans hquery)
  subst bit
  exact ⟨hlast, herr⟩

/-- At an encoded grid vertex, the relocated output approximates its canonical color flag. -/
theorem gridOutput_correct (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (ε : ℚ)
    (hε : ε < 1 / 4) (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (source vertex : List Bool) (x y : ℕ)
    (hx : x ≤ 2 ^ (pairFst source).length) (hy : y ≤ 2 ^ (pairFst source).length)
    (hvertex : vertex = Nat.toBitsLE ((pairFst source).length + 1) x ++
      Nat.toBitsLE ((pairFst source).length + 1) y)
    (i : Fin 2) (offset : ℕ) (raw : RawCircuit)
    (hraw : raw.WellFormed vertex.length)
    (hquery : raw.eval? vertex = some (bitOf (gridCoordinateColor source vertex) i))
    (hsize : offset + vertex.length + raw.length ≤ k)
    (hplace : ∀ t : Fin raw.length, ∀ href : ((raw.get t).shift offset).WellFormedAt k,
      g ⟨offset + vertex.length + t.val, by omega⟩ =
        BimatrixRawGate.gate ((raw.get t).shift offset) href)
    (hinput : ∀ j : Fin k, ∀ hj0 : offset ≤ j.val, ∀ hj : j.val < offset + vertex.length,
      |(k : ℚ) * value c j - (if vertex[j.val - offset] then 1 else 0)| ≤ ε) :
    ∃ hlast : offset + (vertex.length + raw.length - 1) < k,
      |(k : ℚ) * value c ⟨offset + (vertex.length + raw.length - 1), hlast⟩ -
        (if bitOf (encodeGridColor (spernerColor source x y)) i then 1 else 0)| ≤ ε := by
  have h := output_correct H M hk g c hc hM hg hscale ε hε hδ source vertex i offset raw
    hraw hquery hsize hplace hinput
  have he : gridCoordinateColor source vertex = encodeGridColor (spernerColor source x y) := by
    rw [hvertex]
    exact gridCoordinateColor_encode source x y hx hy
  rw [he] at h
  exact h

/-- Actual polynomial-time raw compilers recover both canonical color indicators on the grid. -/
theorem exists_compiled_gridColorCircuits :
    ∃ codes : Fin 2 → List Bool → List Bool,
      (∀ i, codes i ∈ FP) ∧ ∀ i source,
        ∃ raw : RawCircuit, RawCircuit.decode? (codes i source) = some raw ∧
          raw.WellFormed (2 * ((pairFst source).length + 1)) ∧
          ∀ x y, x ≤ 2 ^ (pairFst source).length → y ≤ 2 ^ (pairFst source).length →
            raw.eval? (Nat.toBitsLE ((pairFst source).length + 1) x ++
              Nat.toBitsLE ((pairFst source).length + 1) y) =
              some (bitOf (encodeGridColor (spernerColor source x y)) i) := by
  obtain ⟨codes, hFP, hcodes⟩ := exists_gridCoordinateColorRawCircuitGenerators
  refine ⟨codes, hFP, fun i source => ?_⟩
  obtain ⟨raw, hd, hw, he⟩ := hcodes i source
  refine ⟨raw, hd, hw, fun x y hx hy => ?_⟩
  have h := he (Nat.toBitsLE ((pairFst source).length + 1) x ++
    Nat.toBitsLE ((pairFst source).length + 1) y) (by simp; omega)
  rw [gridCoordinateColor_encode source x y hx hy] at h
  exact h

end GameTheory.Complexity.Backend.BimatrixCoordinateColor
