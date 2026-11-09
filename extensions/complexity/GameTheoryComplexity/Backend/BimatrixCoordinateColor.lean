module

public import GameTheoryComplexity.Backend.SpernerCoordinateColor
public import GameTheoryComplexity.Backend.BimatrixRawCircuit

@[expose] public section

/-! Checked native coordinate-color circuits are represented by paired game
outputs. Explicit relocated gate placements and live input-wire errors connect
the designated native output to the canonical grid-color indicators. -/

namespace GameTheory.Complexity.Backend.BimatrixCoordinateColor

open Cslib.Circuits Cslib.BitString Turing.MultiTapeTM
open GameTheory.Finite GameTheory.Finite.BimatrixAffineGate
open GameTheory.Finite.BimatrixGateProgram

variable {k : ℕ}

/-- A checked coordinate-color flag is approximated at its selected relocated wire. -/
theorem output_correct (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (ε : ℚ)
    (hε : ε < 1 / 4) (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (source vertex : List Bool) (i : Fin 2) (offset : ℕ)
    (gates : List (CircuitFormat.signature.Op × List ℕ))
    (hraw : Program.IsCodeFrom CircuitFormat.signature vertex.length 0 gates)
    (output : Fin (vertex.length + gates.length))
    (hquery : CircuitFormat.evalOutput vertex gates output.val =
      (gridCoordinateColor source vertex).getD i.val false)
    (hsize : offset + vertex.length + gates.length ≤ k)
    (hplace : ∀ t : Fin gates.length,
      ∀ href : Program.IsCodeFrom CircuitFormat.signature k 0
        [(gates[t].1, gates[t].2.map (offset + ·))],
      g ⟨offset + vertex.length + t.val, by omega⟩ =
        BimatrixRawGate.gate (gates[t].1, gates[t].2.map (offset + ·)) href)
    (hinput : ∀ j : Fin k, offset ≤ j.val → j.val < offset + vertex.length →
      |(k : ℚ) * value c j - (if vertex.getD (j.val - offset) false then 1 else 0)| ≤ ε) :
    |(k : ℚ) * value c ⟨offset + output.val, by omega⟩ -
      (if (gridCoordinateColor source vertex).getD i.val false then 1 else 0)| ≤ ε := by
  have h := BimatrixRawCircuit.evalOutput_correct_at H M hk g c hc hM hg hscale ε hε hδ
    offset gates vertex hraw hsize hplace hinput output
  rw [hquery] at h
  exact h

/-- An encoded grid vertex's selected output approximates its canonical color flag. -/
theorem gridOutput_correct (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (ε : ℚ)
    (hε : ε < 1 / 4) (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (source vertex : List Bool) (x y : ℕ)
    (hx : x ≤ 2 ^ (CircuitWords.first source).length)
    (hy : y ≤ 2 ^ (CircuitWords.first source).length)
    (hvertex : vertex = lowBits ((CircuitWords.first source).length + 1) x ++
      lowBits ((CircuitWords.first source).length + 1) y)
    (i : Fin 2) (offset : ℕ) (gates : List (CircuitFormat.signature.Op × List ℕ))
    (hraw : Program.IsCodeFrom CircuitFormat.signature vertex.length 0 gates)
    (output : Fin (vertex.length + gates.length))
    (hquery : CircuitFormat.evalOutput vertex gates output.val =
      (gridCoordinateColor source vertex).getD i.val false)
    (hsize : offset + vertex.length + gates.length ≤ k)
    (hplace : ∀ t : Fin gates.length,
      ∀ href : Program.IsCodeFrom CircuitFormat.signature k 0
        [(gates[t].1, gates[t].2.map (offset + ·))],
      g ⟨offset + vertex.length + t.val, by omega⟩ =
        BimatrixRawGate.gate (gates[t].1, gates[t].2.map (offset + ·)) href)
    (hinput : ∀ j : Fin k, offset ≤ j.val → j.val < offset + vertex.length →
      |(k : ℚ) * value c j - (if vertex.getD (j.val - offset) false then 1 else 0)| ≤ ε) :
    |(k : ℚ) * value c ⟨offset + output.val, by omega⟩ -
      (if (encodeGridColor (spernerColor source x y)).getD i.val false then 1 else 0)| ≤ ε := by
  have h := output_correct H M hk g c hc hM hg hscale ε hε hδ source vertex i offset gates
    hraw output hquery hsize hplace hinput
  have he : gridCoordinateColor source vertex = encodeGridColor (spernerColor source x y) := by
    rw [hvertex]
    exact gridCoordinateColor_encode source x y hx hy
  rw [he] at h
  exact h

/-- Native raw compilers recover both grid-color indicators with official topology witnesses. -/
theorem exists_compiled_gridColorCircuits :
    ∃ codes : Fin 2 → List Bool → List Bool,
      (∀ i, ComputableInPolyTime (codes i) encBits encBits) ∧
      ∀ i source,
        ∃ gates : List (CircuitFormat.signature.Op × List ℕ),
          ∃ output : Fin (2 * ((CircuitWords.first source).length + 1) + gates.length),
            CircuitFormat.decode? (codes i source) = some gates ∧
            Program.IsCodeFrom CircuitFormat.signature
              (2 * ((CircuitWords.first source).length + 1)) 0 gates ∧ gates ≠ [] ∧
            output.val = 2 * ((CircuitWords.first source).length + 1) + gates.length - 1 ∧
            ∀ x y, x ≤ 2 ^ (CircuitWords.first source).length →
              y ≤ 2 ^ (CircuitWords.first source).length →
              CircuitFormat.evalOutput
                (lowBits ((CircuitWords.first source).length + 1) x ++
                  lowBits ((CircuitWords.first source).length + 1) y) gates output.val =
                (encodeGridColor (spernerColor source x y)).getD i.val false := by
  obtain ⟨codes, hcodes, hraw⟩ := exists_gridCoordinateColorCircuitCodes
  refine ⟨codes, hcodes, ?_⟩
  intro i source
  obtain ⟨gates, output, hdecode, hvalid, hnonempty, hlast, heval⟩ := hraw i source
  refine ⟨gates, output, hdecode, hvalid, hnonempty, hlast, ?_⟩
  intro x y hx hy
  have h := heval
    (lowBits ((CircuitWords.first source).length + 1) x ++
      lowBits ((CircuitWords.first source).length + 1) y) (by simp; omega)
  rw [gridCoordinateColor_encode source x y hx hy] at h
  exact h

end GameTheory.Complexity.Backend.BimatrixCoordinateColor
