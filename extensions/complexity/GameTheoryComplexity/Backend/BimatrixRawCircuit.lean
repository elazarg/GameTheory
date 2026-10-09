import GameTheoryComplexity.Backend.BimatrixRawGate
import Complexitylib.Circuits.Encoding.Shift
/-! A single paired-action game evaluates a topologically ordered raw circuit.
The invariant follows the canonical memo-array evaluator: primary input errors
are bounded initially, and each comparator output resets its error to the common
block normalization bound, independently of circuit depth. -/
namespace GameTheory.Complexity.Backend.BimatrixRawCircuit
open _root_.Complexity _root_.Complexity.CircuitCode
open GameTheory.Finite GameTheory.Finite.BimatrixCertificate
open GameTheory.Finite.BimatrixAffineGate GameTheory.Finite.BimatrixGateProgram
open scoped BigOperators
variable {k : ℕ}

/-- A relocated circuit preserves approximation bounds only on its live memo wires. -/
theorem evalAux_correct_at (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (ε : ℚ)
    (hε : ε < 1 / 4) (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (offset : ℕ) (raw : RawCircuit) (wires : Array Bool)
    (htopo : raw.TopologicallyWellFormed wires.size) (hsize : offset + wires.size + raw.length ≤ k)
    (hplace : ∀ t : Fin raw.length, ∀ href : ((raw.get t).shift offset).WellFormedAt k,
      g ⟨offset + wires.size + t.val, by omega⟩ =
        BimatrixRawGate.gate ((raw.get t).shift offset) href)
    (hinput : ∀ j : Fin k, ∀ hj0 : offset ≤ j.val, ∀ hj : j.val < offset + wires.size,
      |(k : ℚ) * value c j - (if wires[j.val - offset] then 1 else 0)| ≤ ε) :
    ∃ out : Array Bool, raw.evalAux? wires = some out ∧
      out.size = wires.size + raw.length ∧
      ∀ j : Fin k, ∀ hj0 : offset ≤ j.val, ∀ hj : j.val < offset + out.size,
        |(k : ℚ) * value c j - (if out[j.val - offset] then 1 else 0)| ≤ ε := by
  induction raw generalizing wires with
  | nil => exact ⟨wires, rfl, by simp, hinput⟩
  | cons a tail ih =>
    have hlen : (a :: tail).length = tail.length + 1 := rfl
    have hslot : offset + wires.size < k := by omega
    have ha : a.WellFormedAt wires.size := by
      simpa using htopo ⟨0, by simp⟩
    have ha0 := ha.1
    have ha1 := ha.2
    have haref : (a.shift offset).WellFormedAt k := by
      change offset + a.input₀ < k ∧ offset + a.input₁ < k
      constructor <;> omega
    let bit := a.eval wires[a.input₀] wires[a.input₁]
    have ht : RawCircuit.TopologicallyWellFormed (wires.push bit).size tail := by
      intro t
      have hh := htopo t.succ
      change (tail.get t).WellFormedAt (wires.size + (t.val + 1)) at hh
      simpa only [Array.size_push, Fin.val_succ, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hh
    have hsz : offset + (wires.push bit).size + tail.length ≤ k := by
      rw [Array.size_push]
      omega
    have hp : ∀ t : Fin tail.length, ∀ href : ((tail.get t).shift offset).WellFormedAt k,
        g ⟨offset + (wires.push bit).size + t.val, by omega⟩ =
          BimatrixRawGate.gate ((tail.get t).shift offset) href := by
      intro t href
      have hh := hplace t.succ href
      change g ⟨offset + wires.size + (t.val + 1), by omega⟩ =
        BimatrixRawGate.gate ((tail.get t).shift offset) href at hh
      simpa only [Array.size_push, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hh
    have hnew : |(k : ℚ) * value c ⟨offset + wires.size, hslot⟩ -
        (if bit then 1 else 0)| ≤ ε := by
      have he := (BimatrixRawGate.gate_output_error H M (a.shift offset) haref hk g c hc
        hM hg hscale ⟨offset + wires.size, hslot⟩
        (by simpa using hplace ⟨0, by simp⟩ haref)
        wires[a.input₀] wires[a.input₁] ε
        (by simpa only [RawGate.shift, Nat.add_sub_cancel_left] using
          (hinput ⟨offset + a.input₀, haref.1⟩
            (by change offset ≤ offset + a.input₀; omega)
            (by change offset + a.input₀ < offset + wires.size; omega)))
        (by simpa only [RawGate.shift, Nat.add_sub_cancel_left] using
          (hinput ⟨offset + a.input₁, haref.2⟩
            (by change offset ≤ offset + a.input₁; omega)
            (by change offset + a.input₁ < offset + wires.size; omega))) hε).trans hδ
      simpa only [RawGate.eval_shift] using he
    have hin : ∀ j : Fin k, ∀ hj0 : offset ≤ j.val,
        ∀ hj : j.val < offset + (wires.push bit).size,
        |(k : ℚ) * value c j - (if (wires.push bit)[j.val - offset] then 1 else 0)| ≤ ε := by
      intro j hj0 hj
      by_cases hlt : j.val - offset < wires.size
      · simpa only [Array.getElem_push_lt hlt] using hinput j hj0 (by omega)
      · have he : j.val = offset + wires.size := by simp only [Array.size_push] at hj; omega
        have hjEq : j = ⟨offset + wires.size, hslot⟩ := Fin.ext he
        simpa only [hjEq, Nat.add_sub_cancel_left, Array.getElem_push_eq] using hnew
    obtain ⟨out, ho, hlen, herr⟩ := ih (wires.push bit) ht hsz hp hin
    refine ⟨out, ?_, ?_, herr⟩
    · simp only [RawCircuit.evalAux?, Array.getElem?_eq_getElem ha.1,
        Array.getElem?_eq_getElem ha.2]
      exact ho
    · rw [hlen, Array.size_push, List.length_cons]
      omega


/-- The output of a relocated circuit is approximated independently of earlier game wires. -/
theorem eval_correct_at (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (ε : ℚ)
    (hε : ε < 1 / 4) (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (offset : ℕ) (raw : RawCircuit) (input : List Bool)
    (hraw : raw.WellFormed input.length) (hsize : offset + input.length + raw.length ≤ k)
    (hplace : ∀ t : Fin raw.length, ∀ href : ((raw.get t).shift offset).WellFormedAt k,
      g ⟨offset + input.length + t.val, by omega⟩ =
        BimatrixRawGate.gate ((raw.get t).shift offset) href)
    (hinput : ∀ j : Fin k, ∀ hj0 : offset ≤ j.val, ∀ hj : j.val < offset + input.length,
      |(k : ℚ) * value c j - (if input[j.val - offset] then 1 else 0)| ≤ ε) :
    ∃ bit : Bool, raw.eval? input = some bit ∧
      ∃ hlast : offset + (input.length + raw.length - 1) < k,
        |(k : ℚ) * value c ⟨offset + (input.length + raw.length - 1), hlast⟩ -
          (if bit then 1 else 0)| ≤ ε := by
  have htopo : raw.TopologicallyWellFormed input.toArray.size := by
    simpa only [List.size_toArray] using hraw.2
  have hbound : offset + input.toArray.size + raw.length ≤ k := by
    simpa only [List.size_toArray] using hsize
  have hplacement : ∀ t : Fin raw.length,
      ∀ href : ((raw.get t).shift offset).WellFormedAt k,
      g ⟨offset + input.toArray.size + t.val, by omega⟩ =
        BimatrixRawGate.gate ((raw.get t).shift offset) href := by
    simpa only [List.size_toArray] using hplace
  have hin : ∀ j : Fin k, ∀ hj0 : offset ≤ j.val, ∀ hj : j.val < offset + input.toArray.size,
      |(k : ℚ) * value c j - (if input.toArray[j.val - offset] then 1 else 0)| ≤ ε := by
    simpa only [List.size_toArray, List.getElem_toArray] using hinput
  obtain ⟨out, ho, hlen, herr⟩ := evalAux_correct_at H M hk g c hc hM hg hscale ε hε hδ offset
    raw input.toArray htopo hbound hplacement hin
  have hnonempty : 0 < raw.length := List.length_pos_iff.mpr hraw.1
  have hempty : raw.isEmpty = false := by simpa using hraw.1
  have hi : input.length + raw.length - 1 < out.size := by
    simp only [List.size_toArray] at hlen
    omega
  have hlast : offset + (input.length + raw.length - 1) < k := by omega
  refine ⟨out[input.length + raw.length - 1], ?_, hlast, ?_⟩
  · simp only [RawCircuit.eval?, hempty, Bool.false_eq_true, ite_false, ho]
    change out[input.length + raw.length - 1]? = some out[input.length + raw.length - 1]
    exact Array.getElem?_eq_getElem hi
  · have hh := herr ⟨offset + (input.length + raw.length - 1), hlast⟩
      (by change offset ≤ offset + (input.length + raw.length - 1); omega)
      (by change offset + (input.length + raw.length - 1) < offset + out.size; omega)
    simpa only [Nat.add_sub_cancel_left] using hh
/-- The canonical memo evaluator succeeds and every stored wire retains its error bound. -/
theorem evalAux_correct (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (ε : ℚ)
    (hε : ε < 1 / 4) (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (raw : RawCircuit) (wires : Array Bool)
    (htopo : raw.TopologicallyWellFormed wires.size) (hsize : wires.size + raw.length ≤ k)
    (hplace : ∀ t : Fin raw.length, ∀ href : (raw.get t).WellFormedAt k,
      g ⟨wires.size + t.val, by omega⟩ = BimatrixRawGate.gate (raw.get t) href)
    (hinput : ∀ j : Fin k, ∀ hj : j.val < wires.size,
      |(k : ℚ) * value c j - (if wires[j.val] then 1 else 0)| ≤ ε) :
    ∃ out : Array Bool, raw.evalAux? wires = some out ∧
      out.size = wires.size + raw.length ∧
      ∀ j : Fin k, ∀ hj : j.val < out.size,
        |(k : ℚ) * value c j - (if out[j.val] then 1 else 0)| ≤ ε := by
  have hp : ∀ t : Fin raw.length, ∀ href : ((raw.get t).shift 0).WellFormedAt k,
      g ⟨0 + wires.size + t.val, by omega⟩ =
        BimatrixRawGate.gate ((raw.get t).shift 0) href := by
    intro t href
    simpa only [RawGate.shift, Nat.zero_add] using
      hplace t (by simpa only [RawGate.shift, Nat.zero_add] using href)
  have hh := evalAux_correct_at H M hk g c hc hM hg hscale ε hε hδ 0 raw wires htopo
    (by simpa only [Nat.zero_add] using hsize) hp
    (fun j _ hj => hinput j (by simpa only [Nat.zero_add] using hj))
  simpa only [Nat.zero_le, Nat.zero_add, Nat.sub_zero, forall_true_left] using hh
/-- The designated output of the canonical raw evaluator is represented by its game slot. -/
theorem eval_correct (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (ε : ℚ)
    (hε : ε < 1 / 4) (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (raw : RawCircuit) (input : List Bool)
    (hraw : raw.WellFormed input.length) (hsize : input.length + raw.length ≤ k)
    (hplace : ∀ t : Fin raw.length, ∀ href : (raw.get t).WellFormedAt k,
      g ⟨input.length + t.val, by omega⟩ = BimatrixRawGate.gate (raw.get t) href)
    (hinput : ∀ j : Fin k, ∀ hj : j.val < input.length,
      |(k : ℚ) * value c j - (if input[j.val] then 1 else 0)| ≤ ε) :
    ∃ bit : Bool, raw.eval? input = some bit ∧
      ∃ hlast : input.length + raw.length - 1 < k,
        |(k : ℚ) * value c ⟨input.length + raw.length - 1, hlast⟩ -
          (if bit then 1 else 0)| ≤ ε := by
  have htopo : raw.TopologicallyWellFormed input.toArray.size := by
    simpa only [List.size_toArray] using hraw.2
  have hbound : input.toArray.size + raw.length ≤ k := by
    simpa only [List.size_toArray] using hsize
  have hplacement : ∀ t : Fin raw.length, ∀ href : (raw.get t).WellFormedAt k,
      g ⟨input.toArray.size + t.val, by omega⟩ = BimatrixRawGate.gate (raw.get t) href := by
    simpa only [List.size_toArray] using hplace
  have hin : ∀ j : Fin k, ∀ hj : j.val < input.toArray.size,
      |(k : ℚ) * value c j - (if input.toArray[j.val] then 1 else 0)| ≤ ε := by
    simpa only [List.size_toArray, List.getElem_toArray] using hinput
  obtain ⟨out, ho, hlen, herr⟩ := evalAux_correct H M hk g c hc hM hg hscale ε hε hδ
    raw input.toArray htopo hbound hplacement hin
  have hnonempty : 0 < raw.length := List.length_pos_iff.mpr hraw.1
  have hempty : raw.isEmpty = false := by simpa using hraw.1
  have hi : input.length + raw.length - 1 < out.size := by
    simp only [List.size_toArray] at hlen
    omega
  have hlast : input.length + raw.length - 1 < k := by omega
  refine ⟨out[input.length + raw.length - 1], ?_, hlast, ?_⟩
  · simp only [RawCircuit.eval?, hempty, Bool.false_eq_true, ite_false, ho]
    change out[input.length + raw.length - 1]? = some out[input.length + raw.length - 1]
    exact Array.getElem?_eq_getElem hi
  · exact herr ⟨input.length + raw.length - 1, hlast⟩ hi


end GameTheory.Complexity.Backend.BimatrixRawCircuit
