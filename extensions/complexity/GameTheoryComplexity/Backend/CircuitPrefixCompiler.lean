import GameTheoryComplexity.Backend.CircuitCodeRestriction
import GameTheoryComplexity.Backend.CircuitCodeValidation

/-! Polynomial-time hardwiring of serialized raw circuits. Exact syntax validation
rejects malformed inputs, and explicit guards prevent empty circuits or zero live
width from acquiring a spurious output. Invalid wire topology remains rejected. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham _root_.Complexity.CircuitCode

/-- Restrict a serialized circuit to a fixed seed and a positive live-width ruler.
Malformed syntax, empty gate lists and zero live width return the empty code. -/
def restrictCircuitCode (ruler seed code : List Bool) : List Bool :=
  caseBit₀ (andBit (nonemptyFlag ruler)
    (andBit (nonemptyFlag (circuitUnaryPrefix code)) (circuitCodeSyntaxFlag code)))
    (emitRestrictedCircuitCode ruler seed code) []

private theorem nonemptyFlag_of_ne_nil {bits : List Bool} (h : bits ≠ []) :
    nonemptyFlag bits = [true] := by
  cases bits with
  | nil => contradiction
  | cons b bits => exact nonemptyFlag_cons b bits

/-- For positive live width, hardwiring preserves exact optional evaluation on
every source code, including malformed syntax and invalid wire references. -/
theorem restrictCircuitCode_eval (ruler seed code input : List Bool)
    (hn : 0 < ruler.length) (hi : input.length = ruler.length) :
    evalCode ruler.length (restrictCircuitCode ruler seed code) input =
      evalCode (seed.length + ruler.length) code (seed ++ input) := by
  have hr := nonemptyFlag_of_ne_nil (List.length_pos_iff.mp hn)
  by_cases hs : circuitCodeSyntaxFlag code = [true]
  · obtain ⟨circuit, hd⟩ := (circuitCodeSyntaxFlag_accept code).mp hs
    have he := (RawCircuit.decode?_eq_some_iff _ _).mp hd
    subst code
    by_cases hc : circuit = []
    · subst circuit
      have hp : circuitUnaryPrefix (RawCircuit.encode []) = [] := by
        rw [RawCircuit.encode, circuitUnaryPrefix_encode]
        rfl
      have he : restrictCircuitCode ruler seed (RawCircuit.encode []) = [] := by
        rw [restrictCircuitCode, hr, hp]
        rfl
      rw [he]
      simp only [evalCode, hi, List.length_append, ↓reduceIte, hd]
      rfl
    · have hp : nonemptyFlag (circuitUnaryPrefix circuit.encode) = [true] := by
        rw [RawCircuit.encode, circuitUnaryPrefix_encode]
        exact nonemptyFlag_of_ne_nil (by simpa using hc)
      simp only [restrictCircuitCode, hr, hp, hs, andBit, caseBit₀_cons, Bool.cond_true]
      exact emitRestrictedCircuitCode_eval _ _ _ _ hn hi hc
  · have hb : circuitCodeSyntaxFlag code = [false] :=
      (circuitCodeSyntaxFlag_flag code).resolve_left hs
    have hd : RawCircuit.decode? code = none := by
      cases h : RawCircuit.decode? code with
      | none => rfl
      | some circuit => exact False.elim (hs ((circuitCodeSyntaxFlag_accept code).mpr ⟨_, h⟩))
    have hguard : andBit (nonemptyFlag (circuitUnaryPrefix code)) [false] = [false] := by
      cases h : circuitUnaryPrefix code with
      | nil => rfl
      | cons b bits => rw [nonemptyFlag_cons]; rfl
    have he : restrictCircuitCode ruler seed code = [] := by
      rw [restrictCircuitCode, hr, hb, hguard]
      rfl
    rw [he]
    simp only [evalCode, hi, List.length_append, ↓reduceIte, hd]
    rfl

/-- The complete validated compiler composes polynomial-time input producers. -/
theorem restrictCircuitCodeFn_mem_FP {r s c : List Bool → List Bool}
    (hr : r ∈ FP) (hs : s ∈ FP) (hc : c ∈ FP) :
    (fun z => restrictCircuitCode (r z) (s z) (c z)) ∈ FP := by
  have hcount := FP_subset_CobhamFP (mem_FP_comp hc circuitUnaryPrefix_mem_FP)
  have hsyntax := FP_subset_CobhamFP (mem_FP_comp hc circuitCodeSyntaxFlag_mem_FP)
  have hflag := andFn (nonemptyFn (FP_subset_CobhamFP hr))
    (andFn (nonemptyFn hcount) hsyntax)
  exact CobhamFP_subset_FP (iteFn hflag
    (FP_subset_CobhamFP (emitRestrictedCircuitCodeFn_mem_FP hr hs hc)) Cobham.empty)

/-- One polynomial-time word machine compiles paired rulers, seeds and codes. -/
theorem restrictCircuitCode_pair_mem_FP :
    (fun z => restrictCircuitCode (pairFst z) (pairFst (pairSnd z))
      (pairSnd (pairSnd z))) ∈ FP :=
  restrictCircuitCodeFn_mem_FP pairFst_mem_FP
    (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

end GameTheory.Complexity.Backend
