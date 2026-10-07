import GameTheoryComplexity.Backend.PointerCircuitGeneration
import GameTheoryComplexity.Backend.EndOfLineVerifier

/-! Uniform circuit generation serializes consistent-edge normalization of
End-of-Line pointers. A shared polynomial-time compiler specializes their scalar
bit queries. Invalid source promises map to the empty instance. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open EndOfLineMachineOps

private theorem source_width_pos {input : List Bool} (h : endOfLineSourceValid input) :
    0 < endOfLineWidth input := by
  by_contra hn
  have hz : endOfLineWidth input = 0 := by omega
  have ho : endOfLineOrigin input = [] := by simp [endOfLineOrigin, hz]
  have hs : endOfLineSuccessor input (endOfLineOrigin input) = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [endOfLineSuccessor, evaluateCircuitVector_length, ho]
    rfl
  exact h.2.1 (hs.trans ho.symm)

/-- An actual polynomial-time mapper serializes normalized pointers at the same
width for valid sources and returns the empty instance for invalid sources. -/
theorem exists_normalizedEndOfLineInstance :
    ∃ f : List Bool → List Bool, f ∈ FP ∧
      (∀ input, endOfLineSourceValid input →
        endOfLineWidth (f input) = endOfLineWidth input ∧
          ∀ vertex, vertex.length = endOfLineWidth input →
            endOfLinePredecessor (f input) vertex =
                endOfLineNormalizedPredecessor input vertex ∧
            endOfLineSuccessor (f input) vertex = endOfLineNormalizedSuccessor input vertex) ∧
      (∀ input, ¬endOfLineSourceValid input → f input = []) := by
  obtain ⟨g, hg, hgen⟩ := exists_pointerCircuitInstance pairFst
    endOfLineNormalizedPredecessor endOfLineNormalizedSuccessor pairFst_mem_FP
    (normalizedPredecessorFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
    (normalizedSuccessorFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)
    endOfLineNormalizedPredecessor_length endOfLineNormalizedSuccessor_length
  let f := fun input => caseBit₀ (endOfLineSourceFlag input) (g input) []
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  refine ⟨f, selectFn_mem_FP (endOfLineSourceFlagFn_mem_FP hid) hg (constFn_mem_FP []),
    ?_, ?_⟩
  · intro input hsource
    have hflag := (endOfLineSourceFlag_accept input).mpr hsource
    have hf : f input = g input := by simp [f, hflag, caseBit₀]
    rw [hf]
    exact hgen input (source_width_pos hsource)
  · intro input hinvalid
    have hflag := (endOfLineSourceFlag_flag input).resolve_left
      (fun h => hinvalid ((endOfLineSourceFlag_accept input).mp h))
    simp [f, hflag, caseBit₀]

end GameTheory.Complexity.Backend
