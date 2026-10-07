import GameTheoryComplexity.Backend.RawEndOfLineReduction
import GameTheoryComplexity.Backend.EndOfLinePointerNormalization

/-! A polynomial-time instance normalizer yields a search reduction when its
serialized pointers agree with consistent-edge normalization on every vertex.
The decoder returns the target witness unchanged, including the empty fallback. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

private theorem normalized_source {input : List Bool}
    (h : endOfLineSourceValid input) :
    endOfLineNormalizedPredecessor input (endOfLineOrigin input) = endOfLineOrigin input ∧
      endOfLineNormalizedSuccessor input (endOfLineOrigin input) ≠ endOfLineOrigin input := by
  constructor
  · rw [endOfLineNormalizedPredecessor_eq,
      GameTheory.Math.EndOfLine.normalizePredecessor]
    split_ifs
    · exact h.1
    · rfl
  · rw [endOfLineNormalizedSuccessor_eq,
      GameTheory.Math.EndOfLine.normalizeSuccessor_ne_self_iff]
    exact ⟨h.2.1, h.2.2⟩

/-- Exact serialized pointer semantics suffice for an every-answer reduction. -/
def endpointToRawReductionOfNormalization (f : List Bool → List Bool) (hf : f ∈ FP)
    (hvalid : ∀ input, endOfLineSourceValid input →
      endOfLineWidth (f input) = endOfLineWidth input ∧
        ∀ vertex, vertex.length = endOfLineWidth input →
          endOfLinePredecessor (f input) vertex = endOfLineNormalizedPredecessor input vertex ∧
          endOfLineSuccessor (f input) vertex = endOfLineNormalizedSuccessor input vertex)
    (hinvalid : ∀ input, ¬endOfLineSourceValid input → f input = []) :
    SearchReduction endOfLineRelation rawEndOfLineRelation where
  instanceMap := f
  instanceMap_mem_FP := hf
  decode := fun v => v 1
  decode_mem_FPn := cobham_iff_FPn.mp (Cobham.proj 1)
  sound := by
    intro input witness hw
    change endOfLineRelation input witness
    by_cases hsource : endOfLineSourceValid input
    · obtain ⟨hwidth, hpointers⟩ := hvalid input hsource
      have horigin : endOfLineOrigin (f input) = endOfLineOrigin input := by
        simp only [endOfLineOrigin, hwidth]
      have ho := hpointers (endOfLineOrigin input) List.length_replicate
      have hn := normalized_source hsource
      have hraw : rawEndOfLineSourceValid (f input) := by
        exact ⟨by rw [horigin, ho.1, hn.1], by rw [horigin, ho.2]; exact hn.2⟩
      rcases hw with ⟨_, hlen, hw⟩ | ⟨hbad, _⟩
      · have hlen' : witness.length = endOfLineWidth input := hlen.trans hwidth
        have hv := hpointers witness hlen'
        have hnp := hpointers (endOfLineNormalizedPredecessor input witness)
          ((endOfLineNormalizedPredecessor_length input witness).trans hlen')
        have hns := hpointers (endOfLineNormalizedSuccessor input witness)
          ((endOfLineNormalizedSuccessor_length input witness).trans hlen')
        have hw' : GameTheory.Math.EndOfLine.RawWitness
            (endOfLineNormalizedPredecessor input) (endOfLineNormalizedSuccessor input)
            (endOfLineOrigin input) witness := by
          simpa only [GameTheory.Math.EndOfLine.RawWitness, horigin,
            hv.1, hv.2, hnp.2, hns.1] using hw
        obtain ⟨hne, hend⟩ := (endOfLineNormalized_rawWitness_iff hsource).mp hw'
        exact Or.inl ⟨hsource, hlen', hne, hend⟩
      · exact False.elim (hbad hraw)
    · rw [hinvalid input hsource] at hw
      have hraw : ¬rawEndOfLineSourceValid [] := by
        simp [rawEndOfLineSourceValid, endOfLineOrigin, endOfLineWidth,
          endOfLineSuccessor, evaluateCircuitVector, pairFst]
      rcases hw with ⟨hbad, _, _⟩ | ⟨_, rfl⟩
      · exact False.elim (hraw hbad)
      · exact Or.inr ⟨hsource, rfl⟩

end GameTheory.Complexity.Backend
