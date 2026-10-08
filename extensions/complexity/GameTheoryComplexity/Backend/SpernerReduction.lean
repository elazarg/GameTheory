import GameTheoryComplexity.Backend.PointerCircuitGeneration
import GameTheoryComplexity.Backend.SpernerProblem
import GameTheoryComplexity.Backend.SpernerPointerMachine
import GameTheoryComplexity.Backend.SearchReduction

/-! Uniform circuit emission turns the local Sperner machine into an End-of-Line
instance. Every target endpoint remains the same encoded triangular cell; the
answer decoder is a certified projection and does not follow a path. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Math.Sperner

/-- An actual FP mapper emits both pointer circuit vectors at the binary node width. -/
theorem exists_spernerEndOfLineInstance :
    ∃ f : List Bool → List Bool, f ∈ FP ∧
      ∀ input, endOfLineWidth (f input) = gridNodeWidth (pairFst input).length ∧
        ∀ vertex, vertex.length = gridNodeWidth (pairFst input).length →
          endOfLinePredecessor (f input) vertex = spernerPointer input true vertex ∧
          endOfLineSuccessor (f input) vertex = spernerPointer input false vertex := by
  obtain ⟨f, hf, heval⟩ := exists_pointerCircuitInstance
    (fun input => gridWidthWord (pairFst input))
    (fun input vertex => spernerPointer input true vertex)
    (fun input vertex => spernerPointer input false vertex)
    (gridWidthWordFn_mem_FP pairFst_mem_FP)
    (spernerPointer_pair_mem_FP true) (spernerPointer_pair_mem_FP false)
    (fun _ _ => gridPointerMachine_length _ _ _ _)
    (fun _ _ => gridPointerMachine_length _ _ _ _)
  refine ⟨f, hf, fun input => ?_⟩
  have hn : 0 < (gridWidthWord (pairFst input)).length := by
    simp [gridWidthWord, gridNodeWidth]
  simpa only [gridWidthWord, List.length_replicate] using heval input hn

private theorem compiledSperner_source (f : List Bool → List Bool) (input : List Bool)
    (hwidth : endOfLineWidth (f input) = gridNodeWidth (pairFst input).length)
    (hptr : ∀ vertex, vertex.length = gridNodeWidth (pairFst input).length →
      endOfLinePredecessor (f input) vertex = spernerPointer input true vertex ∧
      endOfLineSuccessor (f input) vertex = spernerPointer input false vertex) :
    endOfLineSourceValid (f input) := by
  have ho : endOfLineOrigin (f input) = encodeGridNode (pairFst input).length none := by
    simp only [endOfLineOrigin, hwidth, encodeGridNode]
  have hsource := spernerPointer_source input
  have h₀ := hptr (encodeGridNode (pairFst input).length none) (encodeGridNode_length _ _)
  have h₁ := hptr (spernerPointer input false (encodeGridNode (pairFst input).length none))
    ((gridPointerMachine_length _ _ _ _).trans (encodeGridNode_length _ _))
  exact ⟨by rw [ho, h₀.1]; exact hsource.1,
    by rw [ho, h₀.2]; exact hsource.2.1,
    by rw [ho, h₀.2, h₁.1]; exact hsource.2.2⟩

/-- Exact-width pointer compilation preserves every End-of-Line answer, including
endpoints on components disconnected from the source. -/
def spernerToEndOfLineReductionOfCircuitInstance (f : List Bool → List Bool) (hf : f ∈ FP)
    (heval : ∀ input, endOfLineWidth (f input) = gridNodeWidth (pairFst input).length ∧
      ∀ vertex, vertex.length = gridNodeWidth (pairFst input).length →
        endOfLinePredecessor (f input) vertex = spernerPointer input true vertex ∧
        endOfLineSuccessor (f input) vertex = spernerPointer input false vertex) :
    SearchReduction spernerRelation endOfLineRelation where
  instanceMap := f
  instanceMap_mem_FP := hf
  decode := fun v => v 1
  decode_mem_FPn := cobham_iff_FPn.mp (Cobham.proj 1)
  sound := by
    intro input witness hw
    change spernerRelation input witness
    obtain ⟨hwidth, hptr⟩ := heval input
    have hsource := compiledSperner_source f input hwidth hptr
    rcases hw with ⟨_, hlen, hne, hend⟩ | ⟨hbad, _⟩
    · have hlen' := hlen.trans hwidth
      have hv := hptr witness hlen'
      have hp := hptr (spernerPointer input true witness)
        ((gridPointerMachine_length _ _ _ _).trans hlen')
      have hs := hptr (spernerPointer input false witness)
        ((gridPointerMachine_length _ _ _ _).trans hlen')
      have he : GameTheory.Math.EndOfLine.IsEndpoint
          (spernerPointer input true) (spernerPointer input false) witness := by
        simpa only [GameTheory.Math.EndOfLine.IsEndpoint,
          GameTheory.Math.EndOfLine.HasPredecessor, GameTheory.Math.EndOfLine.HasSuccessor,
          hv.1, hv.2, hp.2, hs.1] using hend
      have hne' : witness ≠ encodeGridNode (pairFst input).length none := by
        simpa only [endOfLineOrigin, hwidth, encodeGridNode] using hne
      obtain ⟨t, hd, _, ht⟩ := spernerPointer_endpoint_decodes input witness hne' he
      exact ⟨t, hd, ht⟩
    · exact False.elim (hbad hsource)

/-- Both instance compilation and the every-answer projection have actual FP certificates. -/
theorem exists_spernerToEndOfLineReduction :
    Nonempty (SearchReduction spernerRelation endOfLineRelation) := by
  obtain ⟨f, hf, heval⟩ := exists_spernerEndOfLineInstance
  exact ⟨spernerToEndOfLineReductionOfCircuitInstance f hf heval⟩

end GameTheory.Complexity.Backend
