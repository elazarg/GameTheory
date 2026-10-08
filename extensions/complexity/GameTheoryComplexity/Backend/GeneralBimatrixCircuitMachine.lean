import GameTheoryComplexity.Backend.PointerCircuitGeneration
import GameTheoryComplexity.Backend.GeneralBimatrixPointerMachine

/-! Uniform circuit emission for serialized bimatrix path pointers.
The actual polynomial-time pointer machines are specialized to each instance
and each output bit. The emitted End-of-Line circuits agree on every vertex
at the explicit positive node width, including malformed node encodings.
-/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- The predecessor machine remains polynomial-time on paired instance/node words. -/
theorem generalBimatrixPredecessor_pair_mem_FP :
    (fun z => generalBimatrixPredecessorWord ![pairFst z, pairSnd z]) ∈ FP := by
  apply CobhamFP_subset_FP
  exact (Cobham.comp generalBimatrixPredecessorWord_cobham (fun i => by
    fin_cases i
    · exact FP_subset_CobhamFP pairFst_mem_FP
    · exact FP_subset_CobhamFP pairSnd_mem_FP)).of_eq fun _ => rfl

/-- The successor machine remains polynomial-time on paired instance/node words. -/
theorem generalBimatrixSuccessor_pair_mem_FP :
    (fun z => generalBimatrixSuccessorWord ![pairFst z, pairSnd z]) ∈ FP := by
  apply CobhamFP_subset_FP
  exact (Cobham.comp generalBimatrixSuccessorWord_cobham (fun i => by
    fin_cases i
    · exact FP_subset_CobhamFP pairFst_mem_FP
    · exact FP_subset_CobhamFP pairSnd_mem_FP)).of_eq fun _ => rfl

/-- There is an actual polynomial-time End-of-Line instance mapper whose circuits
compute the two bimatrix pointers at every vertex of the supplied node width. -/
theorem exists_generalBimatrixEndOfLineInstance :
    ∃ f : List Bool → List Bool, f ∈ FP ∧ ∀ input,
      endOfLineWidth (f input) = (generalBimatrixNodeRuler input).length ∧
        ∀ vertex, vertex.length = (generalBimatrixNodeRuler input).length →
          endOfLinePredecessor (f input) vertex = generalBimatrixPredecessorWord ![input, vertex] ∧
          endOfLineSuccessor (f input) vertex = generalBimatrixSuccessorWord ![input, vertex] := by
  obtain ⟨f, hf, heval⟩ := exists_pointerCircuitInstance generalBimatrixNodeRuler
    (fun input vertex => generalBimatrixPredecessorWord ![input, vertex])
    (fun input vertex => generalBimatrixSuccessorWord ![input, vertex])
    (CobhamFP_subset_FP generalBimatrixNodeRuler_cobham)
    generalBimatrixPredecessor_pair_mem_FP generalBimatrixSuccessor_pair_mem_FP
    (fun _ _ => generalBimatrixPredecessorWord_length _)
    (fun _ _ => generalBimatrixSuccessorWord_length _)
  exact ⟨f, hf, fun input => heval input (generalBimatrixNodeRuler_pos input)⟩

end GameTheory.Complexity.Backend