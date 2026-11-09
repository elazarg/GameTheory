module

public import GameTheoryComplexity.Backend.PointerCircuitGeneration
public import GameTheoryComplexity.Backend.GeneralBimatrixPointerMachine

@[expose] public section

/-! Native uniform circuit emission specializes the serialized bimatrix path
pointers on every vertex of the prescribed node width. Malformed node words
retain the pointers' identity behavior. -/
namespace GameTheory.Complexity.Backend
open Turing.MultiTapeTM

private theorem pointerArguments_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => ![p.1, p.2])
      (encPair encBits encBits) (encPi encBits) := by
  apply ComputableInPolyTime.pi
  intro i
  fin_cases i
  · exact .fst encBits encBits
  · exact .snd encBits encBits

/-- Native predecessor execution charges the complete instance and node. -/
theorem generalBimatrixPredecessor_joint_polyTime :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => generalBimatrixPredecessorWord ![p.1, p.2])
      (encPair encBits encBits) encBits :=
  generalBimatrixPredecessorWord_polyTime.comp pointerArguments_polyTime

/-- Native successor execution charges the complete instance and node. -/
theorem generalBimatrixSuccessor_joint_polyTime :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => generalBimatrixSuccessorWord ![p.1, p.2])
      (encPair encBits encBits) encBits :=
  generalBimatrixSuccessorWord_polyTime.comp pointerArguments_polyTime

/-- Compile the actual total pointers at the computed width, preserving every vertex. -/
theorem exists_generalBimatrixEndOfLineInstance :
    ∃ f : List Bool → List Bool, ComputableInPolyTime f encBits encBits ∧ ∀ input,
      endOfLineWidth (f input) = (generalBimatrixNodeRuler input).length ∧
        ∀ vertex, vertex.length = (generalBimatrixNodeRuler input).length →
          endOfLinePredecessor (f input) vertex = generalBimatrixPredecessorWord ![input, vertex] ∧
          endOfLineSuccessor (f input) vertex = generalBimatrixSuccessorWord ![input, vertex] := by
  obtain ⟨f, hf, hwidth, heval⟩ := exists_pointerCircuitInstance
    (ComputableInPolyTime.length_bits_comp generalBimatrixNodeRuler_polyTime)
    generalBimatrixPredecessor_joint_polyTime generalBimatrixSuccessor_joint_polyTime
    (fun _ _ hu => (generalBimatrixPredecessorWord_length _).trans hu)
    (fun _ _ hu => (generalBimatrixSuccessorWord_length _).trans hu)
  exact ⟨f, hf, fun input => ⟨hwidth input, heval input⟩⟩

end GameTheory.Complexity.Backend
