module

public import GameTheoryComplexity.Backend.GeneralBimatrixCircuitMachine

@[expose] public section

/-! Circuit emission preserves all vertices at the serialized node width. -/
namespace GameTheory.Complexity.Tests.GeneralBimatrixCircuitMachine
open Backend Turing.MultiTapeTM

private def input : List Bool := encodeGeneralInstance 1 1 1 (fun _ _ => 0) (fun _ _ => 0)

private theorem input_valid : GeneralInstanceValid input :=
  encodeGeneralInstance_valid 1 1 1 _ _ (by decide) (by decide) (by decide)

-- Native certificates charge the complete instance and candidate node.
example : ComputableInPolyTime
    (fun p : List Bool × List Bool => generalBimatrixPredecessorWord ![p.1, p.2])
    (encPair encBits encBits) encBits := generalBimatrixPredecessor_joint_polyTime
example : ComputableInPolyTime
    (fun p : List Bool × List Bool => generalBimatrixSuccessorWord ![p.1, p.2])
    (encPair encBits encBits) encBits := generalBimatrixSuccessor_joint_polyTime

-- Compilation agrees on every eight-bit word, without assuming it decodes to a port.
example : ∃ f : List Bool → List Bool, ComputableInPolyTime f encBits encBits ∧ endOfLineWidth (f input) = 8 ∧
    ∀ vertex, vertex.length = 8 →
      endOfLinePredecessor (f input) vertex = generalBimatrixPredecessorWord ![input, vertex] ∧
      endOfLineSuccessor (f input) vertex = generalBimatrixSuccessorWord ![input, vertex] := by
  obtain ⟨f, hf, heval⟩ := exists_generalBimatrixEndOfLineInstance
  have hw : (generalBimatrixNodeRuler input).length = 8 := by
    rw [generalBimatrixNodeRuler_length input input_valid]
    decide +kernel
  exact ⟨f, hf, by simpa only [hw] using heval input⟩

-- An invalid instance still compiles at the positive fallback width.
example : ∃ f : List Bool → List Bool, ComputableInPolyTime f encBits encBits ∧ endOfLineWidth (f []) = 1 ∧
    ∀ vertex, vertex.length = 1 →
      endOfLinePredecessor (f []) vertex = generalBimatrixPredecessorWord ![[], vertex] ∧
      endOfLineSuccessor (f []) vertex = generalBimatrixSuccessorWord ![[], vertex] := by
  obtain ⟨f, hf, heval⟩ := exists_generalBimatrixEndOfLineInstance
  have hw : (generalBimatrixNodeRuler []).length = 1 := by decide +kernel
  exact ⟨f, hf, by simpa only [hw] using heval []⟩

-- The malformed-instance fallback really isolates both possible one-bit vertices.
example : generalBimatrixPredecessorWord ![[], [false]] = [false] ∧
    generalBimatrixSuccessorWord ![[], [false]] = [false] ∧
    generalBimatrixPredecessorWord ![[], [true]] = [true] ∧
    generalBimatrixSuccessorWord ![[], [true]] = [true] := by decide +kernel

end GameTheory.Complexity.Tests.GeneralBimatrixCircuitMachine
