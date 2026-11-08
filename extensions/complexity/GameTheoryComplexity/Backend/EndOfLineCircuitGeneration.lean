module

public import GameTheoryComplexity.Backend.CircuitVectorEmission
public import GameTheoryComplexity.Backend.EndOfLineProblem
public import GameTheoryComplexity.Backend.NativeEndOfLineSemantics

@[expose] public section

/-! Uniform circuit instances for native active-edge pointers.
The instance stores a true unary width ruler followed by predecessor and successor
circuit vectors in the concrete doubled-word byte format. The construction keeps
the prescribed width and the exact filtered pointer values on its input cube.
-/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM

/-- Construct an efficient concrete instance whose decoded pointers are the
native active incoming and outgoing maps on the prescribed finite cube. -/
theorem exists_activeEndOfLineInstance {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {P S : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hP_length : ∀ a (u : List Bool), u.length = n a → (P (a, u)).length = n a)
    (hS_length : ∀ a (u : List Bool), u.length = n a → (S (a, u)).length = n a) :
    ∃ inst : α → List Bool,
      ComputableInPolyTime inst enc encBits ∧
      (∀ a, endOfLineWidth (inst a) = n a) ∧
      ∀ a (u : List Bool), u.length = n a →
        endOfLinePredecessor (inst a) u = NativeEndOfLine.activePredecessor n P S (a, u) ∧
        endOfLineSuccessor (inst a) u = Cslib.Complexity.ppadToPppMap n P S (a, u) := by
  obtain ⟨predecessors, hpredecessors, hpredecessor_eval⟩ :=
    exists_circuitVector hn (NativeEndOfLine.activePredecessor_polyTime n P S hn hP hS)
      (fun a u hu => NativeEndOfLine.activePredecessor_length n P S a (hP_length a) u hu)
  obtain ⟨successors, hsuccessors, hsuccessor_eval⟩ :=
    exists_circuitVector hn (NativeEndOfLine.ppadToPppMap_polyTime n P S hn hP hS)
      (fun a u hu => Cslib.Complexity.length_ppadToPppMap (hS_length a) hu)
  let inst (a : α) : List Bool :=
    CircuitWords.encodePair (List.replicate (n a) true)
      (CircuitWords.encodePair (predecessors a) (successors a))
  refine ⟨inst, ?_, ?_, ?_⟩
  · have hinner := CircuitWords.encodePair_polyTime.comp (hpredecessors.prod hsuccessors)
    exact CircuitWords.encodePair_polyTime.comp
      (((ComputableInPolyTime.bitsReplicate true).comp hn).prod hinner)
  · intro a
    simp only [inst, endOfLineWidth, CircuitWords.first_encodePair, List.length_replicate]
  · intro a u hu
    constructor
    · simpa only [inst, endOfLinePredecessor, CircuitWords.rest_encodePair,
        CircuitWords.first_encodePair] using hpredecessor_eval a u hu
    · simpa only [inst, endOfLineSuccessor, CircuitWords.rest_encodePair] using
        hsuccessor_eval a u hu

end GameTheory.Complexity.Backend
