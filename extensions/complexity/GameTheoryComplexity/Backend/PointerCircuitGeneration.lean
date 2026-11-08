module

public import GameTheoryComplexity.Backend.CircuitVectorEmission
public import GameTheoryComplexity.Backend.EndOfLineProblem

@[expose] public section

/-! Uniform circuit generation for total word pointers on a prescribed finite
cube. The width is charged in unary and both pointers are compiled directly
from their native polynomial-time certificates, including the zero-width cube.
-/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM

/-- Compile two efficient width-preserving pointers into one concrete instance. -/
theorem exists_pointerCircuitInstance {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {P S : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hP_length : ∀ a u, u.length = n a → (P (a, u)).length = n a)
    (hS_length : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    ∃ inst : α → List Bool,
      ComputableInPolyTime inst enc encBits ∧
      (∀ a, endOfLineWidth (inst a) = n a) ∧
      ∀ a u, u.length = n a →
        endOfLinePredecessor (inst a) u = P (a, u) ∧
        endOfLineSuccessor (inst a) u = S (a, u) := by
  obtain ⟨predecessors, hp, hpeval⟩ := exists_circuitVector hn hP hP_length
  obtain ⟨successors, hs, hseval⟩ := exists_circuitVector hn hS hS_length
  let inst (a : α) : List Bool :=
    CircuitWords.encodePair (List.replicate (n a) true)
      (CircuitWords.encodePair (predecessors a) (successors a))
  refine ⟨inst, ?_, ?_, ?_⟩
  · exact CircuitWords.encodePair_polyTime.comp
      (((ComputableInPolyTime.bitsReplicate true).comp hn).prod
        (CircuitWords.encodePair_polyTime.comp (hp.prod hs)))
  · intro a
    simp only [inst, endOfLineWidth, CircuitWords.first_encodePair, List.length_replicate]
  · intro a u hu
    constructor
    · simpa only [inst, endOfLinePredecessor, CircuitWords.rest_encodePair,
        CircuitWords.first_encodePair] using hpeval a u hu
    · simpa only [inst, endOfLineSuccessor, CircuitWords.rest_encodePair] using hseval a u hu

end GameTheory.Complexity.Backend
