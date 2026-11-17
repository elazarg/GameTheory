module

public import GameTheory.Math.EndOfLineNormalization
public import GameTheoryComplexity.Backend.EndOfLineMachineOps

@[expose] public section

/-! Polynomial-time evaluation of consistent End-of-Line pointers. Each evaluator
checks the original pointer and its reverse link, retaining the pointer only when
it encodes an incident edge. These are word evaluators, rather than serializers
of new circuit instances. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM
open EndOfLineMachineOps

/-- Keep an incoming pointer exactly when its reverse link agrees. -/
def endOfLineNormalizedPredecessor (input vertex : List Bool) : List Bool :=
  if predecessorFlag input vertex then endOfLinePredecessor input vertex else vertex

/-- Keep an outgoing pointer exactly when its reverse link agrees. -/
def endOfLineNormalizedSuccessor (input vertex : List Bool) : List Bool :=
  if successorFlag input vertex then endOfLineSuccessor input vertex else vertex

theorem endOfLineNormalizedPredecessor_eq (input vertex : List Bool) :
    endOfLineNormalizedPredecessor input vertex =
      GameTheory.Math.EndOfLine.normalizePredecessor
        (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
  unfold endOfLineNormalizedPredecessor GameTheory.Math.EndOfLine.normalizePredecessor
  simp only [predecessorFlag_accept]

theorem endOfLineNormalizedSuccessor_eq (input vertex : List Bool) :
    endOfLineNormalizedSuccessor input vertex =
      GameTheory.Math.EndOfLine.normalizeSuccessor
        (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
  unfold endOfLineNormalizedSuccessor GameTheory.Math.EndOfLine.normalizeSuccessor
  simp only [successorFlag_accept]

@[simp] theorem endOfLineNormalizedPredecessor_length (input vertex : List Bool) :
    (endOfLineNormalizedPredecessor input vertex).length = vertex.length := by
  rw [endOfLineNormalizedPredecessor_eq,
    GameTheory.Math.EndOfLine.normalizePredecessor]
  split_ifs
  · exact evaluateCircuitVector_length _ vertex
  · rfl

@[simp] theorem endOfLineNormalizedSuccessor_length (input vertex : List Bool) :
    (endOfLineNormalizedSuccessor input vertex).length = vertex.length := by
  rw [endOfLineNormalizedSuccessor_eq, GameTheory.Math.EndOfLine.normalizeSuccessor]
  split_ifs
  · exact evaluateCircuitVector_length _ vertex
  · rfl

/-- Normalization charges the original pointers and their consistency checks. -/
@[fun_prop] theorem normalizedPredecessor_polyTime
    {α : Type} {enc : α ↪ List Bool} {input vertex : α → List Bool}
    (hi : ComputableInPolyTime input enc encBits)
    (hv : ComputableInPolyTime vertex enc encBits) :
    ComputableInPolyTime (fun a => endOfLineNormalizedPredecessor (input a) (vertex a))
      enc encBits :=
  (predecessorFlag_polyTime hi hv).ite (predecessor_polyTime hi hv) hv

@[fun_prop] theorem normalizedSuccessor_polyTime
    {α : Type} {enc : α ↪ List Bool} {input vertex : α → List Bool}
    (hi : ComputableInPolyTime input enc encBits)
    (hv : ComputableInPolyTime vertex enc encBits) :
    ComputableInPolyTime (fun a => endOfLineNormalizedSuccessor (input a) (vertex a))
      enc encBits :=
  (successorFlag_polyTime hi hv).ite (successor_polyTime hi hv) hv

/-- Machine normalization preserves precisely the original graph endpoints. -/
theorem endOfLineNormalized_endpoint_iff (input vertex : List Bool) :
    GameTheory.Math.EndOfLine.IsEndpoint (endOfLineNormalizedPredecessor input)
        (endOfLineNormalizedSuccessor input) vertex ↔
      GameTheory.Math.EndOfLine.IsEndpoint (endOfLinePredecessor input)
        (endOfLineSuccessor input) vertex := by
  have hp := funext (endOfLineNormalizedPredecessor_eq input)
  have hs := funext (endOfLineNormalizedSuccessor_eq input)
  rw [hp, hs]
  exact GameTheory.Math.EndOfLine.isEndpoint_normalize_iff _ _ vertex

/-- Under the genuine-source promise, normalized raw answers are exactly endpoints. -/
theorem endOfLineNormalized_rawWitness_iff {input vertex : List Bool}
    (hsource : endOfLineSourceValid input) :
    GameTheory.Math.EndOfLine.RawWitness (endOfLineNormalizedPredecessor input)
        (endOfLineNormalizedSuccessor input) (endOfLineOrigin input) vertex ↔
      vertex ≠ endOfLineOrigin input ∧ GameTheory.Math.EndOfLine.IsEndpoint
        (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
  have hp := funext (endOfLineNormalizedPredecessor_eq input)
  have hs := funext (endOfLineNormalizedSuccessor_eq input)
  rw [hp, hs]
  exact GameTheory.Math.EndOfLine.normalized_rawWitness_iff _ _
    hsource.1 hsource.2.1 hsource.2.2

end GameTheory.Complexity.Backend
