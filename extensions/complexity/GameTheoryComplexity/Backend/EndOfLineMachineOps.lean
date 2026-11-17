module

public import GameTheoryComplexity.Backend.EndOfLineProblem

@[expose] public section

/-! Native polynomial-time pointer operations and Boolean consistency checks for
serialized End-of-Line instances. Every computation retains the total byte semantics. -/

namespace GameTheory.Complexity.Backend.EndOfLineMachineOps

open Turing.MultiTapeTM
open ComputableInPolyTime

@[fun_prop] theorem width_polyTime
    {α : Type} {encIn : α ↪ List Bool} {input : α → List Bool}
    (hi : ComputableInPolyTime input encIn encBits) :
    ComputableInPolyTime (fun a => endOfLineWidth (input a)) encIn encUnary :=
  length_bits.comp (CircuitWords.first_polyTime.comp hi)

@[fun_prop] theorem predecessor_polyTime
    {α : Type} {encIn : α ↪ List Bool} {input vertex : α → List Bool}
    (hi : ComputableInPolyTime input encIn encBits)
    (hv : ComputableInPolyTime vertex encIn encBits) :
    ComputableInPolyTime (fun a => endOfLinePredecessor (input a) (vertex a)) encIn encBits :=
  evaluateCircuitVector_polyTime
    (CircuitWords.first_polyTime.comp (CircuitWords.rest_polyTime.comp hi)) hv

@[fun_prop] theorem successor_polyTime
    {α : Type} {encIn : α ↪ List Bool} {input vertex : α → List Bool}
    (hi : ComputableInPolyTime input encIn encBits)
    (hv : ComputableInPolyTime vertex encIn encBits) :
    ComputableInPolyTime (fun a => endOfLineSuccessor (input a) (vertex a)) encIn encBits :=
  evaluateCircuitVector_polyTime
    (CircuitWords.rest_polyTime.comp (CircuitWords.rest_polyTime.comp hi)) hv

@[fun_prop] theorem origin_polyTime
    {α : Type} {encIn : α ↪ List Bool} {input : α → List Bool}
    (hi : ComputableInPolyTime input encIn encBits) :
    ComputableInPolyTime (fun a => endOfLineOrigin (input a)) encIn encBits :=
  (bitsReplicate false).comp (width_polyTime hi)

/-- Check a nontrivial outgoing pointer and agreement of its inverse. -/
def successorFlag (input vertex : List Bool) : Bool :=
  !decide (endOfLineSuccessor input vertex = vertex) &&
    decide (endOfLinePredecessor input (endOfLineSuccessor input vertex) = vertex)

/-- Check a nontrivial incoming pointer and agreement of its inverse. -/
def predecessorFlag (input vertex : List Bool) : Bool :=
  !decide (endOfLinePredecessor input vertex = vertex) &&
    decide (endOfLineSuccessor input (endOfLinePredecessor input vertex) = vertex)

theorem successorFlag_accept (input vertex : List Bool) :
    successorFlag input vertex = true ↔ GameTheory.Math.EndOfLine.HasSuccessor
      (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
  simp [successorFlag, GameTheory.Math.EndOfLine.HasSuccessor]

theorem predecessorFlag_accept (input vertex : List Bool) :
    predecessorFlag input vertex = true ↔ GameTheory.Math.EndOfLine.HasPredecessor
      (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
  simp [predecessorFlag, GameTheory.Math.EndOfLine.HasPredecessor]

@[fun_prop] theorem successorFlag_polyTime
    {α : Type} {encIn : α ↪ List Bool} {input vertex : α → List Bool}
    (hi : ComputableInPolyTime input encIn encBits)
    (hv : ComputableInPolyTime vertex encIn encBits) :
    ComputableInPolyTime (fun a => successorFlag (input a) (vertex a)) encIn encBool := by
  have hs := successor_polyTime hi hv
  exact bool_and' (bool_not.comp (decide_eq' hs hv))
    (decide_eq' (predecessor_polyTime hi hs) hv)

@[fun_prop] theorem predecessorFlag_polyTime
    {α : Type} {encIn : α ↪ List Bool} {input vertex : α → List Bool}
    (hi : ComputableInPolyTime input encIn encBits)
    (hv : ComputableInPolyTime vertex encIn encBits) :
    ComputableInPolyTime (fun a => predecessorFlag (input a) (vertex a)) encIn encBool := by
  have hp := predecessor_polyTime hi hv
  exact bool_and' (bool_not.comp (decide_eq' hp hv))
    (decide_eq' (successor_polyTime hi hp) hv)

end GameTheory.Complexity.Backend.EndOfLineMachineOps
