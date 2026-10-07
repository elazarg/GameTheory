import GameTheory.Math.GridCrossingGeometry

/-! Uncrossing controls cover all directed orientations, switched outgoing
pairings, occupied and unused bends, endpoint preservation, and grid embedding. -/

namespace GameTheory.Tests.GridCrossing

open GameTheory.Math.GridCrossing GameTheory.Math.EndOfLine

example : crossingSuccessor true true (crossingSuccessor true true (.port 3)) = .port 0 ∧
    crossingSuccessor true true (crossingSuccessor true true (.port 2)) = .port 1 := by decide

example : crossingSuccessor true false (crossingSuccessor true false (.port 3)) = .port 2 ∧
    crossingSuccessor true false (crossingSuccessor true false (.port 0)) = .port 1 := by decide

example : crossingSuccessor false true (crossingSuccessor false true (.port 1)) = .port 0 ∧
    crossingSuccessor false true (crossingSuccessor false true (.port 2)) = .port 3 := by decide

example : crossingSuccessor false false (crossingSuccessor false false (.port 1)) = .port 2 ∧
    crossingSuccessor false false (crossingSuccessor false false (.port 0)) = .port 3 := by decide

example : crossingSuccessor true true (crossingSuccessor true true (.port 3)) ≠ .port 1 ∧
    crossingSuccessor true true (crossingSuccessor true true (.port 2)) ≠ .port 0 := by decide

example : HasPredecessor (crossingPredecessor true true) (crossingSuccessor true true)
      (.bend 3) ∧ HasSuccessor (crossingPredecessor true true) (crossingSuccessor true true)
      (.bend 3) ∧ HasPredecessor (crossingPredecessor true true) (crossingSuccessor true true)
      (.bend 1) ∧ HasSuccessor (crossingPredecessor true true) (crossingSuccessor true true)
      (.bend 1) := by decide

example : crossingSuccessor true true (.bend 0) = .bend 0 ∧
    crossingPredecessor true true (.bend 0) = .bend 0 ∧
    crossingSuccessor true true (.bend 2) = .bend 2 ∧
    crossingPredecessor true true (.bend 2) = .bend 2 ∧
    ¬IsEndpoint (crossingPredecessor true true) (crossingSuccessor true true) (.bend 0) ∧
    ¬IsEndpoint (crossingPredecessor true true) (crossingSuccessor true true) (.bend 2) := by
  decide

example (rightward upward : Bool) :
    crossingSuccessor rightward upward .center = .center ∧
      crossingPredecessor rightward upward .center = .center ∧
      ¬IsEndpoint (crossingPredecessor rightward upward)
        (crossingSuccessor rightward upward) .center :=
  ⟨rfl, rfl, center_not_endpoint rightward upward⟩

example (rightward upward : Bool) (p : Fin 4) :
    IsEndpoint (crossingPredecessor rightward upward) (crossingSuccessor rightward upward)
      (.port p) :=
  (crossing_endpoint_iff rightward upward (.port p)).mpr ⟨p, rfl⟩

example : crossingCoordinate (.port 0) = (1, 2) ∧ crossingCoordinate (.port 1) = (2, 1) ∧
    crossingCoordinate (.port 2) = (1, 0) ∧ crossingCoordinate (.port 3) = (0, 1) ∧
    crossingCoordinate (.bend 0) = (2, 2) ∧ crossingCoordinate (.bend 1) = (2, 0) ∧
    crossingCoordinate (.bend 2) = (0, 0) ∧ crossingCoordinate (.bend 3) = (0, 2) ∧
    crossingCoordinate .center = (1, 1) := by decide

example : axisUnitAdjacent (crossingCoordinate (.port 3)) (crossingCoordinate (.bend 3)) ∧
    axisUnitAdjacent (crossingCoordinate (.bend 3)) (crossingCoordinate (.port 0)) ∧
    ¬axisUnitAdjacent (crossingCoordinate .center) (crossingCoordinate .center) := by decide

end GameTheory.Tests.GridCrossing
