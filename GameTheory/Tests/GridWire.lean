import GameTheory.Math.GridWireCrossings

/-! Routing controls exercise ascending and descending columns, corner turns,
proper crossings in both directions, and directly adjacent switch ports. -/

namespace GameTheory.Tests.GridWire

open GameTheory.Math.GridWire GameTheory.Math.GridCrossing GameTheory.Math.EndOfLine

example (p : ℕ × ℕ) :
    IsEndpoint (wirePredecessor 2 1 0) (wireSuccessor 2 1 0) p ↔
      p = vertexPoint 1 ∨ p = vertexPoint 0 :=
  wire_endpoint_iff (by decide) (by decide) p

example : wireSuccessor 2 0 1 (3, 0) = (3, 1) ∧
    wireSuccessor 2 0 1 (3, 9) = (2, 9) ∧
    wireSuccessor 2 0 1 (0, 9) = (0, 8) ∧
    wireSuccessor 2 0 1 (0, 6) = (0, 6) := by decide

example : wireSuccessor 2 1 0 (6, 6) = (6, 5) ∧
    wireSuccessor 2 1 0 (6, 3) = (5, 3) ∧
    wirePredecessor 2 1 0 (6, 3) = (6, 4) ∧
    wirePredecessor 2 1 0 (0, 3) = (1, 3) ∧
    wirePredecessor 2 1 0 (0, 0) = (0, 1) := by decide

example : IsEndpoint (wirePredecessor 2 0 1) (wireSuccessor 2 0 1) (vertexPoint 0) ∧
    IsEndpoint (wirePredecessor 2 0 1) (wireSuccessor 2 0 1) (vertexPoint 1) ∧
    ¬IsEndpoint (wirePredecessor 2 0 1) (wireSuccessor 2 0 1) (3, 9) ∧
    ¬IsEndpoint (wirePredecessor 2 0 1) (wireSuccessor 2 0 1) (2, 4) := by decide

example : horizontalInterior 5 1 3 (12, 6) ∧ verticalInterior 5 0 4 (12, 6) ∧
    horizontalInterior 5 2 0 (12, 3) ∧ verticalInterior 5 0 4 (12, 3) := by
  unfold horizontalInterior verticalInterior wireColumn
  decide

example : horizontalInterior 5 4 2 (45, 15) ∧ verticalInterior 5 3 0 (45, 15) := by
  unfold horizontalInterior verticalInterior wireColumn
  decide

example : crossingNeighborhood (12, 3) (12, 4) ∧
    crossingNeighborhood (12, 6) (12, 5) ∧ axisUnitAdjacent (12, 4) (12, 5) := by
  unfold crossingNeighborhood
  decide

example : ¬∃ p, crossingNeighborhood (12, 3) p ∧ crossingNeighborhood (12, 6) p := by
  rintro ⟨p, ha, hb⟩
  exact crossingNeighborhood_disjoint (by decide) (by decide) (by decide) ha hb

-- Arbitrary edges sharing a source or target really do overlap. The geometric
-- classification therefore needs the uniqueness supplied by consistent pointers.
example : horizontalInterior 3 0 1 (1, 0) ∧ horizontalInterior 3 0 2 (1, 0) ∧
    horizontalInterior 3 0 1 (1, 9) ∧ horizontalInterior 3 2 1 (1, 9) := by
  unfold horizontalInterior wireColumn
  decide

end GameTheory.Tests.GridWire
