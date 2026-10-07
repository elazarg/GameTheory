import GameTheory.Math.GridCrossing

/-! The directed uncrossing gadget fits in a three-by-three grid. Port-to-bend
steps occupy the square's perimeter, and the unused center remains isolated. -/

namespace GameTheory.Math.GridCrossing

/-- Coordinates of the four ports, four bends, and unused center. -/
def crossingCoordinate : CrossingNode → ℕ × ℕ
  | .port p =>
    if p = 0 then (1, 2) else if p = 1 then (2, 1)
    else if p = 2 then (1, 0) else (0, 1)
  | .bend k =>
    if k = 0 then (2, 2) else if k = 1 then (2, 0)
    else if k = 2 then (0, 0) else (0, 2)
  | .center => (1, 1)

/-- Two grid points differ by one in one coordinate and agree in the other. -/
def axisUnitAdjacent (a b : ℕ × ℕ) : Prop :=
  ((a.1 + 1 = b.1 ∨ b.1 + 1 = a.1) ∧ a.2 = b.2) ∨
    (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2))

instance (a b : ℕ × ℕ) : Decidable (axisUnitAdjacent a b) :=
  inferInstanceAs (Decidable
    (((a.1 + 1 = b.1 ∨ b.1 + 1 = a.1) ∧ a.2 = b.2) ∨
      (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2))))

/-- Every gadget node occupies a distinct grid point. -/
theorem crossingCoordinate_injective : Function.Injective crossingCoordinate := by
  intro a b
  cases a with
  | port p =>
    cases b with
    | port q => fin_cases p <;> fin_cases q <;> decide
    | bend q => fin_cases p <;> fin_cases q <;> decide
    | center => fin_cases p <;> decide
  | bend p =>
    cases b with
    | port q => fin_cases p <;> fin_cases q <;> decide
    | bend q => fin_cases p <;> fin_cases q <;> decide
    | center => fin_cases p <;> decide
  | center =>
    cases b with
    | port q => fin_cases q <;> decide
    | bend q => fin_cases q <;> decide
    | center => decide

/-- Every nontrivial successor step follows a unit horizontal or vertical grid edge. -/
theorem crossingSuccessor_adjacent (rightward upward : Bool) (node : CrossingNode) :
    crossingSuccessor rightward upward node ≠ node →
      axisUnitAdjacent (crossingCoordinate node)
        (crossingCoordinate (crossingSuccessor rightward upward node)) := by
  cases rightward <;> cases upward <;> cases node with
  | port p => fin_cases p <;> decide
  | bend p => fin_cases p <;> decide
  | center => decide

/-- Every nontrivial predecessor step follows a unit horizontal or vertical grid edge. -/
theorem crossingPredecessor_adjacent (rightward upward : Bool) (node : CrossingNode) :
    crossingPredecessor rightward upward node ≠ node →
      axisUnitAdjacent (crossingCoordinate node)
        (crossingCoordinate (crossingPredecessor rightward upward node)) := by
  cases rightward <;> cases upward <;> cases node with
  | port p => fin_cases p <;> decide
  | bend p => fin_cases p <;> decide
  | center => decide

end GameTheory.Math.GridCrossing
