import GameTheory.Math.EndOfLine
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-! A directed grid crossing can be replaced locally by two disjoint bent paths.
The replacement connects each incoming port to the other strand's outgoing port,
preserving all port orientations and creating no internal End-of-Line endpoints. -/

namespace GameTheory.Math.GridCrossing

/-- Four compass ports, four corner bends, and an unused central vertex.
Ports are north, east, south, west; bends are northeast, southeast, southwest, northwest. -/
inductive CrossingNode where
  | port (p : Fin 4)
  | bend (p : Fin 4)
  | center
  deriving DecidableEq

/-- The incoming horizontal port for the chosen direction. -/
def horizontalInputPort (rightward : Bool) : Fin 4 := if rightward then 3 else 1

/-- The outgoing horizontal port for the chosen direction. -/
def horizontalOutputPort (rightward : Bool) : Fin 4 := if rightward then 1 else 3

/-- The incoming vertical port for the chosen direction. -/
def verticalInputPort (upward : Bool) : Fin 4 := if upward then 2 else 0

/-- The outgoing vertical port for the chosen direction. -/
def verticalOutputPort (upward : Bool) : Fin 4 := if upward then 0 else 2

/-- The corner joining the horizontal input to the vertical output. -/
def horizontalBend (rightward upward : Bool) : Fin 4 :=
  if rightward then if upward then 3 else 2 else if upward then 0 else 1

/-- The corner joining the vertical input to the horizontal output. -/
def verticalBend (rightward upward : Bool) : Fin 4 :=
  if rightward then if upward then 1 else 0 else if upward then 2 else 3

/-- Follow the directed bent paths; dangling outputs and unused nodes remain fixed. -/
def crossingSuccessor (rightward upward : Bool) : CrossingNode → CrossingNode
  | .port p =>
      if p = horizontalInputPort rightward then .bend (horizontalBend rightward upward)
      else if p = verticalInputPort upward then .bend (verticalBend rightward upward)
      else .port p
  | .bend p =>
      if p = horizontalBend rightward upward then .port (verticalOutputPort upward)
      else if p = verticalBend rightward upward then .port (horizontalOutputPort rightward)
      else .bend p
  | .center => .center

/-- Follow the bent paths backwards; dangling inputs and unused nodes remain fixed. -/
def crossingPredecessor (rightward upward : Bool) : CrossingNode → CrossingNode
  | .port p =>
      if p = verticalOutputPort upward then .bend (horizontalBend rightward upward)
      else if p = horizontalOutputPort rightward then .bend (verticalBend rightward upward)
      else .port p
  | .bend p =>
      if p = horizontalBend rightward upward then .port (horizontalInputPort rightward)
      else if p = verticalBend rightward upward then .port (verticalInputPort upward)
      else .bend p
  | .center => .center

/-- The horizontal incoming strand is routed to the vertical outgoing port. -/
theorem horizontal_route (rightward upward : Bool) :
    crossingSuccessor rightward upward (.port (horizontalInputPort rightward)) =
        .bend (horizontalBend rightward upward) ∧
      crossingSuccessor rightward upward (.bend (horizontalBend rightward upward)) =
        .port (verticalOutputPort upward) ∧
      crossingPredecessor rightward upward (.bend (horizontalBend rightward upward)) =
        .port (horizontalInputPort rightward) ∧
      crossingPredecessor rightward upward (.port (verticalOutputPort upward)) =
        .bend (horizontalBend rightward upward) := by
  cases rightward <;> cases upward <;> decide

/-- The vertical incoming strand is routed to the horizontal outgoing port. -/
theorem vertical_route (rightward upward : Bool) :
    crossingSuccessor rightward upward (.port (verticalInputPort upward)) =
        .bend (verticalBend rightward upward) ∧
      crossingSuccessor rightward upward (.bend (verticalBend rightward upward)) =
        .port (horizontalOutputPort rightward) ∧
      crossingPredecessor rightward upward (.bend (verticalBend rightward upward)) =
        .port (verticalInputPort upward) ∧
      crossingPredecessor rightward upward (.port (horizontalOutputPort rightward)) =
        .bend (verticalBend rightward upward) := by
  cases rightward <;> cases upward <;> decide

/-- Every nontrivial successor edge has the matching predecessor edge. -/
theorem crossing_successor_consistent (rightward upward : Bool) (node : CrossingNode) :
    crossingSuccessor rightward upward node ≠ node →
      crossingPredecessor rightward upward (crossingSuccessor rightward upward node) = node := by
  cases rightward <;> cases upward <;> cases node with
  | port p => fin_cases p <;> decide
  | bend p => fin_cases p <;> decide
  | center => decide

/-- Every nontrivial predecessor edge has the matching successor edge. -/
theorem crossing_predecessor_consistent (rightward upward : Bool) (node : CrossingNode) :
    crossingPredecessor rightward upward node ≠ node →
      crossingSuccessor rightward upward (crossingPredecessor rightward upward node) = node := by
  cases rightward <;> cases upward <;> cases node with
  | port p => fin_cases p <;> decide
  | bend p => fin_cases p <;> decide
  | center => decide

/-- Exactly the original incoming ports have nontrivial outgoing edges. -/
theorem port_hasSuccessor_iff (rightward upward : Bool) (p : Fin 4) :
    EndOfLine.HasSuccessor (crossingPredecessor rightward upward)
        (crossingSuccessor rightward upward) (.port p) ↔
      p = horizontalInputPort rightward ∨ p = verticalInputPort upward := by
  cases rightward <;> cases upward <;> fin_cases p <;> decide

/-- Exactly the original outgoing ports have nontrivial incoming edges. -/
theorem port_hasPredecessor_iff (rightward upward : Bool) (p : Fin 4) :
    EndOfLine.HasPredecessor (crossingPredecessor rightward upward)
        (crossingSuccessor rightward upward) (.port p) ↔
      p = horizontalOutputPort rightward ∨ p = verticalOutputPort upward := by
  cases rightward <;> cases upward <;> fin_cases p <;> decide

/-- The local endpoints are precisely the four dangling ports. -/
theorem crossing_endpoint_iff (rightward upward : Bool) (node : CrossingNode) :
    EndOfLine.IsEndpoint (crossingPredecessor rightward upward)
        (crossingSuccessor rightward upward) node ↔ ∃ p, node = .port p := by
  cases rightward <;> cases upward <;> cases node with
  | port p => fin_cases p <;> decide
  | bend p => fin_cases p <;> decide
  | center => decide

/-- Neither a routed bend nor an unused bend introduces an endpoint. -/
theorem bend_not_endpoint (rightward upward : Bool) (p : Fin 4) :
    ¬EndOfLine.IsEndpoint (crossingPredecessor rightward upward)
      (crossingSuccessor rightward upward) (.bend p) := by
  rw [crossing_endpoint_iff]
  simp

/-- The unused center vertex is isolated and is not an endpoint. -/
theorem center_not_endpoint (rightward upward : Bool) :
    ¬EndOfLine.IsEndpoint (crossingPredecessor rightward upward)
      (crossingSuccessor rightward upward) .center := by
  rw [crossing_endpoint_iff]
  simp

end GameTheory.Math.GridCrossing
