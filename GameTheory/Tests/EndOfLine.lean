import GameTheory.Math.EndOfLine

/-! Finite End-of-Line fixtures allow unrelated cycles, self-loops and
inconsistent pointers. The inverse-link hypothesis at the source is essential. -/

namespace GameTheory.Tests.EndOfLine

open GameTheory.Math.EndOfLine

private def predecessor (x : Fin 8) : Fin 8 :=
  match x.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 4
  | 4 => 3
  | _ => x

private def successor (x : Fin 8) : Fin 8 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 3 => 4
  | 4 => 3
  | 6 => 7
  | _ => x

example : predecessor 0 = 0 ∧ successor 0 ≠ 0 ∧ predecessor (successor 0) = 0 := by
  decide

example : ∀ x : Fin 8, IsEndpoint predecessor successor x ↔ x = 0 ∨ x = 2 := by
  decide

example : ∃ x, x ≠ (0 : Fin 8) ∧ IsEndpoint predecessor successor x :=
  exists_endpoint_ne_origin predecessor successor 0 (by decide) (by decide) (by decide)

example : ∀ x : Fin 8, x = 3 ∨ x = 4 →
    HasSuccessor predecessor successor x ∧ HasPredecessor predecessor successor x := by
  decide

example : ¬HasSuccessor predecessor successor 5 ∧
    ¬HasPredecessor predecessor successor 5 := by
  decide

example : successor 6 ≠ 6 ∧ ¬HasSuccessor predecessor successor 6 := by
  decide

private def brokenSuccessor (x : Fin 2) : Fin 2 := if x = 0 then 1 else 0

example : id (0 : Fin 2) = 0 ∧ brokenSuccessor 0 ≠ 0 := by
  decide

example : id (brokenSuccessor 0) ≠ (0 : Fin 2) ∧
    ∀ x, ¬IsEndpoint id brokenSuccessor x := by
  decide

end GameTheory.Tests.EndOfLine
