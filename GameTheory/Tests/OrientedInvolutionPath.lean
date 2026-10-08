import GameTheory.Math.OrientedInvolutionPath
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! An oriented three-edge path alongside an unrelated alternating cycle.
Only the path's two endpoints fix the incident-edge involution.
-/

namespace GameTheory.Tests.OrientedInvolutionPath

open GameTheory.Math.OrientedInvolutionPath

private def flip : Fin 8 → Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6]
private def turn : Fin 8 → Fin 8 := ![0, 2, 1, 3, 7, 6, 5, 4]
private def color : Fin 8 → Bool := ![true, false, true, false, true, false, true, false]

private theorem flip_involutive : Function.Involutive flip := by
  unfold Function.Involutive
  decide
private theorem turn_involutive : Function.Involutive turn := by
  unfold Function.Involutive
  decide
private theorem flip_nonfixed : ∀ x, flip x ≠ x := by decide
private theorem flip_color : ∀ x, color (flip x) = !(color x) := by decide
private theorem turn_color : ∀ x, turn x ≠ x → color (turn x) = !(color x) := by decide

-- The chosen orientation yields 0 → 1 → 2 → 3, with self pointers at its ends.
example : successor flip turn color 0 = 1 ∧ successor flip turn color 1 = 2 ∧
    successor flip turn color 2 = 3 ∧ successor flip turn color 3 = 3 := by decide
example : predecessor flip turn color 0 = 0 ∧ predecessor flip turn color 1 = 0 ∧
    predecessor flip turn color 2 = 1 ∧ predecessor flip turn color 3 = 2 := by decide

-- The source satisfies the existing End-of-Line pointer interface.
example : predecessor flip turn color 0 = 0 ∧ successor flip turn color 0 ≠ 0 ∧
    predecessor flip turn color (successor flip turn color 0) = 0 :=
  source_pointers flip turn color flip_involutive flip_nonfixed flip_color 0 (by decide) (by decide)

-- Unrelated cycles contribute no endpoints.
example (x : Fin 8) : GameTheory.Math.EndOfLine.IsEndpoint
    (predecessor flip turn color) (successor flip turn color) x ↔ x = 0 ∨ x = 3 := by
  rw [isEndpoint_iff flip turn color flip_involutive turn_involutive flip_nonfixed
    flip_color turn_color]
  fin_cases x <;> decide

example : ∃ x : Fin 8, x ≠ 0 ∧ turn x = x :=
  exists_fixedPoint_ne_origin flip turn color flip_involutive turn_involutive flip_nonfixed
    flip_color turn_color 0 (by decide) (by decide)

-- An interior point has both valid inverse laws.
example : predecessor flip turn color (successor flip turn color 1) = 1 ∧
    successor flip turn color (predecessor flip turn color 1) = 1 :=
  ⟨predecessor_successor flip turn color flip_involutive turn_involutive flip_color
      turn_color 1 (by decide),
    successor_predecessor flip turn color flip_involutive turn_involutive flip_color
      turn_color 1 (by decide)⟩

-- The sink has the complementary failure direction to the source.
example : predecessor flip turn color (successor flip turn color 3) ≠ 3 ∧
    successor flip turn color (predecessor flip turn color 3) = 3 := by decide

end GameTheory.Tests.OrientedInvolutionPath
