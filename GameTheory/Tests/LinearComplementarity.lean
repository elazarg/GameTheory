import GameTheory.Math.LinearComplementarity
import Mathlib.Tactic.NormNum

/-! Signed coefficients, degeneracy, empty carriers and infeasible slack exercise
linear complementarity without game-specific assumptions. -/

namespace GameTheory.Tests.LinearComplementarity

open GameTheory.Math.LinearComplementarity

-- A negative constant is repaired by a positive coordinate.
example : IsSolution (fun _ : Fin 1 => (-1 : ℚ))
    (fun _ _ => 2) (fun _ => 1 / 2) := by
  constructor
  · intro i
    norm_num
  constructor
  · intro i
    norm_num [slack]
  · intro i
    norm_num [slack]

-- A degenerate zero slack admits every nonnegative coordinate.
example : IsSolution (fun _ : Fin 1 => (0 : ℚ))
    (fun _ _ => 0) (fun _ => 7) := by
  simp [IsSolution, slack]

-- Both vectors being nonnegative is insufficient without complementarity.
example : ¬ IsSolution (fun _ : Fin 1 => (1 : ℚ))
    (fun _ _ => 0) (fun _ => 1) := by
  simp [IsSolution, slack]

-- Complementarity alone must not admit a negative slack at a zero coordinate.
example : ¬ IsSolution (fun _ : Fin 1 => (-1 : ℚ))
    (fun _ _ => 0) (fun _ => 0) := by
  intro h
  have hneg := h.slack_nonneg 0
  norm_num [slack] at hneg

-- A zero slack likewise must not admit a negative coordinate.
example : ¬ IsSolution (fun _ : Fin 1 => (0 : ℚ))
    (fun _ _ => 0) (fun _ => -1) := by
  simp [IsSolution, slack]

-- Empty carriers satisfy all three requirements without inventing coordinates.
example : IsSolution (fun i : Fin 0 => (i.elim0 : ℚ))
    (fun i _ => i.elim0) (fun i => i.elim0) := by
  exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

end GameTheory.Tests.LinearComplementarity
