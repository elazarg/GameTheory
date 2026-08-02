/-
# Two-player zero-sum stochastic games

Only structural vocabulary lives here: pointwise zero-sum stage utility and a
proof-free row/column presentation of dependent joint actions.  Discounted
values and fixed points remain in the one-way Analysis bridge.
-/

import GameTheory.Core.ZeroSum
import GameTheory.Stochastic.Basic

namespace GameTheory.Stochastic.Game

universe ua

variable (G : Game (Fin 2))

/-- The native stochastic utility is zero-sum at every state and joint action.
This is a pointwise specialization of the canonical Core predicate. -/
def IsZeroSum : Prop :=
  ∀ state action,
    GameTheory.IsZeroSum (fun _ : Unit => G.stageUtility state action)

/-- Assemble a dependent two-player action profile from row and column
coordinates without exposing transport. -/
def pairAction (row : G.Action 0) (col : G.Action 1) : ∀ i, G.Action i :=
  Fin.cons row (Fin.cons col fun k : Fin 0 => k.elim0)

@[simp]
theorem pairAction_zero (row : G.Action 0) (col : G.Action 1) :
    G.pairAction row col 0 = row := rfl

@[simp]
theorem pairAction_one (row : G.Action 0) (col : G.Action 1) :
    G.pairAction row col 1 = col := rfl

/-- A dependent two-player action profile is determined by its row and column
coordinates. -/
theorem pairAction_apply (action : ∀ i, G.Action i) :
    G.pairAction (action 0) (action 1) = action := by
  funext i
  fin_cases i <;> rfl

end GameTheory.Stochastic.Game
