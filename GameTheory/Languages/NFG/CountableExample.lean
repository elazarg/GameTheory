import GameTheory.Languages.NFG.Compile
import Mathlib.Tactic.Linarith

/-!
# Countable-action NFG over `ℕ`

A 2-player game where each player picks a natural number, with the only
nonzero payoff at `(0, 0)`. Demonstrates `NFGGame`, `IsNashPure`, and
`IsDominant` over an infinite action type.
-/

namespace NFG

/-- 2-player NFG over `ℕ`-valued actions.

`(n, m) ↦ 1` if both pick `0`, else `0`. Players are indexed by `Fin 2`. -/
def natChoose : NFGGame (Fin 2) (fun _ => ℕ) where
  Outcome := ∀ _ : Fin 2, ℕ
  outcome := id
  utility s _ := if s 0 = 0 ∧ s 1 = 0 then 1 else 0

/-- The pure profile where both players pick `0`. -/
def natChoose_zero : StrategyProfile (fun _ : Fin 2 => ℕ) :=
  fun _ => 0

/-- `(0, 0)` is a Nash equilibrium. -/
theorem natChoose_zero_is_nash : IsNashPure natChoose natChoose_zero := by
  intro i a'
  simp only [natChoose, deviate]
  fin_cases i <;>
    (by_cases h : a' = 0 <;> simp [natChoose_zero, h, Function.update])

/-- For player 0, action `0` is dominant: against any opponent, `0` maximizes
    your payoff. (If opponent plays `0`, `0` gives `1` and any other action gives `0`;
    if opponent plays anything else, your payoff is `0` regardless.) -/
theorem natChoose_zero_dominant_0 : IsDominant natChoose 0 0 := by
  intro s a'
  simp only [natChoose, deviate]
  by_cases hs : s 1 = 0
  · by_cases ha : a' = 0
    · simp [hs, ha, Function.update]
    · simp [hs, ha, Function.update]
  · simp [hs, Function.update]

end NFG
