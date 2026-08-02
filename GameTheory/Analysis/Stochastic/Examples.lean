/-
# Discounted stochastic-value witness

This two-state zero-sum game has state-dependent payoffs and two distinct,
genuinely nondegenerate controlled transition laws.  It exercises the complete
stable-to-Analysis path through the Shapley contraction, unique value, and
stationary saddle selector.
-/

import GameTheory.Analysis.Stochastic.Discounted

noncomputable section

namespace GameTheory.Stochastic.Examples

open GameTheory Probability
open scoped NNReal

private def transition (state : Bool) (action : Fin 2 → Bool) : FinDist Bool :=
  if action 0 = action 1 then
    FinDist.mix (1 / 3) (by norm_num) (by norm_num)
      (FinDist.pure state) (FinDist.pure (!state))
  else
    FinDist.mix (2 / 3) (by norm_num) (by norm_num)
      (FinDist.pure state) (FinDist.pure (!state))

private def stageUtility
    (state : Bool) (action : Fin 2 → Bool) : Fin 2 → ℝ :=
  let payoff : ℝ := if action 0 = action 1 then (if state then 2 else 1) else -1
  Fin.cons payoff (Fin.cons (-payoff) fun k : Fin 0 => k.elim0)

/-- A hostile finite stochastic game: neither state, action, transition, nor
payoff input is degenerate. -/
def hostileGame : Game (Fin 2) where
  State := Bool
  Action _ := Bool
  transition := transition
  stageUtility := stageUtility

private instance stateFintype : Fintype hostileGame.State :=
  inferInstanceAs (Fintype Bool)

private instance actionFintype : ∀ i, Fintype (hostileGame.Action i) :=
  fun _ => inferInstanceAs (Fintype Bool)

private instance actionNonempty : ∀ i, Nonempty (hostileGame.Action i) :=
  fun _ => inferInstanceAs (Nonempty Bool)

theorem hostileGame_isZeroSum : hostileGame.IsZeroSum := by
  rw [Game.IsZeroSum]
  intro state action _
  rw [Fin.sum_univ_two]
  simp [hostileGame, stageUtility]

/-- The hostile game has a unique normalized discounted Shapley value. -/
theorem hostileGame_hasUnique_shapleyValue {β : ℝ≥0} (hβ : β < 1) :
    ∃! value : Bool → ℝ,
      hostileGame.shapleyOperator (β : ℝ) value = value :=
  hostileGame.existsUnique_shapleyValue hβ

/-- Its selected statewise actions are genuine canonical saddle points. -/
theorem hostileGame_hasStationarySaddle {β : ℝ≥0} (hβ : β < 1)
    (state : Bool) :
    IsSaddlePoint
      (MatrixGame.utility
        (hostileGame.auxiliaryMatrix (β : ℝ)
          (hostileGame.discountedValue hβ) state))
      (hostileGame.stationarySaddleProfile hβ state) :=
  hostileGame.stationarySaddleProfile_isSaddlePoint hβ state

end GameTheory.Stochastic.Examples
