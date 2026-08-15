/-
# Discounted stochastic-value witness

This two-state zero-sum game has state-dependent payoffs and two distinct,
genuinely nondegenerate controlled transition laws.  It exercises the complete
stable-to-Analysis path through the Shapley contraction, unique value, and
stationary saddle selector.
-/

import GameTheory.Analysis.Stochastic.Discounted
import GameTheory.Analysis.Stochastic.Fink

noncomputable section

namespace GameTheory.Stochastic.Examples

open GameTheory GameTheory.Math.Probability
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

/-! ## General-sum Fink witness -/

/-- A two-point transition law with both states in its support. -/
private def twoStateLaw (weight : ℝ) (hzero : 0 ≤ weight)
    (hone : weight ≤ 1) : FinDist (Fin 2) :=
  FinDist.mix weight hzero hone (FinDist.pure 0) (FinDist.pure 1)

/-- A finite general-sum stochastic game. Agreement and disagreement change
the transition weights, while the two players value the states differently. -/
def generalSumGame : Game (Fin 2) where
  State := Fin 2
  Action _ := Fin 2
  transition _ joint :=
    if joint 0 = joint 1 then
      twoStateLaw (1 / 3) (by norm_num) (by norm_num)
    else
      twoStateLaw (2 / 3) (by norm_num) (by norm_num)
  stageUtility state joint who :=
    if who = 0 then
      if joint 0 = joint 1 then
        if state = 0 then 2 else 1
      else -1
    else if joint 0 = joint 1 then 0
    else if state = 0 then 1 else 2

private instance generalSumStateFintype : Fintype generalSumGame.State :=
  inferInstanceAs (Fintype (Fin 2))

private instance generalSumActionFintype :
    ∀ player, Fintype (generalSumGame.Action player) :=
  fun _ => inferInstanceAs (Fintype (Fin 2))

private instance generalSumActionNonempty :
    ∀ player, Nonempty (generalSumGame.Action player) :=
  fun _ => inferInstanceAs (Nonempty (Fin 2))

private theorem generalSumGame_stageUtility_bound
    (state : generalSumGame.State)
    (joint : ∀ player, generalSumGame.Action player) (who : Fin 2) :
    |generalSumGame.stageUtility state joint who| ≤ 2 := by
  simp only [generalSumGame]
  split_ifs <;> norm_num

/-- Every transition is genuinely stochastic and reaches both public states. -/
theorem generalSumGame_transition_supports_both
    (state : generalSumGame.State)
    (joint : ∀ player, generalSumGame.Action player) :
    (0 : Fin 2) ∈ (generalSumGame.transition state joint).support ∧
      (1 : Fin 2) ∈ (generalSumGame.transition state joint).support := by
  simp only [generalSumGame]
  split_ifs
  · constructor
    · exact FinDist.mem_support_mix_left (1 / 3) (by norm_num) (by norm_num)
        (by norm_num) (by simp)
    · exact FinDist.mem_support_mix_right (1 / 3) (by norm_num) (by norm_num)
        (by norm_num) (by simp)
  · constructor
    · exact FinDist.mem_support_mix_left (2 / 3) (by norm_num) (by norm_num)
        (by norm_num) (by simp)
    · exact FinDist.mem_support_mix_right (2 / 3) (by norm_num) (by norm_num)
        (by norm_num) (by simp)

/-- The general fixed-point theorem supplies a stationary Bellman equilibrium
for the hostile game at discount one half. -/
theorem generalSumGame_exists_discountedStationaryBellmanEq :
    ∃ (profile : generalSumGame.StationaryMixedProfile)
        (value : generalSumGame.State → Fin 2 → ℝ),
      generalSumGame.IsDiscountedStationaryBellmanEq (1 / 2) profile value ∧
        ∀ state who, |value state who| ≤ 2 := by
  exact generalSumGame.exists_isDiscountedStationaryBellmanEq_bounded
    (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num)
    generalSumGame_stageUtility_bound

end GameTheory.Stochastic.Examples
