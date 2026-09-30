/-
# Discounted stochastic-value witness

This two-state zero-sum game has state-dependent payoffs and two distinct,
genuinely nondegenerate controlled transition laws.  It exercises the complete
stable-to-Analysis path through the Shapley contraction, unique value, and
stationary saddle selector. A drift game on the natural numbers exercises the
same value on infinitely many states and exhibits an unbounded solution of its
Bellman equation.
-/

import GameTheory.Analysis.Stochastic.Discounted
import GameTheory.Analysis.Stochastic.Fink
import GameTheory.Math.Probability.Mixture

noncomputable section

namespace GameTheory.Stochastic.Examples

open GameTheory GameTheory.Math.Probability
open scoped NNReal

private def transition (state : Bool) (action : Fin 2 → Bool) : PMF Bool :=
  if action 0 = action 1 then
    mix (1 / 3) (by norm_num) (by norm_num)
      (PMF.pure state) (PMF.pure (!state))
  else
    mix (2 / 3) (by norm_num) (by norm_num)
      (PMF.pure state) (PMF.pure (!state))

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

/-- The hostile witness has the two Boolean states. -/
instance stateFintype : Fintype hostileGame.State :=
  inferInstanceAs (Fintype Bool)

/-- Each player in the hostile witness has two Boolean actions. -/
instance actionFintype : ∀ i, Fintype (hostileGame.Action i) :=
  fun _ => inferInstanceAs (Fintype Bool)

/-- Every player in the hostile witness has an available action. -/
instance actionNonempty : ∀ i, Nonempty (hostileGame.Action i) :=
  fun _ => inferInstanceAs (Nonempty Bool)

theorem hostileGame_isZeroSum : hostileGame.IsZeroSum := by
  rw [Game.IsZeroSum]
  intro state action _
  rw [Fin.sum_univ_two]
  simp [hostileGame, stageUtility]

/-- The hostile game has a unique bounded normalized discounted Shapley value;
on two states every value is bounded. -/
theorem hostileGame_hasUnique_shapleyValue {β : ℝ≥0} (hβ : β < 1) :
    ∃! value : Bool → ℝ,
      (∃ bound : ℝ, ∀ state, |value state| ≤ bound) ∧
        hostileGame.shapleyOperator (β : ℝ) value = value :=
  hostileGame.existsUnique_shapleyValue
    hostileGame.hasBoundedRowStageUtility_of_finite hβ

/-- Its selected statewise actions are genuine canonical saddle points. -/
theorem hostileGame_hasStationarySaddle {β : ℝ≥0} (hβ : β < 1)
    (state : Bool) :
    IsSaddlePoint
      (MatrixGame.utility
        (hostileGame.auxiliaryMatrix (β : ℝ)
          (hostileGame.discountedValue
            hostileGame.hasBoundedRowStageUtility_of_finite hβ) state))
      (hostileGame.stationarySaddleProfile
        hostileGame.hasBoundedRowStageUtility_of_finite hβ state) :=
  hostileGame.stationarySaddleProfile_isSaddlePoint _ hβ state

/-! ## Infinite-state witness

The Shapley value needs only bounded stage utility, not finitely many states.
On an infinite state space the Bellman equation also has unbounded solutions,
so the bounded qualifier in `existsUnique_shapleyValue` cannot be dropped. -/

/-- Play drifts deterministically through the natural numbers, with zero stage
utility. -/
def driftGame : Game (Fin 2) where
  State := ℕ
  Action _ := Bool
  transition state _ := PMF.pure (state + 1)
  stageUtility _ _ _ := 0

/-- Each player in the drift game has two Boolean actions. -/
instance driftActionFintype : ∀ i, Fintype (driftGame.Action i) :=
  fun _ => inferInstanceAs (Fintype Bool)

/-- Every player in the drift game has an available action. -/
instance driftActionNonempty : ∀ i, Nonempty (driftGame.Action i) :=
  fun _ => inferInstanceAs (Nonempty Bool)

theorem driftGame_hasBoundedRowStageUtility :
    driftGame.HasBoundedRowStageUtility :=
  ⟨0, fun _ _ => by simp [driftGame]⟩

/-- The drift game has a unique bounded discounted value on infinitely many
states. -/
theorem driftGame_hasUnique_shapleyValue {β : ℝ≥0} (hβ : β < 1) :
    ∃! value : ℕ → ℝ,
      (∃ bound : ℝ, ∀ state, |value state| ≤ bound) ∧
        driftGame.shapleyOperator (β : ℝ) value = value :=
  driftGame.existsUnique_shapleyValue driftGame_hasBoundedRowStageUtility hβ

/-- Growth at the inverse discount rate also solves the drift game's Bellman
equation, and it is unbounded. -/
theorem driftGame_unbounded_shapleySolution {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    driftGame.shapleyOperator β (fun state : ℕ => β⁻¹ ^ state) =
        (fun state : ℕ => β⁻¹ ^ state) ∧
      ¬ ∃ bound : ℝ, ∀ state : ℕ, |β⁻¹ ^ state| ≤ bound := by
  refine ⟨funext fun state : ℕ => ?_, ?_⟩
  · have hmatrix :
        driftGame.auxiliaryMatrix β (fun state : ℕ => β⁻¹ ^ state) state =
          fun _ _ => β⁻¹ ^ state := by
      funext row col
      simp only [Game.auxiliaryMatrix, Game.normalizedOneStepUtility, driftGame,
        expect_pure, mul_zero, zero_add]
      rw [pow_succ, mul_comm, mul_assoc, inv_mul_cancel₀ hβ0.ne', mul_one]
    change MatrixGame.value (driftGame.auxiliaryMatrix β _ state) = _
    rw [hmatrix, MatrixGame.value_const]
  · rintro ⟨bound, hbound⟩
    obtain ⟨state, hstate⟩ :=
      ((tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hβ0).2 hβ1)).eventually_gt_atTop
        bound).exists
    exact (not_le.2 hstate) ((le_abs_self _).trans (hbound state))

/-! ## General-sum Fink witness -/

/-- A two-point transition law with both states in its support. -/
private def twoStateLaw (weight : ℝ) (hzero : 0 ≤ weight)
    (hone : weight ≤ 1) : PMF (Fin 2) :=
  mix weight hzero hone (PMF.pure 0) (PMF.pure 1)

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
    · exact mem_support_mix_left (1 / 3) (by norm_num) (by norm_num)
        (by norm_num) (by simp)
    · exact mem_support_mix_right (1 / 3) (by norm_num) (by norm_num)
        (by norm_num) (by simp)
  · constructor
    · exact mem_support_mix_left (2 / 3) (by norm_num) (by norm_num)
        (by norm_num) (by simp)
    · exact mem_support_mix_right (2 / 3) (by norm_num) (by norm_num)
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
