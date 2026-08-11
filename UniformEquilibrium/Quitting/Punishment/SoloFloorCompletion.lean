/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Punishment.ApproximateCompletedCycle

/-!
# Punishment completion from singleton-floor dominance

A prospective solo owner need not admit one exact stationary Nash rate.  It is
enough that the owner's singleton payoff vector dominates every player's own
singleton payoff.  At a vanishing positive solo rate, an outsider's only new
risk is the collision with the owner, so its complete stationary unilateral
cap exceeds the target by `O(rate)`.  The existing approximate punishment
completion then handles the owner's possible negative singleton payoff.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Singleton-floor solo compiler.**  If the singleton payoff vector of one
owner dominates every player's own singleton payoff coordinatewise, and the
owner can be punished down to its own singleton payoff, then that vector is a
uniform-equilibrium payoff.

No positive lower bound on the owner's rate is needed.  The proof uses the
vanishing rates `1 / (n + 1)` and the approximate period-one punishment
compiler. -/
theorem isUniformEquilibriumPayoff_soloReward_of_soloFloor_of_punishmentIR
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι)
    (hfloor : ∀ who,
      quittingSoloReward reward who who ≤
        quittingSoloReward reward owner who)
    (hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  let rate : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hratePos : ∀ n, 0 < rate n := by
    intro n
    dsimp only [rate]
    positivity
  have hrateOne : ∀ n, rate n ≤ 1 := by
    intro n
    dsimp only [rate]
    apply (div_le_one (by positivity)).2
    exact_mod_cast (show (1 : ℕ) ≤ n + 1 by omega)
  have hrateVanish : Tendsto rate atTop (nhds 0) := by
    simpa only [rate] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0))
  let hazard : ℕ → PMF Bool := fun n =>
    quittingHazardCoin (rate n) (hratePos n).le (hrateOne n)
  let error : ℕ → ℝ := fun n =>
    2 * quittingRewardBound reward * rate n
  have herror0 : ∀ n, 0 ≤ error n := by
    intro n
    exact mul_nonneg
      (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
      (hratePos n).le
  have herrorVanish : Tendsto error atTop (nhds 0) := by
    simpa [error, mul_assoc] using
      hrateVanish.const_mul (2 * quittingRewardBound reward)
  have hhazardPositive : ∀ n, 0 < (hazard n true).toReal := by
    intro n
    dsimp only [hazard]
    rw [quittingHazardCoin_true_toReal]
    exact hratePos n
  apply isUniformEquilibriumPayoff_soloReward_of_approximate_caps
    reward owner hazard error hhazardPositive herror0 herrorVanish
  · intro n other hother
    let M := quittingRewardBound reward
    let target := quittingSoloReward reward owner other
    let solo := quittingSoloReward reward other other
    let collision := quittingSingletonCollisionReward reward owner other
    have hM : 0 ≤ M := quittingRewardBound_nonneg reward
    have hcollision : collision ≤ M := by
      exact (le_abs_self collision).trans (by
        simpa [M, collision, quittingSingletonCollisionReward] using
          (abs_reward_le_quittingRewardBound reward
            ⟨{owner, other}, by simp⟩ other))
    have htargetAbs : |target| ≤ M := by
      change |reward (quittingSingletonTerminal owner) other| ≤
        quittingRewardBound reward
      exact abs_reward_le_quittingRewardBound reward
        (quittingSingletonTerminal owner) other
    have hspread : collision - target ≤ 2 * M := by
      have htargetLower := (abs_le.mp htargetAbs).1
      linarith
    have hcontinue : 0 ≤ 1 - rate n := sub_nonneg.mpr (hrateOne n)
    rw [quittingStationaryUnilateralCap_solo_other
      reward hother (hazard n) (hhazardPositive n)]
    apply max_le
    · rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
        reward hother (hazard n)]
      have htrue : (hazard n true).toReal = rate n := by
        simp [hazard]
      have hfalse : (hazard n false).toReal = 1 - rate n := by
        simp [hazard]
      rw [htrue, hfalse]
      calc
        (1 - rate n) * quittingSoloReward reward other other +
              rate n * quittingSingletonCollisionReward reward owner other ≤
            (1 - rate n) * target + rate n * collision := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hfloor other) hcontinue)
            (le_refl _)
        _ = target + rate n * (collision - target) := by ring
        _ ≤ target + rate n * (2 * M) := by
          gcongr
        _ = quittingSoloReward reward owner other + error n := by
          dsimp only [target, M, error]
          ring
    · exact le_add_of_nonneg_right (herror0 n)
  · exact hpunishment

end GameTheory
