/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.LiveMassRecurrence
import UniformEquilibrium.Quitting.Stationary.Root

/-!
# Live mass under a stationary quitting profile

For a stationary quitting profile, the conditional probability of surviving
one more stage is a constant `q`: the mass assigned by the product root action
to the all-continue joint action.  Consequently the live mass after `time`
stages is exactly `q ^ time`.

This gives the elementary stationary regime split.  Either `q = 1`, in which
case play remains live with probability one at every finite time, or `q < 1`,
in which case live mass converges geometrically to zero.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The one-stage probability that every player continues under a stationary
product root action. -/
def quittingStationaryContinueMass (root : ι → PMF Bool) : ℝ :=
  ((pmfPi root) (quittingAllContinueAction : ι → Bool)).toReal

omit [DecidableEq ι] in
/-- The all-continue mass is the product of the displayed Continue
probabilities. -/
theorem quittingStationaryContinueMass_eq_prod_continueProbability
    (root : ι → PMF Bool) :
    quittingStationaryContinueMass root =
      ∏ player, (root player false).toReal := by
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  rfl

omit [DecidableEq ι] in
theorem quittingStationaryContinueMass_nonneg
    (root : ι → PMF Bool) :
    0 ≤ quittingStationaryContinueMass root :=
  ENNReal.toReal_nonneg

omit [DecidableEq ι] in
theorem quittingStationaryContinueMass_le_one
    (root : ι → PMF Bool) :
    quittingStationaryContinueMass root ≤ 1 := by
  unfold quittingStationaryContinueMass
  rw [← ENNReal.toReal_one,
    ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by simp)]
  exact PMF.coe_le_one _ _

/-- Forcing one coordinate to Continue can only increase the all-continue
mass. -/
theorem quittingStationaryContinueMass_le_update_pure_false
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryContinueMass root ≤
      quittingStationaryContinueMass
        (Function.update root who (PMF.pure false)) := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_le_prod
  · intro player _
    exact ENNReal.toReal_nonneg
  · intro player _
    by_cases hplayer : player = who
    · subst player
      simp only [Function.update_self, PMF.pure_apply]
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        ((root who).coe_le_one false)
    · simp [Function.update_of_ne hplayer]

/-- One-stage probability that the product root action absorbs. -/
def quittingRootAbsorptionMass (root : ι → PMF Bool) : ℝ :=
  1 - quittingStationaryContinueMass root

/-- One-stage absorption probability after forcing `who` to Continue.  This
is the opponent-absorption hazard faced by `who`. -/
def quittingRootOpponentAbsorptionMass
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootAbsorptionMass
    (Function.update root who (PMF.pure false))

/-- Forcing one player to Continue only removes absorption events. -/
theorem quittingRootOpponentAbsorptionMass_le_absorptionMass
    (root : ι → PMF Bool) (who : ι) :
    quittingRootOpponentAbsorptionMass root who ≤
      quittingRootAbsorptionMass root := by
  have hcontinue :=
    quittingStationaryContinueMass_le_update_pure_false root who
  unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  linarith

omit [DecidableEq ι] in
/-- The expectation of the indicator of a nonempty quitter set is exactly
the one-stage absorption mass. -/
theorem expect_quittingNonemptyIndicator_eq_absorptionMass
    (root : ι → PMF Bool) :
    expect (pmfPi root) (fun action ↦
        if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) =
      quittingRootAbsorptionMass root := by
  let allContinue : ι → Bool := quittingAllContinueAction
  have hindicator :
      (fun action : ι → Bool ↦
          if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) =
        fun action ↦ 1 - if action = allContinue then (1 : ℝ) else 0 := by
    funext action
    by_cases hquit : (quittingQuitters action).Nonempty
    · have hne : action ≠ allContinue := by
        intro heq
        subst action
        simp [allContinue] at hquit
      simp [hquit, hne]
    · have heq : action = allContinue :=
        eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty
          action hquit
      subst action
      simp [allContinue]
  rw [hindicator, expect_sub, expect_const,
    ← Math.Probability.apply_toReal_eq_expect_indicator]
  rfl

omit [DecidableEq ι] in
/-- Stationarity makes the conditional all-continue probability independent
of the time and the live history. -/
@[simp] theorem quittingJointContinueMass_stationary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (time : ℕ) :
    quittingJointContinueMass reward
        (quittingStationaryProfile reward root) time =
      quittingStationaryContinueMass root :=
  rfl

omit [DecidableEq ι] in
/-- Exact geometric survival under a stationary quitting profile. -/
@[simp] theorem quittingLiveMass_stationary_eq_pow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (time : ℕ) :
    quittingLiveMass reward (quittingStationaryProfile reward root) time =
      quittingStationaryContinueMass root ^ time := by
  classical
  induction time with
  | zero => simp
  | succ time ih =>
      rw [quittingLiveMass_succ, ih,
        quittingJointContinueMass_stationary, pow_succ]

omit [DecidableEq ι] in
/-- If the stationary profile sometimes absorbs, its live mass converges
geometrically to zero. -/
theorem tendsto_quittingLiveMass_stationary_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (hquit : quittingStationaryContinueMass root < 1) :
    Filter.Tendsto
      (quittingLiveMass reward (quittingStationaryProfile reward root))
      Filter.atTop (nhds 0) := by
  have hlive :
      quittingLiveMass reward (quittingStationaryProfile reward root) =
        fun time => quittingStationaryContinueMass root ^ time := by
    funext time
    exact quittingLiveMass_stationary_eq_pow reward root time
  rw [hlive]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    (quittingStationaryContinueMass_nonneg root) hquit

omit [DecidableEq ι] in
/-- If the stationary all-continue probability is one, the profile remains
live with probability one at every finite time. -/
theorem quittingLiveMass_stationary_eq_one_of_continueMass_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (hcontinue : quittingStationaryContinueMass root = 1)
    (time : ℕ) :
    quittingLiveMass reward (quittingStationaryProfile reward root) time = 1 := by
  rw [quittingLiveMass_stationary_eq_pow, hcontinue, one_pow]

omit [DecidableEq ι] in
/-- Every stationary quitting profile lies in the persistent-live
endpoint or the geometrically absorbing regime. -/
theorem quittingStationary_liveMass_regime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) :
    quittingStationaryContinueMass root = 1 ∨
      Filter.Tendsto
        (quittingLiveMass reward (quittingStationaryProfile reward root))
        Filter.atTop (nhds 0) := by
  rcases eq_or_lt_of_le (quittingStationaryContinueMass_le_one root) with
    hcontinue | hquit
  · exact Or.inl hcontinue
  · exact Or.inr
      (tendsto_quittingLiveMass_stationary_zero reward root hquit)

end GameTheory
