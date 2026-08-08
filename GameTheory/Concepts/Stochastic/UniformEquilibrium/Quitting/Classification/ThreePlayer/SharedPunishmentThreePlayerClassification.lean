/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Classification.ThreePlayer.SharedPunishmentThreePlayerExtremal
import Math.CyclicExposure
import Math.ProbabilityMassFunction.Simplex

/-!
# Classification of optimal shared punishments for the cyclic three-player table

For the cyclic table, the universal lower bound is witnessed by quitting at
time zero.  Consequently a plan whose shared excess is at most `3/4` must make
all three time-zero bad-event probabilities at least `1/4`.  Their cyclic
product structure forces every time-zero quitting marginal to equal `1/2`.
Combined with tail irrelevance, this classifies all minimizers:

* a behavior plan has shared gap `3/4` exactly when its first live row is fair;
* a stationary row has shared gap `3/4` exactly when it is the fair row.

Thus the optimizer is unique among stationary rows, while among arbitrary
history-dependent plans the entire continuation after an all-continue first
stage is free.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace QuittingSharedThreePlayer

/-! ## Coordinate consequences of a small shared gap -/

/-- Each designated player's excess is bounded by the shared worst-player
excess. -/
theorem quittingBestReplyGap_le_quittingSharedPunishmentGap
    (profile : (quittingGame reward).BehaviorProfile) (who : Player) :
    quittingBestReplyValue reward profile who -
        quittingPunishmentValue reward who ≤
      quittingSharedPunishmentGap profile := by
  unfold quittingSharedPunishmentGap
  cases who with
  | a => exact le_max_left _ _
  | b => exact (le_max_left _ _).trans (le_max_right _ _)
  | c => exact (le_max_right _ _).trans (le_max_right _ _)

/-- Exact payoff from quitting at the first stage against an arbitrary plan. -/
theorem quittingTerminalPayoff_update_quitNow_eq_badProbability
    (profile : (quittingGame reward).BehaviorProfile) (who : Player) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
      -(quittingProfileLiveRoot reward profile 0 (next who) true).toReal *
        (quittingProfileLiveRoot reward profile 0 (other who) false).toReal := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingRootSequencePureTimeTerminalValue_some_eq]
  simp [quittingLiveLedgerAccum, quittingOpponentSurvivalWeight,
    quittingFixedOpponentsQuitValue_eq]

/-- If the shared gap is at most `3/4`, each cyclic time-zero bad event has
probability at least `1/4`. -/
theorem quarter_le_badProbability_of_sharedGap_le_three_quarters
    (profile : (quittingGame reward).BehaviorProfile)
    (hgap : quittingSharedPunishmentGap profile ≤ (3 / 4 : ℝ))
    (who : Player) :
    (1 / 4 : ℝ) ≤
      (quittingProfileLiveRoot reward profile 0 (next who) true).toReal *
        (quittingProfileLiveRoot reward profile 0 (other who) false).toReal := by
  have hcoordinate :=
    (quittingBestReplyGap_le_quittingSharedPunishmentGap profile who).trans hgap
  rw [quittingPunishmentValue_eq_neg_one] at hcoordinate
  have hquit := le_quittingBestReplyValue reward profile who
    (quittingPureTimeBehaviorStrategy reward who (some 0))
  rw [quittingTerminalPayoff_update_quitNow_eq_badProbability] at hquit
  nlinarith

/-! ## The cyclic algebra -/

private theorem rootTrueMass_nonneg
    (root : Player → PMF Bool) (who : Player) :
    0 ≤ (root who true).toReal := ENNReal.toReal_nonneg

private theorem rootTrueMass_le_one
    (root : Player → PMF Bool) (who : Player) :
    (root who true).toReal ≤ 1 := by
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
    simpa using PMF.coe_le_one (root who) true)

/-- A shared gap at most `3/4` forces every first-row quitting probability to
be exactly one half. -/
theorem quittingProfileLiveRoot_trueMass_eq_half_of_sharedGap_le_three_quarters
    (profile : (quittingGame reward).BehaviorProfile)
    (hgap : quittingSharedPunishmentGap profile ≤ (3 / 4 : ℝ))
    (player : Player) :
    (quittingProfileLiveRoot reward profile 0 player true).toReal =
      (1 / 2 : ℝ) := by
  let root := quittingProfileLiveRoot reward profile 0
  let x : Player → ℝ := fun who => (root who true).toReal
  have hunit : ∀ who, 0 ≤ x who ∧ x who ≤ 1 := fun who =>
    ⟨rootTrueMass_nonneg root who, rootTrueMass_le_one root who⟩
  have hall : ∀ who,
      (1 / 4 : ℝ) ≤ cyclicExposureNeighbours.exposure x who := by
    intro who
    have h := quarter_le_badProbability_of_sharedGap_le_three_quarters
      profile hgap who
    rw [pmfBool_false_toReal] at h
    simpa [cyclicExposureNeighbours, Math.CyclicExposure.Neighbours.exposure,
      x, root] using h
  have hfair :=
    cyclicExposureNeighbours.eq_fair_of_forall_quarter_le_exposure
      x hunit hall
  simpa [x, root] using congrFun hfair player

private theorem eq_fairMarginal_of_true_toReal_eq_half
    (marginal : PMF Bool)
    (htrue : (marginal true).toReal = (1 / 2 : ℝ)) :
    marginal = fairMarginal := by
  apply Math.ProbabilityMassFunction.toVector_injective
  funext action
  cases action with
  | false =>
      change (marginal false).toReal = (fairMarginal false).toReal
      rw [pmfBool_false_toReal, pmfBool_false_toReal, htrue,
        fairMarginal_apply_toReal]
  | true =>
      change (marginal true).toReal = (fairMarginal true).toReal
      rw [htrue, fairMarginal_apply_toReal]

/-- **Necessity of the fair first row.**  No behavior plan can attain the
shared lower bound unless all three of its first live marginals are fair. -/
theorem quittingProfileLiveRoot_zero_eq_fair_of_sharedGap_le_three_quarters
    (profile : (quittingGame reward).BehaviorProfile)
    (hgap : quittingSharedPunishmentGap profile ≤ (3 / 4 : ℝ)) :
    quittingProfileLiveRoot reward profile 0 = fairRoot := by
  funext player
  have hhalf :=
    quittingProfileLiveRoot_trueMass_eq_half_of_sharedGap_le_three_quarters
      profile hgap player
  simpa [fairRoot] using
    (eq_fairMarginal_of_true_toReal_eq_half
      (quittingProfileLiveRoot reward profile 0 player) hhalf)

/-! ## Complete optimizer classification -/

/-- A behavior plan has shared gap at most `3/4` exactly when its first live
row is fair. -/
theorem quittingSharedPunishmentGap_le_three_quarters_iff_first_eq_fair
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingSharedPunishmentGap profile ≤ (3 / 4 : ℝ) ↔
      quittingProfileLiveRoot reward profile 0 = fairRoot := by
  constructor
  · exact quittingProfileLiveRoot_zero_eq_fair_of_sharedGap_le_three_quarters
      profile
  · intro hfair
    rw [quittingSharedPunishmentGap_eq_three_quarters_of_first_eq_fair
      profile hfair]

/-- **All behavior-plan minimizers.**  A committed shared plan attains the
exact value `3/4` if and only if its first live product row is fair. -/
theorem quittingSharedPunishmentGap_eq_three_quarters_iff_first_eq_fair
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingSharedPunishmentGap profile = (3 / 4 : ℝ) ↔
      quittingProfileLiveRoot reward profile 0 = fairRoot := by
  constructor
  · intro hgap
    exact quittingProfileLiveRoot_zero_eq_fair_of_sharedGap_le_three_quarters
      profile hgap.le
  · exact quittingSharedPunishmentGap_eq_three_quarters_of_first_eq_fair profile

/-- **Unique stationary minimizer.**  A constant product row attains the
shared value `3/4` if and only if every marginal is fair. -/
theorem quittingSharedStationaryPunishmentGap_eq_three_quarters_iff
    (root : Player → PMF Bool) :
    quittingSharedStationaryPunishmentGap root = (3 / 4 : ℝ) ↔
      root = fairRoot := by
  rw [← quittingSharedPunishmentGap_stationary]
  constructor
  · intro hgap
    have hfirst :=
      (quittingSharedPunishmentGap_eq_three_quarters_iff_first_eq_fair
        (quittingStationaryProfile reward root)).mp hgap
    simpa [quittingProfileLiveRoot_stationary] using hfirst
  · rintro rfl
    exact fairRoot_sharedPunishmentGap

end QuittingSharedThreePlayer

end GameTheory
