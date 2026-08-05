/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSharedPunishmentThreePlayerExtremal
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

private theorem cyclic_quarter_forces_half
    {xa xb xc : ℝ}
    (hxa0 : 0 ≤ xa) (hxa1 : xa ≤ 1)
    (hxb0 : 0 ≤ xb) (hxb1 : xb ≤ 1)
    (hxc0 : 0 ≤ xc) (hxc1 : xc ≤ 1)
    (ha : (1 / 4 : ℝ) ≤ xb * (1 - xc))
    (hb : (1 / 4 : ℝ) ≤ xc * (1 - xa))
    (hc : (1 / 4 : ℝ) ≤ xa * (1 - xb)) :
    xa = (1 / 2 : ℝ) ∧ xb = (1 / 2 : ℝ) ∧ xc = (1 / 2 : ℝ) := by
  let qa := xa * (1 - xa)
  let qb := xb * (1 - xb)
  let qc := xc * (1 - xc)
  have hxaC0 : 0 ≤ 1 - xa := by linarith
  have hxbC0 : 0 ≤ 1 - xb := by linarith
  have hxcC0 : 0 ≤ 1 - xc := by linarith
  have hA0 : 0 ≤ xb * (1 - xc) := mul_nonneg hxb0 hxcC0
  have hB0 : 0 ≤ xc * (1 - xa) := mul_nonneg hxc0 hxaC0
  have hC0 : 0 ≤ xa * (1 - xb) := mul_nonneg hxa0 hxbC0
  have hAB :
      (1 / 4 : ℝ) * (1 / 4 : ℝ) ≤
        (xb * (1 - xc)) * (xc * (1 - xa)) := by
    calc
      (1 / 4 : ℝ) * (1 / 4 : ℝ) ≤
          (xb * (1 - xc)) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right ha (by norm_num)
      _ ≤ (xb * (1 - xc)) * (xc * (1 - xa)) :=
        mul_le_mul_of_nonneg_left hb hA0
  have hABC :
      (1 / 4 : ℝ) * (1 / 4 : ℝ) * (1 / 4 : ℝ) ≤
        (xb * (1 - xc)) * (xc * (1 - xa)) * (xa * (1 - xb)) := by
    calc
      (1 / 4 : ℝ) * (1 / 4 : ℝ) * (1 / 4 : ℝ) ≤
          ((xb * (1 - xc)) * (xc * (1 - xa))) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hAB (by norm_num)
      _ ≤ (xb * (1 - xc)) * (xc * (1 - xa)) * (xa * (1 - xb)) :=
        mul_le_mul_of_nonneg_left hc (mul_nonneg hA0 hB0)
  have hprod : (1 / 64 : ℝ) ≤ qa * qb * qc := by
    calc
      (1 / 64 : ℝ) =
          (1 / 4 : ℝ) * (1 / 4 : ℝ) * (1 / 4 : ℝ) := by norm_num
      _ ≤ (xb * (1 - xc)) * (xc * (1 - xa)) * (xa * (1 - xb)) := hABC
      _ = qa * qb * qc := by
        dsimp [qa, qb, qc]
        ring
  have hqa0 : 0 ≤ qa := by
    dsimp [qa]
    exact mul_nonneg hxa0 hxaC0
  have hqb0 : 0 ≤ qb := by
    dsimp [qb]
    exact mul_nonneg hxb0 hxbC0
  have hqc0 : 0 ≤ qc := by
    dsimp [qc]
    exact mul_nonneg hxc0 hxcC0
  have hqa1 : qa ≤ (1 / 4 : ℝ) := by
    dsimp [qa]
    nlinarith [sq_nonneg (xa - 1 / 2)]
  have hqb1 : qb ≤ (1 / 4 : ℝ) := by
    dsimp [qb]
    nlinarith [sq_nonneg (xb - 1 / 2)]
  have hqc1 : qc ≤ (1 / 4 : ℝ) := by
    dsimp [qc]
    nlinarith [sq_nonneg (xc - 1 / 2)]
  have hqbqc : qb * qc ≤ (1 / 16 : ℝ) := by
    calc
      qb * qc ≤ (1 / 4 : ℝ) * qc :=
        mul_le_mul_of_nonneg_right hqb1 hqc0
      _ ≤ (1 / 4 : ℝ) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hqc1 (by norm_num)
      _ = (1 / 16 : ℝ) := by norm_num
  have hqaqc : qa * qc ≤ (1 / 16 : ℝ) := by
    calc
      qa * qc ≤ (1 / 4 : ℝ) * qc :=
        mul_le_mul_of_nonneg_right hqa1 hqc0
      _ ≤ (1 / 4 : ℝ) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hqc1 (by norm_num)
      _ = (1 / 16 : ℝ) := by norm_num
  have hqaqb : qa * qb ≤ (1 / 16 : ℝ) := by
    calc
      qa * qb ≤ (1 / 4 : ℝ) * qb :=
        mul_le_mul_of_nonneg_right hqa1 hqb0
      _ ≤ (1 / 4 : ℝ) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hqb1 (by norm_num)
      _ = (1 / 16 : ℝ) := by norm_num
  have hprodA : qa * qb * qc ≤ qa * (1 / 16 : ℝ) := by
    calc
      qa * qb * qc = qa * (qb * qc) := by ring
      _ ≤ qa * (1 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_left hqbqc hqa0
  have hprodB : qa * qb * qc ≤ qb * (1 / 16 : ℝ) := by
    calc
      qa * qb * qc = qb * (qa * qc) := by ring
      _ ≤ qb * (1 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_left hqaqc hqb0
  have hprodC : qa * qb * qc ≤ qc * (1 / 16 : ℝ) := by
    calc
      qa * qb * qc = qc * (qa * qb) := by ring
      _ ≤ qc * (1 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_left hqaqb hqc0
  have hqaLower : (1 / 4 : ℝ) ≤ qa := by
    nlinarith [hprod, hprodA]
  have hqbLower : (1 / 4 : ℝ) ≤ qb := by
    nlinarith [hprod, hprodB]
  have hqcLower : (1 / 4 : ℝ) ≤ qc := by
    nlinarith [hprod, hprodC]
  have hqa : qa = (1 / 4 : ℝ) := le_antisymm hqa1 hqaLower
  have hqb : qb = (1 / 4 : ℝ) := le_antisymm hqb1 hqbLower
  have hqc : qc = (1 / 4 : ℝ) := le_antisymm hqc1 hqcLower
  have hxa : xa = (1 / 2 : ℝ) := by
    have h := hqa
    dsimp [qa] at h
    nlinarith [sq_nonneg (xa - 1 / 2)]
  have hxb : xb = (1 / 2 : ℝ) := by
    have h := hqb
    dsimp [qb] at h
    nlinarith [sq_nonneg (xb - 1 / 2)]
  have hxc : xc = (1 / 2 : ℝ) := by
    have h := hqc
    dsimp [qc] at h
    nlinarith [sq_nonneg (xc - 1 / 2)]
  exact ⟨hxa, hxb, hxc⟩

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
  let xa := (root Player.a true).toReal
  let xb := (root Player.b true).toReal
  let xc := (root Player.c true).toReal
  have ha := quarter_le_badProbability_of_sharedGap_le_three_quarters
    profile hgap Player.a
  have hb := quarter_le_badProbability_of_sharedGap_le_three_quarters
    profile hgap Player.b
  have hc := quarter_le_badProbability_of_sharedGap_le_three_quarters
    profile hgap Player.c
  rw [pmfBool_false_toReal] at ha hb hc
  change (1 / 4 : ℝ) ≤ xb * (1 - xc) at ha
  change (1 / 4 : ℝ) ≤ xc * (1 - xa) at hb
  change (1 / 4 : ℝ) ≤ xa * (1 - xb) at hc
  obtain ⟨hxa, hxb, hxc⟩ := cyclic_quarter_forces_half
    (rootTrueMass_nonneg root Player.a)
    (rootTrueMass_le_one root Player.a)
    (rootTrueMass_nonneg root Player.b)
    (rootTrueMass_le_one root Player.b)
    (rootTrueMass_nonneg root Player.c)
    (rootTrueMass_le_one root Player.c)
    ha hb hc
  cases player with
  | a => exact hxa
  | b => exact hxb
  | c => exact hxc

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
