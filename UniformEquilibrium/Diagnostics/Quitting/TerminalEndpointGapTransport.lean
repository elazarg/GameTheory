/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.InfiniteBehavioralTailEvaluation
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseStrategicRescaling
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment

/-!
# Deconditioning an endpoint gap on one actual terminal profile

Conditioning a terminal law on eventual absorption can hide a literal
deviation gain when the absorption probability is small.  The complementary
Never endpoint removes that loss if the same player also has a positive
singleton payoff.  The resulting estimate is affine in the absorption
probability and therefore uniform over all absorption regimes.

The profile ownership in this file is essential.  The conditioned payoff,
the stage-zero root, the literal prescribed payoff, and the best-response
envelope all come from one displayed behavioral profile.  Thus the results do
not compare a conditioned endpoint extracted from one tail with a separately
selected near-minimizing profile.  Establishing that co-realization is a
separate premise, not a consequence of the scalar transport.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The actual conditioned terminal payoff -/

/-- Total eventual-absorption probability of one behavioral profile. -/
def quittingTerminalAbsorptionProbability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  ∑ terminal, quittingAbsorbedMassLimit reward profile terminal

/-- Terminal reward conditioned on eventual absorption.  At zero absorption
the value is canonically set to zero; only its product with the absorption
probability is operational. -/
def quittingTerminalConditionedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : Payoff ι :=
  fun who =>
    if quittingTerminalAbsorptionProbability reward profile = 0 then 0
    else quittingTerminalPayoff reward profile who /
      quittingTerminalAbsorptionProbability reward profile

omit [DecidableEq ι] in
/-- The actual eventual-absorption probability lies in the unit interval. -/
theorem quittingTerminalAbsorptionProbability_mem_Icc
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalAbsorptionProbability reward profile ∈ Set.Icc 0 1 := by
  classical
  have hmass := quittingTerminalOutcomeMass_mem_stdSimplex reward profile
  have habsorptionNonneg :
      0 ≤ quittingTerminalAbsorptionProbability reward profile := by
    unfold quittingTerminalAbsorptionProbability
    exact Finset.sum_nonneg fun terminal _ => hmass.1 (some terminal)
  have hconservation :=
    quittingLiveMassLimit_add_sum_absorbedMassLimit reward profile
  have hliveNonneg := hmass.1 (none : QuittingTerminalOutcome ι)
  change 0 ≤ quittingLiveMassLimit reward profile at hliveNonneg
  constructor
  · exact habsorptionNonneg
  · unfold quittingTerminalAbsorptionProbability
    linarith

omit [DecidableEq ι] in
/-- Exact deconditioning for the canonical conditioned payoff, including the
zero-absorption case. -/
theorem quittingTerminalPayoff_eq_absorptionProbability_mul_conditionedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward profile who =
      quittingTerminalAbsorptionProbability reward profile *
        quittingTerminalConditionedPayoff reward profile who := by
  classical
  let alpha := quittingTerminalAbsorptionProbability reward profile
  by_cases hzero : alpha = 0
  · have hmass := quittingTerminalOutcomeMass_mem_stdSimplex reward profile
    have hallZero : ∀ terminal,
        quittingAbsorbedMassLimit reward profile terminal = 0 := by
      have hsum :
          (∑ terminal, quittingAbsorbedMassLimit reward profile terminal) = 0 := by
        simpa [alpha, quittingTerminalAbsorptionProbability] using hzero
      have hnonneg : ∀ terminal ∈ (Finset.univ :
          Finset {S : Finset ι // S.Nonempty}),
          0 ≤ quittingAbsorbedMassLimit reward profile terminal := by
        intro terminal _
        exact hmass.1 (some terminal)
      have hpointwise :=
        (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
      exact fun terminal => hpointwise terminal (Finset.mem_univ terminal)
    unfold quittingTerminalPayoff
    simp only [hallZero, zero_mul, Finset.sum_const_zero]
    have hzero' :
        quittingTerminalAbsorptionProbability reward profile = 0 := by
      simpa only [alpha] using hzero
    simp [hzero']
  · unfold quittingTerminalConditionedPayoff
    change quittingTerminalPayoff reward profile who =
      alpha * (if alpha = 0 then 0
        else quittingTerminalPayoff reward profile who / alpha)
    rw [if_neg hzero]
    field_simp

/-! ## Affine transport -/

omit [Fintype ι] [DecidableEq ι] in
/-- A convex combination dominates the smaller endpoint. -/
theorem min_le_one_sub_mul_add_mul
    {alpha delta eta : ℝ} (halpha : alpha ∈ Set.Icc 0 1) :
    min delta eta ≤ (1 - alpha) * delta + alpha * eta := by
  rcases le_total delta eta with hdelta | heta
  · rw [min_eq_left hdelta]
    have hnonneg : 0 ≤ alpha * (eta - delta) :=
      mul_nonneg halpha.1 (sub_nonneg.mpr hdelta)
    calc
      delta ≤ delta + alpha * (eta - delta) := le_add_of_nonneg_right hnonneg
      _ = (1 - alpha) * delta + alpha * eta := by ring
  · rw [min_eq_right heta]
    have hnonneg : 0 ≤ (1 - alpha) * (delta - eta) :=
      mul_nonneg (sub_nonneg.mpr halpha.2) (sub_nonneg.mpr heta)
    calc
      eta ≤ eta + (1 - alpha) * (delta - eta) :=
        le_add_of_nonneg_right hnonneg
      _ = (1 - alpha) * delta + alpha * eta := by ring

/-- Literal terminal exploitability dominates the immediate-Quit gain of
each player in the same behavioral profile. -/
theorem quittingFixedOpponentsQuitValue_sub_terminalPayoff_le_exploitability
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingStationaryFixedOpponentsQuitValue reward
          (quittingProfileLiveRoot reward profile 0) who -
        quittingTerminalPayoff reward profile who ≤
      max 0 (quittingContinuationBestResponseValue reward profile who -
        quittingTerminalPayoff reward profile who) ∧
    quittingStationaryFixedOpponentsQuitValue reward
          (quittingProfileLiveRoot reward profile 0) who -
        quittingTerminalPayoff reward profile who ≤
      quittingTerminalExploitability reward profile := by
  have hquit :
      quittingStationaryFixedOpponentsQuitValue reward
          (quittingProfileLiveRoot reward profile 0) who ≤
        quittingContinuationBestResponseValue reward profile who := by
    rw [← quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile who
        (quittingPureTimeBehaviorStrategy reward who (some 0)) hM hreward
  have hcoordinate :
      quittingStationaryFixedOpponentsQuitValue reward
            (quittingProfileLiveRoot reward profile 0) who -
          quittingTerminalPayoff reward profile who ≤
        max 0 (quittingContinuationBestResponseValue reward profile who -
          quittingTerminalPayoff reward profile who) :=
    (sub_le_sub_right hquit _).trans (le_max_right _ _)
  refine ⟨hcoordinate, hcoordinate.trans ?_⟩
  unfold quittingTerminalExploitability
  exact QuittingBoundaryHolonomy.le_finitePlayerMax
    (fun player => max 0
      (quittingContinuationBestResponseValue reward profile player -
        quittingTerminalPayoff reward profile player)) who

/-- **Exact affine deconditioning.**  A proposed endpoint `endpoint` is
compared with the conditioned terminal payoff of one actual profile.  The
result is a lower bound on that same player's literal terminal debt. -/
theorem affineConditionedEndpointGap_le_terminalCoordinateDebt
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (endpoint : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    let alpha := quittingTerminalAbsorptionProbability reward profile
    let conditioned := quittingTerminalConditionedPayoff reward profile who
    let solo := reward (quittingSingletonTerminal who) who
    (1 - alpha) * solo + alpha * (solo - endpoint) -
          2 * M * quittingRootOpponentAbsorptionMass
            (quittingProfileLiveRoot reward profile 0) who -
          alpha * |conditioned - endpoint| ≤
      max 0 (quittingContinuationBestResponseValue reward profile who -
        quittingTerminalPayoff reward profile who) := by
  dsimp only
  let alpha := quittingTerminalAbsorptionProbability reward profile
  let conditioned := quittingTerminalConditionedPayoff reward profile who
  let solo := reward (quittingSingletonTerminal who) who
  let opponent := quittingRootOpponentAbsorptionMass
    (quittingProfileLiveRoot reward profile 0) who
  have halpha := quittingTerminalAbsorptionProbability_mem_Icc reward profile
  have hfactor :=
    quittingTerminalPayoff_eq_absorptionProbability_mul_conditionedPayoff
      reward profile who
  have hquitClose :=
    abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
      (reward := reward) (quittingProfileLiveRoot reward profile 0) who
        hM hreward
  change alpha ∈ Set.Icc 0 1 at halpha
  change quittingTerminalPayoff reward profile who = alpha * conditioned at hfactor
  change |quittingStationaryFixedOpponentsQuitValue reward
      (quittingProfileLiveRoot reward profile 0) who - solo| ≤
    2 * M * opponent at hquitClose
  have hconditionedError :
      -alpha * |conditioned - endpoint| ≤
        alpha * (endpoint - conditioned) := by
    have herror : -|conditioned - endpoint| ≤ endpoint - conditioned := by
      simpa [abs_sub_comm] using neg_abs_le (endpoint - conditioned)
    simpa only [mul_neg, neg_mul] using
      (mul_le_mul_of_nonneg_left herror halpha.1)
  have hquitLower :
      solo - 2 * M * opponent ≤
        quittingStationaryFixedOpponentsQuitValue reward
          (quittingProfileLiveRoot reward profile 0) who := by
    linarith [(abs_le.mp hquitClose).1]
  have hgainLower :
      (1 - alpha) * solo + alpha * (solo - endpoint) -
            2 * M * opponent - alpha * |conditioned - endpoint| ≤
        quittingStationaryFixedOpponentsQuitValue reward
            (quittingProfileLiveRoot reward profile 0) who -
          quittingTerminalPayoff reward profile who := by
    calc
      (1 - alpha) * solo + alpha * (solo - endpoint) -
            2 * M * opponent - alpha * |conditioned - endpoint| =
          solo - 2 * M * opponent - alpha * endpoint -
            alpha * |conditioned - endpoint| := by ring
      _ ≤ solo - 2 * M * opponent - alpha * endpoint +
            alpha * (endpoint - conditioned) := by
        linarith
      _ = solo - 2 * M * opponent - alpha * conditioned := by ring
      _ ≤ quittingStationaryFixedOpponentsQuitValue reward
            (quittingProfileLiveRoot reward profile 0) who -
          alpha * conditioned := sub_le_sub_right hquitLower _
      _ = quittingStationaryFixedOpponentsQuitValue reward
            (quittingProfileLiveRoot reward profile 0) who -
          quittingTerminalPayoff reward profile who := by rw [hfactor]
  exact hgainLower.trans
    (quittingFixedOpponentsQuitValue_sub_terminalPayoff_le_exploitability
      reward profile who hM hreward).1

/-- If both endpoints of the conditioning split have positive gaps, the
literal debt bound is uniform in the eventual-absorption probability. -/
theorem min_sub_errors_le_terminalCoordinateDebt_of_conditionedEndpointGap
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (endpoint delta eta : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsolo : delta ≤ reward (quittingSingletonTerminal who) who)
    (hgap : eta ≤ reward (quittingSingletonTerminal who) who - endpoint) :
    min delta eta -
          2 * M * quittingRootOpponentAbsorptionMass
            (quittingProfileLiveRoot reward profile 0) who -
          |quittingTerminalConditionedPayoff reward profile who - endpoint| ≤
      max 0 (quittingContinuationBestResponseValue reward profile who -
        quittingTerminalPayoff reward profile who) := by
  let alpha := quittingTerminalAbsorptionProbability reward profile
  have halpha := quittingTerminalAbsorptionProbability_mem_Icc reward profile
  have hconvex := min_le_one_sub_mul_add_mul
    (alpha := alpha) (delta := delta) (eta := eta) halpha
  have hendpoints :
      (1 - alpha) * delta + alpha * eta ≤
        (1 - alpha) * reward (quittingSingletonTerminal who) who +
          alpha *
            (reward (quittingSingletonTerminal who) who - endpoint) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hsolo (sub_nonneg.mpr halpha.2))
      (mul_le_mul_of_nonneg_left hgap halpha.1)
  have hconditionedError :
      alpha *
          |quittingTerminalConditionedPayoff reward profile who - endpoint| ≤
        |quittingTerminalConditionedPayoff reward profile who - endpoint| := by
    exact mul_le_of_le_one_left (abs_nonneg _) halpha.2
  have htransport := affineConditionedEndpointGap_le_terminalCoordinateDebt
    reward profile who endpoint hM hreward
  dsimp only at htransport
  dsimp only [alpha] at hconvex hendpoints hconditionedError
  linarith

/-- Sequence form on actual profiles.  If one fixed player's canonical
conditioned payoffs approach an endpoint, its first-row opponent absorption
vanishes, and both endpoint gaps stay positive, then that same player's
literal debt is eventually bounded below by half the smaller gap. -/
theorem eventually_half_min_le_terminalCoordinateDebt_of_conditionedEndpointGap
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile) (who : ι)
    (endpoint delta eta : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdelta : 0 < delta) (heta : 0 < eta)
    (hsolo : delta ≤ reward (quittingSingletonTerminal who) who)
    (hgap : eta ≤ reward (quittingSingletonTerminal who) who - endpoint)
    (hconditioned : Tendsto (fun n =>
      quittingTerminalConditionedPayoff reward (profiles n) who)
      atTop (nhds endpoint))
    (hopponent : Tendsto (fun n =>
      quittingRootOpponentAbsorptionMass
        (quittingProfileLiveRoot reward (profiles n) 0) who)
      atTop (nhds 0)) :
    ∀ᶠ n in atTop,
      min delta eta / 2 ≤
        max 0 (quittingContinuationBestResponseValue reward (profiles n) who -
          quittingTerminalPayoff reward (profiles n) who) := by
  let error : ℕ → ℝ := fun n =>
    2 * M * quittingRootOpponentAbsorptionMass
        (quittingProfileLiveRoot reward (profiles n) 0) who +
      |quittingTerminalConditionedPayoff reward (profiles n) who - endpoint|
  have hconditionedError : Tendsto (fun n =>
      |quittingTerminalConditionedPayoff reward (profiles n) who - endpoint|)
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => endpoint) atTop (nhds endpoint) :=
      tendsto_const_nhds
    simpa using (hconditioned.sub hconst).abs
  have herror : Tendsto error atTop (nhds 0) := by
    simpa [error] using
      (hopponent.const_mul (2 * M)).add hconditionedError
  have hminPositive : 0 < min delta eta := lt_min hdelta heta
  have heventually : ∀ᶠ n in atTop, error n < min delta eta / 2 :=
    herror.eventually (Iio_mem_nhds (half_pos hminPositive))
  filter_upwards [heventually] with n hn
  have hpointwise :=
    min_sub_errors_le_terminalCoordinateDebt_of_conditionedEndpointGap
      reward (profiles n) who endpoint delta eta hM hreward hsolo hgap
  dsimp only [error] at hn
  linarith

end GameTheory
