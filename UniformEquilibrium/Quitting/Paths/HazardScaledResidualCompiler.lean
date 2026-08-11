/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.InfinitePathCompiler
import UniformEquilibrium.Quitting.Cycles.CyclicSupersolution
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalTargetSemantics

/-!
# Infinite paths with opponent-hazard-scaled strategic residual

For unilateral deviations, the relevant clock deletes the deviating
player's own hazard.  Consequently a small residual measured against joint
absorption need not be harmless.  The robust local hypothesis bounds each
player's one-step Bellman residual by `error` times the absorption hazard of
that player's opponents.

The opponent hazard telescopes against the opponent-survival clock.  Its
total weighted mass is one when opponent survival vanishes, so the local
coefficient is also the global deviation bound.  This module packages that
calculation as a nonperiodic path compiler.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A bounded exact policy path whose strategic residual is scaled by each
player's opponent absorption hazard. -/
structure QuittingInfinitePathHazardScaledResidualCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) (error bound : ℝ) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  value_zero : value 0 = target
  survival : ∀ who start,
    Tendsto (quittingOpponentSurvivalWeight roots who start)
      atTop (nhds 0)
  value_bound : ∀ time who, |value time who| ≤ bound
  policy : ∀ time,
    value time = quittingRootSuccessorPayoff reward
      (value (time + 1)) (roots time)
  residual_le : ∀ time who,
    quittingPrescribedOneStepResidual reward roots who
        (fun stage ↦ value stage who) time ≤
      error * (1 - quittingFixedOpponentsContinueMass roots who time)

/-- Opponent absorption, weighted by preceding opponent survival, has total
mass one when the opponent clock vanishes. -/
theorem hasSum_quittingOpponentSurvivalWeight_mul_opponentAbsorption
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hsurvival : Tendsto (quittingOpponentSurvivalWeight roots who 0)
      atTop (nhds 0)) :
    HasSum (fun time ↦
      quittingOpponentSurvivalWeight roots who 0 time *
        (1 - quittingFixedOpponentsContinueMass roots who time)) 1 := by
  have hnonneg : ∀ time, 0 ≤
      quittingOpponentSurvivalWeight roots who 0 time *
        (1 - quittingFixedOpponentsContinueMass roots who time) := by
    intro time
    exact mul_nonneg
      (quittingOpponentSurvivalWeight_nonneg roots who 0 time)
      (sub_nonneg.mpr <| quittingStationaryContinueMass_le_one
        (Function.update (roots time) who (PMF.pure false)))
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg 1).2
  have hlimit : Tendsto (fun fuel : ℕ ↦
      (1 : ℝ) - quittingOpponentSurvivalWeight roots who 0 fuel)
      atTop (nhds (1 - 0)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
      atTop (nhds 1)).sub hsurvival
  have heq : (fun fuel : ℕ ↦
      ∑ time ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who 0 time *
          (1 - quittingFixedOpponentsContinueMass roots who time)) =
      fun fuel ↦ 1 - quittingOpponentSurvivalWeight roots who 0 fuel := by
    funext fuel
    simpa using
      (sum_quittingOpponentSurvivalWeight_mul_one_sub_continueMass
        roots who 0 fuel)
  rw [heq]
  simpa using hlimit

/-- **Deleted-clock local-to-global compiler.**  Exact policy evaluation and
an `error × opponent absorption` residual bound give terminal `error`-Nash
play.  No summation constant is lost. -/
theorem
    QuittingInfinitePathHazardScaledResidualCertificate.isεAsymptoticNash_and_delivers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) {error bound : ℝ}
    (certificate : QuittingInfinitePathHazardScaledResidualCertificate
      reward target error bound)
    (_herror : 0 ≤ error) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) error
        (quittingInfinitePathProfile reward certificate.roots) ∧
      quittingTerminalPayoff reward
          (quittingInfinitePathProfile reward certificate.roots) = target := by
  have hselected :=
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_survival_tendsto_zero
      reward certificate.roots certificate.value certificate.survival
        hbound hreward certificate.value_bound certificate.policy
  have hdelivery : quittingTerminalPayoff reward
      (quittingInfinitePathProfile reward certificate.roots) = target := by
    funext who
    rw [quittingTerminalPayoff_infinitePathProfile]
    have hzero := congrFun (hselected 0) who
    change quittingRootSequenceTerminalValue reward certificate.roots who 0 =
      target who
    rw [← hzero, certificate.value_zero]
  constructor
  · intro who deviation
    let prescribed : ℕ → ℝ :=
      quittingRootSequenceTerminalValue reward certificate.roots who
    have hprescribed : prescribed = fun time ↦ certificate.value time who := by
      funext time
      exact (congrFun (hselected time) who).symm
    let residual : ℕ → ℝ := fun time ↦
      quittingPrescribedOneStepResidual reward certificate.roots who
        prescribed time
    let opponentStop : ℕ → ℝ := fun time ↦
      quittingOpponentSurvivalWeight certificate.roots who 0 time *
        (1 - quittingFixedOpponentsContinueMass
          certificate.roots who time)
    let weightedResidual : ℕ → ℝ := fun time ↦
      quittingOpponentSurvivalWeight certificate.roots who 0 time *
        residual time
    have hstop : HasSum opponentStop 1 := by
      simpa only [opponentStop] using
        hasSum_quittingOpponentSurvivalWeight_mul_opponentAbsorption
          certificate.roots who (certificate.survival who 0)
    have hresidualNonneg : ∀ time, 0 ≤ residual time := by
      intro time
      exact quittingPrescribedOneStepResidual_nonneg reward certificate.roots
        who prescribed
          (isQuittingLivePrescribedValue_quittingRootSequenceTerminalValue
            reward certificate.roots who) time
    have hweightedNonneg : ∀ time, 0 ≤ weightedResidual time := by
      intro time
      exact mul_nonneg
        (quittingOpponentSurvivalWeight_nonneg
          certificate.roots who 0 time)
        (hresidualNonneg time)
    have hweightedLe : ∀ time,
        weightedResidual time ≤ error * opponentStop time := by
      intro time
      have hlocal := certificate.residual_le time who
      rw [← hprescribed] at hlocal
      dsimp only [weightedResidual, residual, opponentStop]
      calc
        quittingOpponentSurvivalWeight certificate.roots who 0 time *
              quittingPrescribedOneStepResidual reward certificate.roots who
                prescribed time ≤
            quittingOpponentSurvivalWeight certificate.roots who 0 time *
              (error * (1 - quittingFixedOpponentsContinueMass
                certificate.roots who time)) :=
          mul_le_mul_of_nonneg_left hlocal
            (quittingOpponentSurvivalWeight_nonneg
              certificate.roots who 0 time)
        _ = error *
            (quittingOpponentSurvivalWeight certificate.roots who 0 time *
              (1 - quittingFixedOpponentsContinueMass
                certificate.roots who time)) := by ring
    have hmajorant : Summable (fun time ↦ error * opponentStop time) :=
      hstop.summable.mul_left error
    have hsummable : Summable weightedResidual :=
      Summable.of_nonneg_of_le hweightedNonneg hweightedLe hmajorant
    have hsumLe : (∑' time, weightedResidual time) ≤ error := by
      calc
        (∑' time, weightedResidual time) ≤
            ∑' time, error * opponentStop time :=
          hsummable.tsum_le_tsum hweightedLe hmajorant
        _ = error * ∑' time, opponentStop time :=
          tsum_mul_left
        _ = error := by rw [hstop.tsum_eq, mul_one]
    have hgap :=
      quittingRootSequenceHazardTerminalGap_le_tsum_residual_of_survival_zero
        reward certificate.roots who
          (quittingBehaviorLiveHazard reward deviation) bound hbound hreward
          (certificate.survival who 0) (by simpa only [weightedResidual] using
            hsummable)
    have hdeviation :=
      quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
        reward (quittingInfinitePathProfile reward certificate.roots)
          who deviation
    rw [quittingProfileLiveRoot_infinitePathProfile] at hdeviation
    rw [hdeviation, hdelivery]
    change quittingRootSequenceHazardTerminalValue reward certificate.roots who
        (quittingBehaviorLiveHazard reward deviation) 0 ≤ target who + error
    have hzero : prescribed 0 = target who := by
      dsimp only [prescribed]
      rw [← congrFun (hselected 0) who, certificate.value_zero]
    dsimp only [weightedResidual, residual] at hsumLe
    dsimp only [prescribed] at hzero hgap
    linarith
  · exact hdelivery

/-! ## Separated immediate-Quit and refusal errors -/

/-- A bounded exact policy path with two strategically different errors:
immediate Quit has a uniform additive error, while Continue has an error
scaled by the current opponent absorption hazard. -/
structure QuittingInfinitePathSeparatedErrorCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) (quitError refusalCoefficient bound : ℝ) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  value_zero : value 0 = target
  survival : ∀ who start,
    Tendsto (quittingOpponentSurvivalWeight roots who start)
      atTop (nhds 0)
  value_bound : ∀ time who, |value time who| ≤ bound
  policy : ∀ time,
    value time = quittingRootSuccessorPayoff reward
      (value (time + 1)) (roots time)
  quit_le : ∀ time who,
    quittingStationaryFixedOpponentsQuitValue reward (roots time) who ≤
      value time who + quitError
  continue_le : ∀ time who,
    quittingStationaryFixedOpponentsContinueReward reward
          (roots time) who +
        quittingStationaryFixedOpponentsContinueMass (roots time) who *
          value (time + 1) who ≤
      value time who + refusalCoefficient *
        (1 - quittingStationaryFixedOpponentsContinueMass
          (roots time) who)

/-- **Separated-error Snell comparison.**  A uniform immediate-Quit error
and an opponent-hazard-scaled Continue error add once.  The latter does not
accumulate because the added constant is transported by the same opponent
Continue mass. -/
theorem quittingRootSequenceHazardTerminalValue_le_add_of_separatedError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (player : ι) (deviation : ℕ → PMF Bool)
    {quitError refusalCoefficient bound : ℝ}
    (hquitError : 0 ≤ quitError)
    (hrefusal : 0 ≤ refusalCoefficient)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hquit : ∀ time who,
      quittingStationaryFixedOpponentsQuitValue reward (roots time) who ≤
        value time who + quitError)
    (hcontinue : ∀ time who,
      quittingStationaryFixedOpponentsContinueReward reward
            (roots time) who +
          quittingStationaryFixedOpponentsContinueMass (roots time) who *
            value (time + 1) who ≤
        value time who + refusalCoefficient *
          (1 - quittingStationaryFixedOpponentsContinueMass
            (roots time) who))
    (hsurvival : Tendsto
      (quittingOpponentSurvivalWeight roots player 0) atTop (nhds 0)) :
    quittingRootSequenceHazardTerminalValue reward roots player deviation 0 ≤
      value 0 player + (quitError + refusalCoefficient) := by
  let allowance := quitError + refusalCoefficient
  let super : ℕ → ℝ := fun time ↦ value time player + allowance
  let deviationValue : ℕ → ℝ := fun time ↦
    quittingRootSequenceHazardTerminalValue
      reward roots player deviation time
  have hallowance : 0 ≤ allowance := add_nonneg hquitError hrefusal
  have hdeviation : ∀ time, deviationValue time ≤
      quittingLiveBellmanValue reward roots player deviationValue time := by
    intro time
    exact quittingRootSequenceHazardTerminalValue_le_liveBellmanValue
      reward roots player deviation time
  have hsuper : ∀ time,
      quittingLiveBellmanValue reward roots player super time ≤ super time := by
    intro time
    let continueMass :=
      quittingStationaryFixedOpponentsContinueMass (roots time) player
    have hmass0 : 0 ≤ continueMass := by
      dsimp only [continueMass]
      exact quittingStationaryFixedOpponentsContinueMass_nonneg
        (roots time) player
    have hmass1 : continueMass ≤ 1 := by
      dsimp only [continueMass]
      exact quittingStationaryContinueMass_le_one
        (Function.update (roots time) player (PMF.pure false))
    have hcontinueTime := hcontinue time player
    dsimp only [quittingLiveBellmanValue, super]
    apply max_le
    · exact (hquit time player).trans <| by
        dsimp only [allowance]
        linarith
    · change quittingStationaryFixedOpponentsContinueReward reward
            (roots time) player +
          continueMass * (value (time + 1) player + allowance) ≤
        value time player + allowance
      change quittingStationaryFixedOpponentsContinueReward reward
            (roots time) player +
          continueMass * value (time + 1) player ≤
        value time player + refusalCoefficient * (1 - continueMass)
        at hcontinueTime
      dsimp only [allowance]
      nlinarith
  have hgapBound : ∀ time,
      max (deviationValue time - super time) 0 ≤ 2 * bound := by
    intro time
    have hdev := abs_quittingTerminalPayoff_le reward
      (quittingRootSequenceProfile reward
        (quittingRootSequenceUpdate roots player deviation) time)
      player hbound hreward
    have hval := hvalueBound time player
    have hraw : deviationValue time - super time ≤ 2 * bound := by
      dsimp only [deviationValue, super, allowance,
        quittingRootSequenceHazardTerminalValue,
        quittingRootSequenceTerminalValue] at hdev ⊢
      rw [abs_le] at hdev hval
      linarith
    exact max_le hraw (by linarith)
  have hcomparison :=
    quittingSubBellmanValue_le_superSolution_of_survival_zero
      reward roots player super deviationValue (2 * bound)
      hdeviation hsuper hgapBound hsurvival
  simpa only [deviationValue, super, allowance] using hcomparison

/-- A separated-error certificate compiles to terminal
`quitError + refusalCoefficient`-Nash play and exact delivery. -/
theorem QuittingInfinitePathSeparatedErrorCertificate.isεAsymptoticNash_and_delivers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) {quitError refusalCoefficient bound : ℝ}
    (certificate : QuittingInfinitePathSeparatedErrorCertificate
      reward target quitError refusalCoefficient bound)
    (hquitError : 0 ≤ quitError)
    (hrefusal : 0 ≤ refusalCoefficient)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (quitError + refusalCoefficient)
        (quittingInfinitePathProfile reward certificate.roots) ∧
      quittingTerminalPayoff reward
          (quittingInfinitePathProfile reward certificate.roots) = target := by
  have hselected :=
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_survival_tendsto_zero
      reward certificate.roots certificate.value certificate.survival
        hbound hreward certificate.value_bound certificate.policy
  have hdelivery : quittingTerminalPayoff reward
      (quittingInfinitePathProfile reward certificate.roots) = target := by
    funext who
    rw [quittingTerminalPayoff_infinitePathProfile]
    have hzero := congrFun (hselected 0) who
    change quittingRootSequenceTerminalValue reward certificate.roots who 0 =
      target who
    rw [← hzero, certificate.value_zero]
  constructor
  · intro player deviation
    have hhazard :=
      quittingRootSequenceHazardTerminalValue_le_add_of_separatedError
        reward certificate.roots certificate.value player
          (quittingBehaviorLiveHazard reward deviation)
          hquitError hrefusal hbound hreward certificate.value_bound
          certificate.quit_le certificate.continue_le
          (certificate.survival player 0)
    have hdeviation :=
      quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
        reward (quittingInfinitePathProfile reward certificate.roots)
          player deviation
    rw [quittingProfileLiveRoot_infinitePathProfile] at hdeviation
    rw [hdeviation, hdelivery]
    simpa [certificate.value_zero] using hhazard
  · exact hdelivery

/-- Accuracy-indexed separated-error paths compile to a uniform-equilibrium
payoff.  Each half of the requested error is assigned to one strategic
channel. -/
theorem isUniformEquilibriumPayoff_of_arbitrarily_small_separatedError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hcertificates : ∀ error, 0 < error →
      Nonempty (QuittingInfinitePathSeparatedErrorCertificate
        reward target (error / 2) (error / 2) bound)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_fixedTarget
  intro error herror
  obtain ⟨certificate⟩ := hcertificates error herror
  have hhalf : 0 ≤ error / 2 := by linarith
  have hcompiled := certificate.isεAsymptoticNash_and_delivers
    reward target hhalf hhalf hbound hreward
  refine ⟨quittingInfinitePathProfile reward certificate.roots, ?_,
    hcompiled.2⟩
  simpa only [add_halves] using hcompiled.1

/-- Accuracy-indexed deleted-clock certificates deliver a uniform-equilibrium
payoff.  A diffuse product purification only has to make the local coefficient
arbitrarily small; the opponent clock performs the global summation. -/
theorem isUniformEquilibriumPayoff_of_arbitrarily_small_hazardScaledResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hcertificates : ∀ error, 0 < error →
      Nonempty (QuittingInfinitePathHazardScaledResidualCertificate
        reward target error bound)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  intro ε hε
  let error := ε / 2
  have herror : 0 < error := by
    dsimp only [error]
    linarith
  obtain ⟨certificate⟩ := hcertificates error herror
  let profile := quittingInfinitePathProfile reward certificate.roots
  have hcompiled := certificate.isεAsymptoticNash_and_delivers
    reward target herror.le hbound hreward
  have hterminalNash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error profile := by
    simpa only [profile] using hcompiled.1
  have hterminalValue : quittingTerminalPayoff reward profile = target := by
    simpa only [profile] using hcompiled.2
  have huniform : (quittingGame reward).IsUniformεEquilibrium
      none ε profile :=
    quittingGame_isUniformεEquilibrium_of_terminalNash
      reward profile (by dsimp only [error]; linarith)
        hterminalNash bound hbound hreward
  obtain ⟨nashThreshold, hnashThreshold⟩ := huniform
  have heventuallyDelivery : ∀ᶠ horizon : ℕ in atTop, ∀ who,
      |(quittingGame reward).finiteAveragePayoff none horizon profile who -
          target who| ≤ ε := by
    apply Filter.eventually_all.mpr
    intro who
    have hball :=
      (tendsto_finiteAveragePayoff_quittingGame reward profile who).eventually
        (Metric.ball_mem_nhds
          (quittingTerminalPayoff reward profile who) hε)
    filter_upwards [hball] with horizon hhorizon
    have htarget := congrFun hterminalValue who
    rw [htarget] at hhorizon
    simpa [Metric.mem_ball, Real.dist_eq] using hhorizon.le
  obtain ⟨deliveryThreshold, hdeliveryThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨profile, max nashThreshold deliveryThreshold,
    fun horizon hhorizon ↦ ?_⟩
  constructor
  · exact hnashThreshold horizon
      (le_trans (Nat.le_max_left _ _) hhorizon)
  · exact hdeliveryThreshold horizon
      (le_trans (Nat.le_max_right _ _) hhorizon)

end GameTheory
