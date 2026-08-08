/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.CyclicSupersolution
import UniformEquilibrium.Quitting.Paths.InfinitePathCompiler

/-!
# Nonperiodic quitting-path supersolutions

The ordinary residual telescope accumulates a generic one-step error.  A
singleton-flow mesh has a stronger shape: prescribed Continue is exact, while
immediate Quit is at most `e` above the prescribed value.  Adding the same
constant `e` to every value is then a Snell supersolution, because a Continue
step transports only `c * e ≤ e`.

This file removes the cyclicity restriction from that argument.  On an
arbitrary infinite root path, exact policy evaluation, exact prescribed
Continue, a uniform immediate-Quit cap, bounded values, and vanishing
playerwise opponent survival imply terminal `e`-Nash play with no accumulation
in time.  Accuracy-indexed certificates therefore yield a uniform-equilibrium
payoff.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A bounded nonperiodic root path with exact Bellman transport, exact
prescribed-Continue transport, and a uniform immediate-Quit error. -/
structure QuittingInfinitePathQuitErrorCertificate
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
  quit_le : ∀ time who,
    quittingStationaryFixedOpponentsQuitValue reward (roots time) who ≤
      value time who + error
  continue_eq : ∀ time who,
    quittingStationaryFixedOpponentsContinueReward reward
          (roots time) who +
        quittingStationaryFixedOpponentsContinueMass
            (roots time) who * value (time + 1) who =
      value time who

/-- **Nonperiodic Snell comparison.**  Exact Continue and an `e`-cap on
immediate Quit make `value + e` a global supersolution.  Vanishing opponent
survival then bounds every history-dependent unilateral hazard by the same
single error `e`; there is no sum over time. -/
theorem quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (player : ι) (deviation : ℕ → PMF Bool)
    {e bound : ℝ} (he : 0 ≤ e) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hquit : ∀ time who,
      quittingStationaryFixedOpponentsQuitValue reward (roots time) who ≤
        value time who + e)
    (hcontinue : ∀ time who,
      quittingStationaryFixedOpponentsContinueReward reward
            (roots time) who +
          quittingStationaryFixedOpponentsContinueMass
              (roots time) who * value (time + 1) who =
        value time who)
    (hsurvival : Tendsto
      (quittingOpponentSurvivalWeight roots player 0) atTop (nhds 0)) :
    quittingRootSequenceHazardTerminalValue reward roots player deviation 0 ≤
      value 0 player + e := by
  let super : ℕ → ℝ := fun time ↦ value time player + e
  let deviationValue : ℕ → ℝ := fun time ↦
    quittingRootSequenceHazardTerminalValue
      reward roots player deviation time
  have hdeviation : ∀ time, deviationValue time ≤
      quittingLiveBellmanValue reward roots player deviationValue time := by
    intro time
    exact quittingRootSequenceHazardTerminalValue_le_liveBellmanValue
      reward roots player deviation time
  have hsuper : ∀ time,
      quittingLiveBellmanValue reward roots player super time ≤ super time := by
    intro time
    have hmass0 : 0 ≤
        quittingFixedOpponentsContinueMass roots player time := by
      change 0 ≤ quittingStationaryFixedOpponentsContinueMass
        (roots time) player
      exact quittingStationaryFixedOpponentsContinueMass_nonneg
        (roots time) player
    have hmass1 :
        quittingFixedOpponentsContinueMass roots player time ≤ 1 := by
      change quittingStationaryFixedOpponentsContinueMass
          (roots time) player ≤ 1
      exact quittingStationaryContinueMass_le_one
        (Function.update (roots time) player (PMF.pure false))
    have hcontinueTime :
        quittingFixedOpponentsContinueReward reward roots player time +
          quittingFixedOpponentsContinueMass roots player time *
            value (time + 1) player =
          value time player := by
      change quittingStationaryFixedOpponentsContinueReward
          reward (roots time) player +
        quittingStationaryFixedOpponentsContinueMass (roots time) player *
          value (time + 1) player = value time player
      exact hcontinue time player
    dsimp only [quittingLiveBellmanValue, super]
    apply max_le
    · exact hquit time player
    · nlinarith
  have hgapBound : ∀ time,
      max (deviationValue time - super time) 0 ≤ 2 * bound := by
    intro time
    have hdev := abs_quittingTerminalPayoff_le reward
      (quittingRootSequenceProfile reward
        (quittingRootSequenceUpdate roots player deviation) time)
      player hbound hreward
    have hval := hvalueBound time player
    have hraw : deviationValue time - super time ≤ 2 * bound := by
      dsimp only [deviationValue, super,
        quittingRootSequenceHazardTerminalValue,
        quittingRootSequenceTerminalValue] at hdev ⊢
      rw [abs_le] at hdev hval
      linarith
    exact max_le hraw (by linarith)
  have hcomparison :=
    quittingSubBellmanValue_le_superSolution_of_survival_zero
      reward roots player super deviationValue (2 * bound)
      hdeviation hsuper hgapBound hsurvival
  simpa only [deviationValue, super] using hcomparison

/-- A nonperiodic quit-error certificate compiles to terminal `error`-Nash
play and delivers its distinguished target exactly in terminal payoff. -/
theorem QuittingInfinitePathQuitErrorCertificate.isεAsymptoticNash_and_delivers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) {error bound : ℝ}
    (certificate : QuittingInfinitePathQuitErrorCertificate
      reward target error bound)
    (herror : 0 ≤ error) (hbound : 0 ≤ bound)
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
  · intro player deviation
    have hhazard :=
      quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue
        reward certificate.roots certificate.value player
          (quittingBehaviorLiveHazard reward deviation)
          herror hbound hreward certificate.value_bound
          certificate.quit_le certificate.continue_eq
          (certificate.survival player 0)
    have hdeviation :=
      quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
        reward (quittingInfinitePathProfile reward certificate.roots)
          player deviation
    rw [quittingProfileLiveRoot_infinitePathProfile] at hdeviation
    rw [hdeviation, hdelivery]
    simpa [certificate.value_zero] using hhazard
  · exact hdelivery

/-- **Accuracy-indexed nonperiodic compiler.**  If the same target admits a
bounded quit-error certificate at every positive tolerance, then it is a
uniform-equilibrium payoff.  Each tolerance may use a different time change,
root path, and value path. -/
theorem isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hcertificates : ∀ error, 0 < error →
      Nonempty (QuittingInfinitePathQuitErrorCertificate
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
