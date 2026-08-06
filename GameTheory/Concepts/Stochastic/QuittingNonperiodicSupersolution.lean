/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCyclicSupersolution
import GameTheory.Concepts.Stochastic.QuittingInfinitePathCompiler

/-!
# Nonperiodic quitting paths with quit-only error

A singleton-flow mesh does not generally satisfy exact one-root Nash.  It has
a sharper asymmetric certificate: prescribed policy evaluation and prescribed
Continue are exact, while immediate Quit is at most `e` above the prescribed
value.

The cyclic compiler already exploits this shape without accumulating `e`
around a cycle.  The same supersolution argument is completely nonperiodic.
Adding the constant `e` to the supplied value path gives a global Bellman
supersolution because every opponent-continue coefficient is at most one.
Vanishing opponent survival kills the terminal boundary, so the same `e`
controls every time-dependent unilateral hazard.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A bounded nonperiodic path with exact prescribed Continue and a uniform
quit-only error controls every time-dependent unilateral quitting hazard by
the same error.  Only the qualitative playerwise survival limit is needed. -/
theorem
    quittingNonperiodicHazardTerminalValue_le_add_of_quitError_exactContinue_of_survival_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (player : ι) (deviation : ℕ → PMF Bool)
    {e bound : ℝ}
    (he : 0 ≤ e) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hsurvival : Tendsto
      (quittingOpponentSurvivalWeight roots player 0) atTop (nhds 0))
    (hquit : ∀ time who,
      quittingFixedOpponentsQuitValue reward roots who time ≤
        value time who + e)
    (hcontinue : ∀ time who,
      quittingFixedOpponentsContinueReward reward roots who time +
        quittingFixedOpponentsContinueMass roots who time *
          value (time + 1) who = value time who) :
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
        quittingFixedOpponentsContinueMass roots player time :=
      quittingStationaryContinueMass_nonneg
        (Function.update (roots time) player (PMF.pure false))
    have hmass1 : quittingFixedOpponentsContinueMass roots player time ≤ 1 :=
      quittingStationaryContinueMass_le_one
        (Function.update (roots time) player (PMF.pure false))
    have hcontinueTime := hcontinue time player
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

/-- Uniform block contraction is a quantitative sufficient condition for the
nonperiodic quit-only-error comparison. -/
theorem
    quittingNonperiodicHazardTerminalValue_le_add_of_quitError_exactContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (player : ι) (deviation : ℕ → PMF Bool)
    {e rho bound : ℝ}
    (he : 0 ≤ e) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hK : 0 < K)
    (hblock : IsQuittingOpponentBlockContraction roots K rho)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hquit : ∀ time who,
      quittingFixedOpponentsQuitValue reward roots who time ≤
        value time who + e)
    (hcontinue : ∀ time who,
      quittingFixedOpponentsContinueReward reward roots who time +
        quittingFixedOpponentsContinueMass roots who time *
          value (time + 1) who = value time who) :
    quittingRootSequenceHazardTerminalValue reward roots player deviation 0 ≤
      value 0 player + e := by
  exact
    quittingNonperiodicHazardTerminalValue_le_add_of_quitError_exactContinue_of_survival_tendsto_zero
      reward roots value player deviation he hbound hreward hvalueBound
      (tendsto_zero_quittingOpponentSurvivalWeight_of_blockContraction
        roots hK hblock hrho0 hrho1 player 0)
      hquit hcontinue

/-- **Nonperiodic quit-only-error compiler.** Exact policy evaluation selects
the supplied value path.  Exact Continue, a uniform immediate-Quit error, and
vanishing playerwise opponent survival compile to a terminal behavioral
`e`-Nash profile delivering `value 0`. -/
theorem
    nonperiodicPath_isAsymptoticNash_and_delivers_of_quitError_exactContinue_of_survival_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    {e bound : ℝ}
    (he : 0 ≤ e)
    (hsurvival : ∀ who start,
      Tendsto (quittingOpponentSurvivalWeight roots who start)
        atTop (nhds 0))
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hquit : ∀ time who,
      quittingFixedOpponentsQuitValue reward roots who time ≤
        value time who + e)
    (hcontinue : ∀ time who,
      quittingFixedOpponentsContinueReward reward roots who time +
        quittingFixedOpponentsContinueMass roots who time *
          value (time + 1) who = value time who) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) e
        (quittingInfinitePathProfile reward roots) ∧
      quittingTerminalPayoff reward
          (quittingInfinitePathProfile reward roots) = value 0 := by
  have hselected :=
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_survival_tendsto_zero
      reward roots value hsurvival hbound hreward hvalueBound hpolicy
  have hdelivery : quittingTerminalPayoff reward
      (quittingInfinitePathProfile reward roots) = value 0 := by
    funext who
    rw [quittingTerminalPayoff_infinitePathProfile]
    exact (congrFun (hselected 0) who).symm
  constructor
  · intro player deviation
    have hhazard :=
      quittingNonperiodicHazardTerminalValue_le_add_of_quitError_exactContinue_of_survival_tendsto_zero
        reward roots value player
          (quittingBehaviorLiveHazard reward deviation)
          he hbound hreward hvalueBound (hsurvival player 0)
          hquit hcontinue
    have hdeviation :=
      quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
        reward (quittingInfinitePathProfile reward roots) player deviation
    rw [quittingProfileLiveRoot_infinitePathProfile] at hdeviation
    rw [hdeviation, congrFun hdelivery player]
    exact hhazard
  · exact hdelivery

/-- Block-contraction form of the nonperiodic quit-only-error compiler. -/
theorem nonperiodicPath_isAsymptoticNash_and_delivers_of_quitError_exactContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    {e rho bound : ℝ}
    (he : 0 ≤ e)
    (hK : 0 < K)
    (hblock : IsQuittingOpponentBlockContraction roots K rho)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hquit : ∀ time who,
      quittingFixedOpponentsQuitValue reward roots who time ≤
        value time who + e)
    (hcontinue : ∀ time who,
      quittingFixedOpponentsContinueReward reward roots who time +
        quittingFixedOpponentsContinueMass roots who time *
          value (time + 1) who = value time who) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) e
        (quittingInfinitePathProfile reward roots) ∧
      quittingTerminalPayoff reward
          (quittingInfinitePathProfile reward roots) = value 0 := by
  exact
    nonperiodicPath_isAsymptoticNash_and_delivers_of_quitError_exactContinue_of_survival_tendsto_zero
      reward roots value he
      (fun who start ↦
        tendsto_zero_quittingOpponentSurvivalWeight_of_blockContraction
          roots hK hblock hrho0 hrho1 who start)
      hbound hreward hvalueBound hpolicy hquit hcontinue

/-- A terminal quit-only-error path becomes a uniform `ε`-equilibrium and its
finite-horizon payoffs uniformly approach the supplied initial value whenever
its terminal error is strictly below `ε`. -/
theorem
    nonperiodicPath_isUniformεEquilibrium_and_delivers_of_quitError_exactContinue_of_survival_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    {e ε bound : ℝ}
    (he : 0 ≤ e) (herror : e < ε)
    (hsurvival : ∀ who start,
      Tendsto (quittingOpponentSurvivalWeight roots who start)
        atTop (nhds 0))
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hquit : ∀ time who,
      quittingFixedOpponentsQuitValue reward roots who time ≤
        value time who + e)
    (hcontinue : ∀ time who,
      quittingFixedOpponentsContinueReward reward roots who time +
        quittingFixedOpponentsContinueMass roots who time *
          value (time + 1) who = value time who) :
    ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
      (quittingGame reward).IsεHorizonNash none horizon ε
        (quittingInfinitePathProfile reward roots) ∧
      ∀ who,
        |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingInfinitePathProfile reward roots) who -
          value 0 who| ≤ ε := by
  let profile := quittingInfinitePathProfile reward roots
  have hcompiled :=
    nonperiodicPath_isAsymptoticNash_and_delivers_of_quitError_exactContinue_of_survival_tendsto_zero
      reward roots value he hsurvival hbound hreward hvalueBound
        hpolicy hquit hcontinue
  have hterminalNash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) e profile := by
    simpa only [profile] using hcompiled.1
  have hterminalValue : quittingTerminalPayoff reward profile = value 0 := by
    simpa only [profile] using hcompiled.2
  have huniform : (quittingGame reward).IsUniformεEquilibrium
      none ε profile :=
    quittingGame_isUniformεEquilibrium_of_terminalNash
      reward profile herror hterminalNash bound hbound hreward
  obtain ⟨nashThreshold, hnashThreshold⟩ := huniform
  have heventuallyDelivery : ∀ᶠ horizon : ℕ in atTop, ∀ who,
      |(quittingGame reward).finiteAveragePayoff none horizon profile who -
          value 0 who| ≤ ε := by
    apply Filter.eventually_all.mpr
    intro who
    have hε : 0 < ε := lt_of_le_of_lt he herror
    have hball :=
      (tendsto_finiteAveragePayoff_quittingGame reward profile who).eventually
        (Metric.ball_mem_nhds
          (quittingTerminalPayoff reward profile who) hε)
    filter_upwards [hball] with horizon hhorizon
    have hvalue := congrFun hterminalValue who
    rw [hvalue] at hhorizon
    simpa [Metric.mem_ball, Real.dist_eq] using hhorizon.le
  obtain ⟨deliveryThreshold, hdeliveryThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨max nashThreshold deliveryThreshold, fun horizon hhorizon ↦ ?_⟩
  constructor
  · exact hnashThreshold horizon
      (le_trans (Nat.le_max_left _ _) hhorizon)
  · exact hdeliveryThreshold horizon
      (le_trans (Nat.le_max_right _ _) hhorizon)

end GameTheory
