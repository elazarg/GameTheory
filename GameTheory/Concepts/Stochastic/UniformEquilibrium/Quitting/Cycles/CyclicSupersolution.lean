/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Cycles.PeriodicFiniteHorizonRate

/-!
# Cyclic quitting supersolutions with quit-only error

An undifferentiated one-step root error is geometrically accumulated by the
usual residual telescope.  The mesh certificates used for singleton flows
have a stronger shape: prescribed Continue is exact, while immediate Quit is
at most `e` above the prescribed value.  Adding the same constant `e` to
every cyclic value is then a global Snell supersolution, because Continue
propagates only `c * e ≤ e`.

This file formalizes that sharper comparison and packages it as a terminal
behavioral `e`-Nash compiler.  No cycle-length amplification occurs.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Bellman supersolution comparison -/

/-- One-step contraction of the positive gap between a sub-Bellman value and
a Bellman supersolution. -/
theorem quittingPositiveSubBellmanGap_le_of_superSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (player : ι)
    (super deviation : ℕ → ℝ) (time : ℕ)
    (hdeviation : deviation time ≤
      quittingLiveBellmanValue reward roots player deviation time)
    (hsuper : quittingLiveBellmanValue reward roots player super time ≤
      super time) :
    max (deviation time - super time) 0 ≤
      quittingFixedOpponentsContinueMass roots player time *
        max (deviation (time + 1) - super (time + 1)) 0 := by
  let quitValue := quittingFixedOpponentsQuitValue reward roots player time
  let superContinue :=
    quittingFixedOpponentsContinueReward reward roots player time +
      quittingFixedOpponentsContinueMass roots player time * super (time + 1)
  let deviationContinue :=
    quittingFixedOpponentsContinueReward reward roots player time +
      quittingFixedOpponentsContinueMass roots player time *
        deviation (time + 1)
  let continueMass := quittingFixedOpponentsContinueMass roots player time
  let nextGap := max (deviation (time + 1) - super (time + 1)) 0
  have hmass0 : 0 ≤ continueMass := by
    exact quittingStationaryContinueMass_nonneg
      (Function.update (roots time) player (PMF.pure false))
  have hnext0 : 0 ≤ nextGap := le_max_right _ _
  have hnext : deviation (time + 1) - super (time + 1) ≤ nextGap :=
    le_max_left _ _
  have hcontinue : deviationContinue ≤
      superContinue + continueMass * nextGap := by
    dsimp only [deviationContinue, superContinue, continueMass, nextGap]
    have hscaled := mul_le_mul_of_nonneg_left hnext hmass0
    linarith
  have hbonus0 : 0 ≤ continueMass * nextGap :=
    mul_nonneg hmass0 hnext0
  have hmaximum : max quitValue deviationContinue ≤
      max quitValue superContinue + continueMass * nextGap := by
    apply max_le
    · exact (le_max_left quitValue superContinue).trans
        (le_add_of_nonneg_right hbonus0)
    · exact hcontinue.trans (add_le_add
        (le_max_right quitValue superContinue) (le_refl _))
  have hraw : deviation time - super time ≤
      continueMass * nextGap := by
    dsimp only [quittingLiveBellmanValue, quitValue,
      deviationContinue] at hdeviation
    dsimp only [quittingLiveBellmanValue, quitValue,
      superContinue] at hsuper
    dsimp only [continueMass, nextGap]
    linarith
  exact max_le hraw hbonus0

/-- Finite iteration of the supersolution comparison. -/
theorem quittingPositiveSubBellmanGap_le_survival_of_superSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (player : ι)
    (super deviation : ℕ → ℝ)
    (hdeviation : ∀ time, deviation time ≤
      quittingLiveBellmanValue reward roots player deviation time)
    (hsuper : ∀ time,
      quittingLiveBellmanValue reward roots player super time ≤ super time)
    (start fuel : ℕ) :
    max (deviation start - super start) 0 ≤
      quittingOpponentSurvivalWeight roots player start fuel *
        max (deviation (start + fuel) - super (start + fuel)) 0 := by
  induction fuel with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hstep := quittingPositiveSubBellmanGap_le_of_superSolution
        reward roots player super deviation (start + fuel)
          (hdeviation (start + fuel)) (hsuper (start + fuel))
      have hscaled := mul_le_mul_of_nonneg_left hstep
        (quittingOpponentSurvivalWeight_nonneg roots player start fuel)
      calc
        max (deviation start - super start) 0 ≤
            quittingOpponentSurvivalWeight roots player start fuel *
              max (deviation (start + fuel) -
                super (start + fuel)) 0 := ih
        _ ≤ quittingOpponentSurvivalWeight roots player start fuel *
              (quittingFixedOpponentsContinueMass roots player
                  (start + fuel) *
                max (deviation (start + fuel + 1) -
                  super (start + fuel + 1)) 0) := hscaled
        _ = quittingOpponentSurvivalWeight roots player start (fuel + 1) *
              max (deviation (start + (fuel + 1)) -
                super (start + (fuel + 1))) 0 := by
          rw [quittingOpponentSurvivalWeight_succ]
          rw [show start + (fuel + 1) = start + fuel + 1 by omega]
          ring

/-- A bounded sub-Bellman value lies below every bounded supersolution once
the opponent-survival clock vanishes. -/
theorem quittingSubBellmanValue_le_superSolution_of_survival_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (player : ι)
    (super deviation : ℕ → ℝ) (gapBound : ℝ)
    (hdeviation : ∀ time, deviation time ≤
      quittingLiveBellmanValue reward roots player deviation time)
    (hsuper : ∀ time,
      quittingLiveBellmanValue reward roots player super time ≤ super time)
    (hgapBound : ∀ time,
      max (deviation time - super time) 0 ≤ gapBound)
    (hsurvival : Tendsto
      (quittingOpponentSurvivalWeight roots player 0) atTop (nhds 0)) :
    deviation 0 ≤ super 0 := by
  have hfinite : ∀ fuel,
      max (deviation 0 - super 0) 0 ≤
        quittingOpponentSurvivalWeight roots player 0 fuel * gapBound := by
    intro fuel
    exact
      (quittingPositiveSubBellmanGap_le_survival_of_superSolution
        reward roots player super deviation hdeviation hsuper 0 fuel).trans
      (mul_le_mul_of_nonneg_left (by simpa using hgapBound fuel)
        (quittingOpponentSurvivalWeight_nonneg roots player 0 fuel))
  have hlimit : Tendsto (fun fuel ↦
      quittingOpponentSurvivalWeight roots player 0 fuel * gapBound)
      atTop (nhds 0) := by
    simpa using hsurvival.mul_const gapBound
  have hmax : max (deviation 0 - super 0) 0 ≤ 0 :=
    ge_of_tendsto' hlimit hfinite
  linarith [le_max_left (deviation 0 - super 0) 0]

/-! ## Cyclic quit-only-error compiler -/

/-- Exact cyclic policy evaluation, exact prescribed Continue, and an
`e`-upper bound on immediate Quit make `value + e` a global Snell
supersolution.  Playerwise opponent contraction then controls every
time-dependent unilateral hazard with the same error `e`, without a
cycle-length factor. -/
theorem quittingCyclicHazardTerminalValue_le_add_of_quitError_exactContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) (player : ι) (deviation : ℕ → PMF Bool)
    {e bound : ℝ} (he : 0 ≤ e) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hpolicy : ∀ cyclePhase,
      value cyclePhase = quittingRootSuccessorPayoff reward
        (value (finRotate K cyclePhase)) (cycle cyclePhase))
    (hquit : ∀ cyclePhase who,
      quittingStationaryFixedOpponentsQuitValue
          reward (cycle cyclePhase) who ≤
        value cyclePhase who + e)
    (hcontinue : ∀ cyclePhase who,
      quittingStationaryFixedOpponentsContinueReward
          reward (cycle cyclePhase) who +
        quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) who *
          value (finRotate K cyclePhase) who = value cyclePhase who)
    (hcontracts : ∀ who,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingCyclicRootSequence cycle phase) player deviation 0 ≤
      quittingCyclicTerminalValue reward cycle phase player + e := by
  let roots := quittingCyclicRootSequence cycle phase
  let super : ℕ → ℝ := fun time ↦
    value (quittingCyclicOrbit phase time) player + e
  let deviationValue : ℕ → ℝ := fun time ↦
    quittingRootSequenceHazardTerminalValue
      reward roots player deviation time
  have hvalue : value = quittingCyclicTerminalValue reward cycle :=
    eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff
      reward cycle value hpolicy hcontracts
  have hdeviation : ∀ time, deviationValue time ≤
      quittingLiveBellmanValue reward roots player deviationValue time := by
    intro time
    exact quittingRootSequenceHazardTerminalValue_le_liveBellmanValue
      reward roots player deviation time
  have hsuper : ∀ time,
      quittingLiveBellmanValue reward roots player super time ≤ super time := by
    intro time
    let cyclePhase := quittingCyclicOrbit phase time
    have hmass0 : 0 ≤
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) player :=
      quittingStationaryFixedOpponentsContinueMass_nonneg
        (cycle cyclePhase) player
    have hmass1 : quittingStationaryFixedOpponentsContinueMass
        (cycle cyclePhase) player ≤ 1 :=
      quittingStationaryContinueMass_le_one
        (Function.update (cycle cyclePhase) player (PMF.pure false))
    have hcontinuePhase := hcontinue cyclePhase player
    dsimp only [quittingLiveBellmanValue, roots, super]
    apply max_le
    · change quittingStationaryFixedOpponentsQuitValue
          reward (cycle cyclePhase) player ≤
        value cyclePhase player + e
      exact hquit cyclePhase player
    · change quittingStationaryFixedOpponentsContinueReward
          reward (cycle cyclePhase) player +
          quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) player *
            (value (quittingCyclicOrbit phase (time + 1)) player + e) ≤
        value cyclePhase player + e
      rw [quittingCyclicOrbit_succ]
      nlinarith
  have hgapBound : ∀ time,
      max (deviationValue time - super time) 0 ≤ 2 * bound := by
    intro time
    have hdev := abs_quittingTerminalPayoff_le reward
      (quittingRootSequenceProfile reward
        (quittingRootSequenceUpdate roots player deviation) time)
      player hbound hreward
    have hval : |value (quittingCyclicOrbit phase time) player| ≤ bound := by
      rw [hvalue]
      simpa only [quittingTerminalPayoff_cyclicBehaviorProfile] using
        (abs_quittingTerminalPayoff_le reward
          (quittingCyclicBehaviorProfile reward cycle
            (quittingCyclicOrbit phase time)) player hbound hreward)
    have hraw : deviationValue time - super time ≤ 2 * bound := by
      dsimp only [deviationValue, super,
        quittingRootSequenceHazardTerminalValue,
        quittingRootSequenceTerminalValue] at hdev ⊢
      rw [abs_le] at hdev hval
      linarith
    exact max_le hraw (by linarith)
  have hsurvival : Tendsto
      (quittingOpponentSurvivalWeight roots player 0) atTop (nhds 0) := by
    dsimp only [roots]
    exact tendsto_zero_quittingOpponentSurvivalWeight_cyclicRootSequence
      cycle phase player (hcontracts player)
  have hcomparison :=
    quittingSubBellmanValue_le_superSolution_of_survival_zero
      reward roots player super deviationValue (2 * bound)
      hdeviation hsuper hgapBound hsurvival
  dsimp only [deviationValue, super] at hcomparison
  rw [hvalue] at hcomparison
  simpa using hcomparison

/-- Behavioral form of the cyclic quit-only-error supersolution compiler. -/
theorem isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) {e bound : ℝ}
    (he : 0 ≤ e) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hpolicy : ∀ cyclePhase,
      value cyclePhase = quittingRootSuccessorPayoff reward
        (value (finRotate K cyclePhase)) (cycle cyclePhase))
    (hquit : ∀ cyclePhase who,
      quittingStationaryFixedOpponentsQuitValue
          reward (cycle cyclePhase) who ≤
        value cyclePhase who + e)
    (hcontinue : ∀ cyclePhase who,
      quittingStationaryFixedOpponentsContinueReward
          reward (cycle cyclePhase) who +
        quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) who *
          value (finRotate K cyclePhase) who = value cyclePhase who)
    (hcontracts : ∀ who,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) e
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  intro player deviation
  have hhazard :=
    quittingCyclicHazardTerminalValue_le_add_of_quitError_exactContinue
      reward cycle value phase player
        (quittingBehaviorLiveHazard reward deviation)
        he hbound hreward hpolicy hquit hcontinue hcontracts
  have hdeviation :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward (quittingCyclicBehaviorProfile reward cycle phase)
        player deviation
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile] at hdeviation
  rw [hdeviation]
  simpa only [quittingTerminalPayoff_cyclicBehaviorProfile] using hhazard

end GameTheory
