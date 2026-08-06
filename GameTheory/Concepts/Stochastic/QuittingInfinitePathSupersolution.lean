/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingInfinitePathCompiler
import GameTheory.Concepts.Stochastic.QuittingCyclicSupersolution

/-!
# Nonperiodic quitting-path supersolutions

A nonperiodic singleton-flow mesh need not satisfy exact one-root Nash at each
microstage.  Its stronger local shape is enough: prescribed Continue is exact,
while immediate Quit is at most one common error `e` above the prescribed
value.  Adding `e` to the supplied value path is then a global Bellman
supersolution.  Vanishing opponent survival compares every time-dependent
unilateral deviation with that supersolution without accumulating `e` over
calendar time.

This is the arbitrary-path counterpart of the cyclic supersolution compiler.
It separates the game-facing argument from the later construction of an
accuracy-indexed nonperiodic subdivision.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact prescribed Continue and a uniform immediate-Quit error make
`value + e` a global Snell supersolution along an arbitrary root sequence.
If the selected player's opponent-survival clock vanishes, every unilateral
hazard has terminal value at most `value 0 + e`. -/
theorem
    quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue
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
        quittingStationaryFixedOpponentsContinueMass (roots time) player :=
      quittingStationaryFixedOpponentsContinueMass_nonneg
        (roots time) player
    have hmass1 :
        quittingStationaryFixedOpponentsContinueMass (roots time) player ≤ 1 :=
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

/-- **Nonperiodic quit-only-error compiler.**  A bounded exact policy path
whose prescribed Continue equations are exact and whose immediate Quit values
are at most `e` above the prescribed path is a terminal behavioral `e`-Nash
profile whenever every shifted opponent-survival clock vanishes.  The
terminal payoff is exactly the supplied initial value. -/
theorem
    infinitePath_isεAsymptoticNash_and_delivers_of_quitError_exactContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    {e bound : ℝ} (he : 0 ≤ e) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hquit : ∀ time who,
      quittingStationaryFixedOpponentsQuitValue reward (roots time) who ≤
        value time who + e)
    (hcontinue : ∀ time who,
      quittingStationaryFixedOpponentsContinueReward reward
            (roots time) who +
          quittingStationaryFixedOpponentsContinueMass
              (roots time) who * value (time + 1) who =
        value time who)
    (hsurvival : ∀ who start,
      Tendsto (quittingOpponentSurvivalWeight roots who start)
        atTop (nhds 0)) :
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
      quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue
        reward roots value player
          (quittingBehaviorLiveHazard reward deviation)
          he hbound hreward hvalueBound hquit hcontinue
          (hsurvival player 0)
    have hdeviation :=
      quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
        reward (quittingInfinitePathProfile reward roots) player deviation
    rw [quittingProfileLiveRoot_infinitePathProfile] at hdeviation
    rw [hdeviation, hdelivery]
    exact hhazard
  · exact hdelivery

end GameTheory
