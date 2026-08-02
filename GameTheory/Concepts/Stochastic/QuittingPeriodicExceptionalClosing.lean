/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingPeriodicClosing

/-!
# Periodic closing with one noncontracting opponent clock

A cyclic quitting profile need not contract every player's opponent-only
survival clock.  Exact phasewise root Nash still closes globally on the
exceptional branch when that player's singleton quitting reward is
nonnegative.  This file packages that branch at the hazard, behavioral, and
uniform-equilibrium levels.

The zero-error hypothesis on a noncontracting branch is essential here.  A
positive phase error repeats forever and its opponent-survival-weighted sum
need not be finite.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact cyclic root Nash controls every time-dependent unilateral hazard
when the selected player's opponent cycle either contracts or the player's
singleton quitting reward is nonnegative. -/
theorem quittingCyclicHazardTerminalValue_le_of_isZeroRootNash_of_branch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι)
    (deviation : ℕ → PMF Bool) (bound : ℝ)
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (hbranch :
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1 ∨
      0 ≤ reward (quittingSingletonTerminal who) who) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingCyclicRootSequence cycle phase) who deviation 0 ≤
      quittingCyclicTerminalValue reward cycle phase who := by
  let roots := quittingCyclicRootSequence cycle phase
  let prescribed := quittingRootSequenceTerminalValue reward roots who
  let profile := quittingCyclicBehaviorProfile reward cycle phase
  let opponentProfile := quittingOpponentOnlyProfile reward profile who
  let limit := quittingLiveMassLimit reward opponentProfile
  have hresidual : ∀ time,
      quittingPrescribedOneStepResidual reward roots who prescribed time =
        0 := by
    intro time
    exact quittingPrescribedOneStepResidual_cyclic_eq_zero
      reward cycle phase who hnash time
  have hsummable : Summable (fun time =>
      quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who prescribed time) :=
    by
      simpa only [hresidual, mul_zero] using
        (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have hweights : quittingOpponentSurvivalWeight roots who 0 =
      quittingLiveMass reward opponentProfile := by
    dsimp only [roots, opponentProfile, profile]
    rw [← quittingProfileLiveRoot_cyclicBehaviorProfile
      reward cycle phase]
    funext fuel
    exact quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
      reward (quittingCyclicBehaviorProfile reward cycle phase) who fuel
  have hlimit : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds limit) := by
    rw [hweights]
    exact tendsto_quittingLiveMass reward opponentProfile
  have hlimitBranch : limit = 0 ∨
      0 ≤ reward (quittingSingletonTerminal who) who := by
    rcases hbranch with hcontracts | hsolo
    · left
      have hzero : Tendsto
          (quittingOpponentSurvivalWeight roots who 0) atTop (nhds 0) := by
        dsimp only [roots]
        exact
          tendsto_zero_quittingOpponentSurvivalWeight_cyclicRootSequence
            cycle phase who hcontracts
      exact tendsto_nhds_unique hlimit hzero
    · exact Or.inr hsolo
  have hgap :=
    quittingRootSequenceHazardTerminalGap_le_tsum_residual_of_zero_or_nonnegativeSolo
      reward roots who deviation bound limit hbound0 hreward hlimit
        hlimitBranch hsummable
  have hsum : (∑' time,
      quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who prescribed time) =
      0 := by
    simp only [hresidual, mul_zero, tsum_zero]
  rw [hsum] at hgap
  have hbase : prescribed 0 =
      quittingCyclicTerminalValue reward cycle phase who := by
    dsimp only [prescribed, roots]
    rw [quittingRootSequenceTerminalValue_cyclic_eq]
    simp
  dsimp only [roots, prescribed] at hgap hbase ⊢
  linarith

/-- Exact phasewise root Nash and the contraction-or-nonnegative-solo branch
for every player make the cyclic behavior profile an exact terminal Nash
profile. -/
theorem isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_branches
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (bound : ℝ) (hbound0 : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (hbranches : ∀ who,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1 ∨
      0 ≤ reward (quittingSingletonTerminal who) who) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  intro who deviation
  have hhazard :=
    quittingCyclicHazardTerminalValue_le_of_isZeroRootNash_of_branch
      reward cycle phase who (quittingBehaviorLiveHazard reward deviation)
        bound hbound0 hreward hnash (hbranches who)
  rw [← quittingTerminalPayoff_cyclicBehaviorProfile
    reward cycle phase] at hhazard
  have hdeviation :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward (quittingCyclicBehaviorProfile reward cycle phase) who deviation
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile] at hdeviation
  rw [hdeviation]
  simpa using hhazard

/-- Finiteness supplies the reward bound in the exact exceptional cyclic
compiler. -/
theorem isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_branches_finite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (hbranches : ∀ who,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1 ∨
      0 ≤ reward (quittingSingletonTerminal who) who) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  exact isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_branches
    reward cycle phase (quittingRewardBound reward)
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) hnash hbranches

/-- The terminal vector of an exact cyclic profile satisfying the
contraction-or-nonnegative-solo branch is a uniform equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_branches
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (hbranches : ∀ who,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1 ∨
      0 ≤ reward (quittingSingletonTerminal who) who) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingCyclicTerminalValue reward cycle phase) := by
  let profile := quittingCyclicBehaviorProfile reward cycle phase
  have hterminalNash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 profile :=
    isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_branches_finite
      reward cycle phase hnash hbranches
  intro ε hε
  have huniform : (quittingGame reward).IsUniformεEquilibrium
      none ε profile :=
    quittingGame_isUniformεEquilibrium_of_terminalNash_finite
      reward profile hε hterminalNash
  obtain ⟨nashThreshold, hnashThreshold⟩ := huniform
  have heventuallyDelivery : ∀ᶠ horizon : ℕ in atTop, ∀ player,
      |(quittingGame reward).finiteAveragePayoff none horizon profile player -
        quittingCyclicTerminalValue reward cycle phase player| < ε := by
    apply Filter.eventually_all.mpr
    intro player
    have hball :=
      (tendsto_finiteAveragePayoff_quittingGame reward profile player).eventually
        (Metric.ball_mem_nhds
          (quittingTerminalPayoff reward profile player) hε)
    filter_upwards [hball] with horizon hhorizon
    simpa only [Metric.mem_ball, Real.dist_eq, profile,
      quittingTerminalPayoff_cyclicBehaviorProfile] using hhorizon
  obtain ⟨deliveryThreshold, hdeliveryThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨profile, max nashThreshold deliveryThreshold,
    fun horizon hhorizon => ?_⟩
  constructor
  · exact hnashThreshold horizon
      (le_trans (Nat.le_max_left _ _) hhorizon)
  · intro player
    exact (hdeliveryThreshold horizon
      (le_trans (Nat.le_max_right _ _) hhorizon) player).le

end GameTheory
