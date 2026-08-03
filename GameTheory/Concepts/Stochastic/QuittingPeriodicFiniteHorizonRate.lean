/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingPeriodicClosing
import GameTheory.Concepts.Stochastic.QuittingPeriodicMeshRate

/-!
# Finite-horizon rates for periodic quitting certificates

The periodic closing machinery produces a player-specific terminal deviation
charge.  This file first packages those charges as a terminal behavioral
approximate Nash equilibrium.  It then combines that terminal error with
explicit finite-horizon delivery and deviation-boundary estimates.

For an accuracy-indexed mesh, a terminal charge of order `A / m` and a
finite-horizon boundary charge of order `B * m / N` give the game-facing
`(A + 2 * B) / sqrt N` Nash bound.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Approximate periodic compiler -/

/-- A playerwise bound on the cyclic residual charge packages the periodic
root-error closing theorem as a terminal behavioral approximate Nash
equilibrium. -/
theorem isεAsymptoticNash_quittingCyclicBehaviorProfile_of_rootError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (rootError : Fin K → ι → ℝ) (ε bound : ℝ)
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hrootError0 : ∀ cyclePhase player,
      0 ≤ rootError cyclePhase player)
    (hroot : ∀ cyclePhase player (oneShot : PMF Bool),
      quittingRootExpectedPayoff reward
          (quittingCyclicTerminalValue reward cycle
            (finRotate K cyclePhase))
          (Function.update (cycle cyclePhase) player oneShot) player ≤
        quittingRootExpectedPayoff reward
            (quittingCyclicTerminalValue reward cycle
              (finRotate K cyclePhase))
            (cycle cyclePhase) player + rootError cyclePhase player)
    (hcontracts : ∀ player,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) player) < 1)
    (hcharge : ∀ player,
      quittingCyclicResidualCharge
          (fun cyclePhase ↦
            quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) player)
          (fun cyclePhase ↦ rootError cyclePhase player) phase K /
        (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) player) ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  intro player deviation
  have hhazard := quittingCyclicHazardTerminalGap_le_of_rootError
    reward cycle phase player
      (quittingBehaviorLiveHazard reward deviation)
      (fun cyclePhase ↦ rootError cyclePhase player)
      bound hbound0 hreward
      (fun cyclePhase ↦ hrootError0 cyclePhase player)
      (fun cyclePhase oneShot ↦ hroot cyclePhase player oneShot)
      (hcontracts player)
  have hdeviation :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward (quittingCyclicBehaviorProfile reward cycle phase)
        player deviation
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile] at hdeviation
  rw [← quittingTerminalPayoff_cyclicBehaviorProfile
    reward cycle phase] at hhazard
  rw [hdeviation]
  linarith [hcharge player]

/-- Finiteness supplies the reward bound for the approximate periodic
compiler. -/
theorem isεAsymptoticNash_quittingCyclicBehaviorProfile_of_rootError_finite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (rootError : Fin K → ι → ℝ) (ε : ℝ)
    (hrootError0 : ∀ cyclePhase player,
      0 ≤ rootError cyclePhase player)
    (hroot : ∀ cyclePhase player (oneShot : PMF Bool),
      quittingRootExpectedPayoff reward
          (quittingCyclicTerminalValue reward cycle
            (finRotate K cyclePhase))
          (Function.update (cycle cyclePhase) player oneShot) player ≤
        quittingRootExpectedPayoff reward
            (quittingCyclicTerminalValue reward cycle
              (finRotate K cyclePhase))
            (cycle cyclePhase) player + rootError cyclePhase player)
    (hcontracts : ∀ player,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) player) < 1)
    (hcharge : ∀ player,
      quittingCyclicResidualCharge
          (fun cyclePhase ↦
            quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) player)
          (fun cyclePhase ↦ rootError cyclePhase player) phase K /
        (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) player) ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  exact
    isεAsymptoticNash_quittingCyclicBehaviorProfile_of_rootError
      reward cycle phase rootError ε (quittingRewardBound reward)
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
      hrootError0 hroot hcontracts hcharge

/-! ## Quantitative finite-horizon transfer -/

/-- At one fixed horizon, terminal Nash error, prescribed delivery error,
and the one-sided deviation boundary error add. -/
theorem StochasticGame.IsεAsymptoticNash.isεHorizonNash_of_explicitBounds
    {G : StochasticGame ι} {initial : G.State}
    {u : G.BehaviorProfile → ι → ℝ}
    {profile : G.BehaviorProfile}
    {horizon : ℕ} {terminalError deliveryError deviationError : ℝ}
    (hnash : G.IsεAsymptoticNash u terminalError profile)
    (hdelivery : ∀ player,
      |G.finiteAveragePayoff initial horizon profile player -
        u profile player| ≤ deliveryError)
    (hdeviation : ∀ player (deviation : G.BehaviorStrategy player),
      G.finiteAveragePayoff initial horizon
          (Function.update profile player deviation) player ≤
        u (Function.update profile player deviation) player +
          deviationError) :
    G.IsεHorizonNash initial horizon
      (terminalError + deliveryError + deviationError) profile := by
  intro player deviation
  have hterminal := hnash player deviation
  have honPath := (abs_le.mp (hdelivery player)).1
  have hfinite := hdeviation player deviation
  linarith

/-! ## Square-root periodic mesh rate -/

/-- Game-facing square-root rate for an accuracy-indexed cyclic quitting
certificate.  The cyclic residual charge supplies the terminal error; the
two explicit finite-horizon estimates supply the boundary error. -/
theorem isSqrtRateHorizonNash_quittingCyclicBehaviorProfile_of_rootError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (rootError : Fin K → ι → ℝ)
    {N : ℕ} {A B m deliveryError deviationError : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 1 ≤ (N : ℝ))
    (hm_lower : Real.sqrt (N : ℝ) ≤ m)
    (hm_upper : m ≤ 2 * Real.sqrt (N : ℝ))
    (hrootError0 : ∀ cyclePhase player,
      0 ≤ rootError cyclePhase player)
    (hroot : ∀ cyclePhase player (oneShot : PMF Bool),
      quittingRootExpectedPayoff reward
          (quittingCyclicTerminalValue reward cycle
            (finRotate K cyclePhase))
          (Function.update (cycle cyclePhase) player oneShot) player ≤
        quittingRootExpectedPayoff reward
            (quittingCyclicTerminalValue reward cycle
              (finRotate K cyclePhase))
            (cycle cyclePhase) player + rootError cyclePhase player)
    (hcontracts : ∀ player,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) player) < 1)
    (hterminal : ∀ player,
      quittingCyclicResidualCharge
          (fun cyclePhase ↦
            quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) player)
          (fun cyclePhase ↦ rootError cyclePhase player) phase K /
        (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) player) ≤ A / m)
    (hdelivery : ∀ player,
      |(quittingGame reward).finiteAveragePayoff none N
          (quittingCyclicBehaviorProfile reward cycle phase) player -
        quittingCyclicTerminalValue reward cycle phase player| ≤
          deliveryError)
    (hdeviation : ∀ player
        (deviation : (quittingGame reward).BehaviorStrategy player),
      (quittingGame reward).finiteAveragePayoff none N
          (Function.update
            (quittingCyclicBehaviorProfile reward cycle phase)
            player deviation) player ≤
        quittingTerminalPayoff reward
            (Function.update
              (quittingCyclicBehaviorProfile reward cycle phase)
              player deviation) player + deviationError)
    (hboundary : deliveryError + deviationError ≤ B * m / (N : ℝ)) :
    (quittingGame reward).IsεHorizonNash none N
      ((A + 2 * B) / Real.sqrt (N : ℝ))
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  let profile := quittingCyclicBehaviorProfile reward cycle phase
  have hterminalNash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (A / m) profile := by
    exact
      isεAsymptoticNash_quittingCyclicBehaviorProfile_of_rootError_finite
        reward cycle phase rootError (A / m)
        hrootError0 hroot hcontracts hterminal
  have hdelivery' : ∀ player,
      |(quittingGame reward).finiteAveragePayoff none N
          profile player -
        quittingTerminalPayoff reward profile player| ≤ deliveryError := by
    intro player
    simpa only [profile,
      quittingTerminalPayoff_cyclicBehaviorProfile] using hdelivery player
  have hdeviation' : ∀ player
      (deviation : (quittingGame reward).BehaviorStrategy player),
      (quittingGame reward).finiteAveragePayoff none N
          (Function.update profile player deviation) player ≤
        quittingTerminalPayoff reward
            (Function.update profile player deviation) player +
          deviationError := by
    simpa only [profile] using hdeviation
  have hfinite :=
    hterminalNash.isεHorizonNash_of_explicitBounds
      hdelivery' hdeviation'
  apply hfinite.mono
  calc
    A / m + deliveryError + deviationError =
        A / m + (deliveryError + deviationError) := by ring
    _ ≤ A / m + B * m / (N : ℝ) :=
      add_le_add (le_refl _) hboundary
    _ ≤ (A + 2 * B) / Real.sqrt (N : ℝ) :=
      inv_add_linear_le_sqrt_rate hA hB hN hm_lower hm_upper

end GameTheory
