/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingStationaryBestResponse
import GameTheory.Concepts.Stochastic.QuittingFiniteNashBellmanDebtMonotonicity

/-!
# Full-rate stationary best-response verification

The stationary Snell cap evaluates behavioral deviations whenever the fixed
opponents have continuation mass strictly below one.  This module closes the
remaining boundary face.  If that mass is one, every opponent marginal is
pure Continue, so the exact unilateral cap is the larger of Never's payoff
zero and the player's singleton quitting reward.

`quittingStationaryFullRateUnilateralCap` bundles the two regimes.  Every
behavioral deviation is bounded by this cap, and a deterministic behavioral
deviation attains it.  Consequently its pointwise inequalities characterize
terminal approximate Nash for any supplied stationary product root, including
roots with unit quitting probabilities.

This is a verifier for a supplied root.  It does not construct or search for
stationary roots, prove that one exists, characterize nonstationary equilibrium
profiles, or provide a uniform-equilibrium delivery theorem.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The exact behavioral unilateral cap against an arbitrary stationary
product root.  The second branch is the boundary case in which every fixed
opponent continues surely. -/
def quittingStationaryFullRateUnilateralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  if quittingStationaryFixedOpponentsContinueMass root who < 1 then
    quittingStationaryUnilateralCap reward root who
  else
    max 0 (reward (quittingSingletonTerminal who) who)

@[simp] theorem quittingStationaryFullRateUnilateralCap_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hcontracts :
      quittingStationaryFixedOpponentsContinueMass root who < 1) :
    quittingStationaryFullRateUnilateralCap reward root who =
      quittingStationaryUnilateralCap reward root who := by
  simp [quittingStationaryFullRateUnilateralCap, hcontracts]

@[simp] theorem quittingStationaryFullRateUnilateralCap_of_not_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hcontracts :
      ¬quittingStationaryFixedOpponentsContinueMass root who < 1) :
    quittingStationaryFullRateUnilateralCap reward root who =
      max 0 (reward (quittingSingletonTerminal who) who) := by
  simp [quittingStationaryFullRateUnilateralCap, hcontracts]

@[simp] theorem quittingStationaryFullRateUnilateralCap_of_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hmass : quittingStationaryFixedOpponentsContinueMass root who = 1) :
    quittingStationaryFullRateUnilateralCap reward root who =
      max 0 (reward (quittingSingletonTerminal who) who) := by
  simp [quittingStationaryFullRateUnilateralCap, hmass]

private theorem fixedOpponentsContinueMass_eq_one_of_not_lt
    (root : ι → PMF Bool) (who : ι)
    (hcontracts :
      ¬quittingStationaryFixedOpponentsContinueMass root who < 1) :
    quittingStationaryFixedOpponentsContinueMass root who = 1 := by
  have hle : quittingStationaryFixedOpponentsContinueMass root who ≤ 1 :=
    quittingStationaryContinueMass_le_one
      (Function.update root who (PMF.pure false))
  exact le_antisymm hle (not_lt.mp hcontracts)

/-- Saturated fixed-opponent continuation mass forces every opponent
marginal to be pure Continue. -/
theorem opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
    (root : ι → PMF Bool) (who : ι)
    (hmass : quittingStationaryFixedOpponentsContinueMass root who = 1) :
    ∀ other, other ≠ who → root other = PMF.pure false := by
  intro other hne
  apply pmf_eq_pure_false_of_apply_true_toReal_eq_zero
  exact quittingProbability_eq_zero_of_fixedOpponentsContinueMass_eq_one
    root who other hne hmass

/-- On the saturated face, replacing one player's stationary strategy by an
arbitrary deviation gives the same profile as replacing that player in the
all-Continue profile. -/
theorem update_stationaryProfile_eq_update_alwaysContinue_of_fixedMass_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (hmass : quittingStationaryFixedOpponentsContinueMass root who = 1) :
    Function.update (quittingStationaryProfile reward root) who deviation =
      Function.update (quittingAlwaysContinueProfile reward) who deviation := by
  have hpure :=
    opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
      root who hmass
  funext player time history
  by_cases hp : player = who
  · subst player
    simp
  · simp only [Function.update_of_ne hp]
    rw [show quittingStationaryProfile reward root player =
        (quittingGame reward).stationaryBehaviorProfile root player from rfl]
    rw [show quittingAlwaysContinueProfile reward player =
        (quittingGame reward).stationaryBehaviorProfile
          (fun _ ↦ PMF.pure false) player from rfl]
    unfold StochasticGame.stationaryBehaviorProfile
    rw [hpure player hp]
    rfl

/-- Every behavioral deviation from a stationary product root is bounded by
the full-rate unilateral cap. -/
theorem quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) who deviation)
        who ≤
      quittingStationaryFullRateUnilateralCap reward root who := by
  by_cases hcontracts :
      quittingStationaryFixedOpponentsContinueMass root who < 1
  · rw [quittingStationaryFullRateUnilateralCap_of_lt
      reward root who hcontracts]
    exact quittingTerminalPayoff_update_stationary_le_unilateralCap
      reward root who deviation hcontracts
  · have hmass := fixedOpponentsContinueMass_eq_one_of_not_lt
      root who hcontracts
    rw [quittingStationaryFullRateUnilateralCap_of_not_lt
      reward root who hcontracts]
    rw [update_stationaryProfile_eq_update_alwaysContinue_of_fixedMass_eq_one
      reward root who deviation hmass]
    exact quittingTerminalPayoff_update_quittingAlwaysContinue_le_max
      reward who deviation

/-- The full-rate unilateral cap is attained by a deterministic behavioral
deviation: a pure quit time in the contracting regime, and either Never or
immediate Quit on the saturated face. -/
theorem exists_behaviorStrategy_terminalPayoff_eq_fullRateUnilateralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward
          (Function.update (quittingStationaryProfile reward root) who
            deviation) who =
        quittingStationaryFullRateUnilateralCap reward root who := by
  by_cases hcontracts :
      quittingStationaryFixedOpponentsContinueMass root who < 1
  · obtain ⟨choice, hchoice⟩ :=
      exists_pureTimeBehaviorStrategy_terminalPayoff_eq_unilateralCap
        reward root who hcontracts
    refine ⟨quittingPureTimeBehaviorStrategy reward who choice, ?_⟩
    rw [quittingStationaryFullRateUnilateralCap_of_lt
      reward root who hcontracts]
    exact hchoice
  · have hmass := fixedOpponentsContinueMass_eq_one_of_not_lt
      root who hcontracts
    rw [quittingStationaryFullRateUnilateralCap_of_not_lt
      reward root who hcontracts]
    by_cases hsolo : reward (quittingSingletonTerminal who) who ≤ 0
    · refine ⟨(quittingAlwaysContinueProfile reward) who, ?_⟩
      rw [update_stationaryProfile_eq_update_alwaysContinue_of_fixedMass_eq_one
        reward root who _ hmass]
      rw [Function.update_eq_self,
        quittingTerminalPayoff_quittingAlwaysContinue]
      exact (max_eq_left hsolo).symm
    · refine ⟨quittingAlwaysQuitStrategy reward who, ?_⟩
      rw [update_stationaryProfile_eq_update_alwaysContinue_of_fixedMass_eq_one
        reward root who _ hmass]
      rw [quittingTerminalPayoff_update_quittingAlwaysQuitStrategy]
      exact (max_eq_right (le_of_not_ge hsolo)).symm

/-- Exact pointwise verifier for terminal approximate Nash at any stationary
product root, with no contraction assumption. -/
theorem isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (ε : ℝ) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward root) ↔
      ∀ who,
        quittingStationaryFullRateUnilateralCap reward root who ≤
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who + ε := by
  constructor
  · intro hnash who
    obtain ⟨deviation, hdeviation⟩ :=
      exists_behaviorStrategy_terminalPayoff_eq_fullRateUnilateralCap
        reward root who
    rw [← hdeviation]
    exact hnash who deviation
  · intro hcap who deviation
    exact (quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap
      reward root who deviation).trans (hcap who)

end GameTheory
