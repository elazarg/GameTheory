/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingBehaviorPureTimeExtremality
import GameTheory.Concepts.Stochastic.QuittingStationarySnellCap

/-!
# Behavioral best responses to stationary quitting profiles

The selected stationary Snell cap includes every finite quit time and the
explicit `Never` alternative.  This file connects that scalar calculation to
the behavior-profile API: arbitrary history-dependent deviations cannot beat
the selected cap.  Consequently pointwise cap inequalities suffice for a
terminal approximate Nash certificate.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
@[simp] theorem quittingProfileLiveRoot_stationary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) :
    quittingProfileLiveRoot reward (quittingStationaryProfile reward root) =
      fun _ => root := by
  funext time who
  rfl

theorem quittingRootSequencePureTimeTerminalValue_const_some
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    ∀ start steps,
      quittingRootSequencePureTimeTerminalValue reward (fun _ => root) who
          (some (start + steps)) start =
        quittingStationaryPureTimeValue
          (quittingStationaryFixedOpponentsQuitValue reward root who)
          (quittingStationaryFixedOpponentsContinueReward reward root who)
          (quittingStationaryFixedOpponentsContinueMass root who) steps := by
  intro start steps
  induction steps generalizing start with
  | zero =>
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
      simp [quittingStationaryPureTimeValue]
      rfl
  | succ steps ih =>
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
      have hne : start ≠ start + (steps + 1) := by omega
      rw [quittingPureTimeHazard_some_of_ne hne]
      simp only [PMF.pure_apply,
        if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
        if_true, ENNReal.toReal_one, zero_mul, one_mul, zero_add]
      have htime : start + (steps + 1) = (start + 1) + steps := by omega
      change
        quittingStationaryFixedOpponentsContinueReward reward root who +
            quittingStationaryFixedOpponentsContinueMass root who *
              quittingRootSequencePureTimeTerminalValue reward
                (fun _ => root) who (some (start + (steps + 1)))
                  (start + 1) = _
      rw [htime, ih (start + 1)]
      rfl

theorem quittingRootSequencePureTimeTerminalValue_const_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hcontracts :
      quittingStationaryFixedOpponentsContinueMass root who < 1)
    (start : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward (fun _ => root) who
        none start =
      quittingStationaryNeverValue
        (quittingStationaryFixedOpponentsContinueReward reward root who)
        (quittingStationaryFixedOpponentsContinueMass root who) := by
  change quittingTerminalPayoff reward
      (quittingStationaryProfile reward
        (Function.update root who (PMF.pure false))) who = _
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
  · rfl
  · exact hcontracts

theorem quittingRootSequencePureTimeTerminalValue_const
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hcontracts :
      quittingStationaryFixedOpponentsContinueMass root who < 1)
    (choice : Option ℕ) :
    quittingRootSequencePureTimeTerminalValue reward (fun _ => root) who
        choice 0 =
      quittingStationaryDeterministicValue
        (quittingStationaryFixedOpponentsQuitValue reward root who)
        (quittingStationaryFixedOpponentsContinueReward reward root who)
        (quittingStationaryFixedOpponentsContinueMass root who) choice := by
  cases choice with
  | none =>
      exact quittingRootSequencePureTimeTerminalValue_const_none
        reward root who hcontracts 0
  | some steps =>
      simpa [quittingStationaryDeterministicValue] using
        quittingRootSequencePureTimeTerminalValue_const_some
          reward root who 0 steps

theorem quittingTerminalPayoff_update_pureTime_stationary_le_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hcontracts :
      quittingStationaryFixedOpponentsContinueMass root who < 1)
    (choice : Option ℕ) :
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) who
          (quittingPureTimeBehaviorStrategy reward who choice)) who ≤
      quittingStationaryUnilateralCap reward root who := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingProfileLiveRoot_stationary,
    quittingRootSequencePureTimeTerminalValue_const reward root who
      hcontracts choice]
  exact (quittingStationarySelectedCap_isLUB _ _ _
    (quittingStationaryFixedOpponentsContinueMass_nonneg root who)
    hcontracts).1 ⟨choice, rfl⟩

theorem quittingTerminalPayoff_update_stationary_le_unilateralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (hcontracts :
      quittingStationaryFixedOpponentsContinueMass root who < 1) :
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) who
          deviation) who ≤
      quittingStationaryUnilateralCap reward root who := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨choice, hchoice⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward (quittingStationaryProfile reward root) who deviation hε
  exact hchoice.trans (by
    simpa [add_comm] using add_le_add_right
      (quittingTerminalPayoff_update_pureTime_stationary_le_cap
        reward root who hcontracts choice) ε)

/-- Pointwise selected-cap bounds are sufficient for terminal approximate
Nash of a playerwise-contracting stationary profile. -/
theorem isεAsymptoticNash_stationary_of_unilateralCap_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (ε : ℝ)
    (hcontracts : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who < 1)
    (hcap : ∀ who,
      quittingStationaryUnilateralCap reward root who ≤
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who + ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingStationaryProfile reward root) := by
  intro who deviation
  exact (quittingTerminalPayoff_update_stationary_le_unilateralCap
    reward root who deviation (hcontracts who)).trans (hcap who)

/-- Under strict opponent contraction, the stationary unilateral cap is
attained by an actual deterministic-time behavior deviation: either Quit
immediately or Never quit. -/
theorem exists_pureTimeBehaviorStrategy_terminalPayoff_eq_unilateralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hcontracts :
      quittingStationaryFixedOpponentsContinueMass root who < 1) :
    ∃ choice : Option ℕ,
      quittingTerminalPayoff reward
          (Function.update (quittingStationaryProfile reward root) who
            (quittingPureTimeBehaviorStrategy reward who choice)) who =
        quittingStationaryUnilateralCap reward root who := by
  let quitValue :=
    quittingStationaryFixedOpponentsQuitValue reward root who
  let continueReward :=
    quittingStationaryFixedOpponentsContinueReward reward root who
  let continueMass :=
    quittingStationaryFixedOpponentsContinueMass root who
  by_cases hnever : quitValue ≤
      quittingStationaryNeverValue continueReward continueMass
  · refine ⟨none, ?_⟩
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingProfileLiveRoot_stationary,
      quittingRootSequencePureTimeTerminalValue_const
        reward root who hcontracts]
    change quittingStationaryNeverValue continueReward continueMass =
      quittingStationarySelectedCap quitValue continueReward continueMass
    exact (max_eq_right hnever).symm
  · refine ⟨some 0, ?_⟩
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingProfileLiveRoot_stationary,
      quittingRootSequencePureTimeTerminalValue_const
        reward root who hcontracts]
    change quittingStationaryPureTimeValue
        quitValue continueReward continueMass 0 =
      quittingStationarySelectedCap quitValue continueReward continueMass
    rw [quittingStationaryPureTimeValue]
    exact (max_eq_left (le_of_not_ge hnever)).symm

/-- For a playerwise-contracting stationary root, the pointwise cap
criterion is also necessary for terminal approximate Nash. -/
theorem isεAsymptoticNash_stationary_iff_unilateralCap_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (ε : ℝ)
    (hcontracts : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who < 1) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward root) ↔
      ∀ who,
        quittingStationaryUnilateralCap reward root who ≤
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who + ε := by
  constructor
  · intro hnash who
    obtain ⟨choice, hchoice⟩ :=
      exists_pureTimeBehaviorStrategy_terminalPayoff_eq_unilateralCap
        reward root who (hcontracts who)
    calc
      quittingStationaryUnilateralCap reward root who =
          quittingTerminalPayoff reward
            (Function.update (quittingStationaryProfile reward root) who
              (quittingPureTimeBehaviorStrategy reward who choice)) who :=
        hchoice.symm
      _ ≤ quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who + ε :=
        hnash who (quittingPureTimeBehaviorStrategy reward who choice)
  · exact isεAsymptoticNash_stationary_of_unilateralCap_le
      reward root ε hcontracts

end GameTheory
