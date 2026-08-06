/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSharedPunishmentThreePlayerClassification
import GameTheory.Concepts.Stochastic.QuittingBehaviorStoppingPayoff

/-!
# The Steinhaus--Trybuła shared-punishment table

On the same cyclic three-player set, give player `i` payoff `-1` whenever
`i` quits, and also whenever its successor quits while its predecessor does
not.  All other terminal payoffs are zero.

For this table, quitting at a deterministic finite date can only replace a
continuation payoff in `[-1,0]` by `-1`.  Hence Never is an exact best reply
against every opponent plan.  The best-reply value is therefore the negative
strict stopping-time exposure of successor against predecessor.  This module
proves that identity in the native quitting-game semantics, for arbitrary
history-dependent committed plans.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open QuittingSharedThreePlayer

namespace QuittingSharedThreePlayerDice

/-- The full-exposure cyclic table: own quitting is punished, and otherwise
the same cyclic bad event as in the `3/4` table is punished. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun S who =>
    if who ∈ S.1 ∨ (next who ∈ S.1 ∧ other who ∉ S.1) then -1 else 0

@[simp] theorem reward_nonpos
    (S : {S : Finset Player // S.Nonempty}) (who : Player) :
    reward S who ≤ 0 := by
  unfold reward
  split <;> norm_num

@[simp] theorem neg_one_le_reward
    (S : {S : Finset Player // S.Nonempty}) (who : Player) :
    -1 ≤ reward S who := by
  unfold reward
  split <;> norm_num

@[simp] theorem abs_reward_le_one
    (S : {S : Finset Player // S.Nonempty}) (who : Player) :
    |reward S who| ≤ 1 := by
  unfold reward
  split <;> norm_num

/-- Pointwise root payoff formula for the full-exposure table. -/
theorem quittingRootPayoff_eq_exposureEvent
    (action : Player → Bool) (who : Player) :
    quittingRootPayoff reward (0 : Payoff Player) action who =
      if action who = true ∨
          (action (next who) = true ∧ action (other who) = false)
        then -1 else 0 := by
  by_cases hevent : action who = true ∨
      (action (next who) = true ∧ action (other who) = false)
  · rw [if_pos hevent]
    have hquit : (quittingQuitters action).Nonempty := by
      rcases hevent with hself | hbad
      · exact ⟨who, by simpa [quittingQuitters] using hself⟩
      · exact ⟨next who, by simpa [quittingQuitters] using hbad.1⟩
    unfold quittingRootPayoff
    rw [dif_pos hquit]
    unfold reward
    rw [if_pos]
    rcases hevent with hself | hbad
    · exact Or.inl (by simpa [quittingQuitters] using hself)
    · exact Or.inr ⟨by simpa [quittingQuitters] using hbad.1,
        by simpa [quittingQuitters] using hbad.2⟩
  · rw [if_neg hevent]
    by_cases hquit : (quittingQuitters action).Nonempty
    · unfold quittingRootPayoff
      rw [dif_pos hquit]
      unfold reward
      rw [if_neg]
      intro hreward
      apply hevent
      rcases hreward with hself | hbad
      · exact Or.inl (by simpa [quittingQuitters] using hself)
      · exact Or.inr ⟨by simpa [quittingQuitters] using hbad.1,
          by simpa [quittingQuitters] using hbad.2⟩
    · unfold quittingRootPayoff
      rw [dif_neg hquit]
      simp

private theorem expect_pmfPi_update_pure_congr
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (root : ι → PMF Bool) (who : ι) (fixed : Bool)
    (first second : (ι → Bool) → ℝ)
    (hagree : ∀ action, action who = fixed → first action = second action) :
    expect (pmfPi (Function.update root who (PMF.pure fixed))) first =
      expect (pmfPi (Function.update root who (PMF.pure fixed))) second := by
  rw [expect_eq_sum, expect_eq_sum]
  apply Finset.sum_congr rfl
  intro action _
  by_cases haction : action who = fixed
  · rw [hagree action haction]
  · have hmass :
        (pmfPi (Function.update root who (PMF.pure fixed)) action).toReal = 0 := by
      rw [pmfPi_apply_update_family]
      simp [PMF.pure_apply, haction]
    rw [hmass]
    simp only [zero_mul]

/-- The pure-Quit branch is identically `-1`, independently of the opponents. -/
theorem quittingStationaryFixedOpponentsQuitValue_eq_neg_one
    (root : Player → PMF Bool) (who : Player) :
    quittingStationaryFixedOpponentsQuitValue reward root who = -1 := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue
    quittingRootAbsorbingContribution quittingRootExpectedPayoff
  calc
    expect (pmfPi (Function.update root who (PMF.pure true)))
        (fun action => quittingRootPayoff reward (0 : Payoff Player) action who) =
      expect (pmfPi (Function.update root who (PMF.pure true)))
        (fun _ => (-1 : ℝ)) := by
          apply expect_pmfPi_update_pure_congr root who true
          intro action haction
          rw [quittingRootPayoff_eq_exposureEvent, if_pos (Or.inl haction)]
    _ = -1 := expect_const _ _

@[simp] theorem quittingFixedOpponentsQuitValue_eq_neg_one
    (roots : ℕ → Player → PMF Bool) (who : Player) (time : ℕ) :
    quittingFixedOpponentsQuitValue reward roots who time = -1 := by
  rw [← quittingStationaryFixedOpponentsQuitValue_apply reward roots who time]
  exact quittingStationaryFixedOpponentsQuitValue_eq_neg_one (roots time) who

/-- If the player continues, the one-stage reward is the negative cyclic bad
probability. -/
theorem quittingStationaryFixedOpponentsContinueReward_eq
    (root : Player → PMF Bool) (who : Player) :
    quittingStationaryFixedOpponentsContinueReward reward root who =
      -(root (next who) true).toReal *
        (root (other who) false).toReal := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward
    quittingRootAbsorbingContribution quittingRootExpectedPayoff
  calc
    expect (pmfPi (Function.update root who (PMF.pure false)))
        (fun action => quittingRootPayoff reward (0 : Payoff Player) action who) =
      expect (pmfPi (Function.update root who (PMF.pure false)))
        (fun action =>
          if action (next who) = true ∧ action (other who) = false
            then (-1 : ℝ) else 0) := by
          apply expect_pmfPi_update_pure_congr root who false
          intro action haction
          rw [quittingRootPayoff_eq_exposureEvent]
          simp [haction]
    _ = -(root (next who) true).toReal *
        (root (other who) false).toReal := by
          rw [QuittingSharedThreePlayer.expect_pmfPi_badEvent _
            (next_ne_other who)]
          simp [next_ne_self who, other_ne_self who]

@[simp] theorem quittingFixedOpponentsContinueReward_eq
    (roots : ℕ → Player → PMF Bool) (who : Player) (time : ℕ) :
    quittingFixedOpponentsContinueReward reward roots who time =
      -(roots time (next who) true).toReal *
        (roots time (other who) false).toReal := by
  rw [← quittingStationaryFixedOpponentsContinueReward_apply
    reward roots who time]
  exact quittingStationaryFixedOpponentsContinueReward_eq (roots time) who

/-- The opponent-survival coefficient is unchanged from the first cyclic
table. -/
theorem quittingStationaryFixedOpponentsContinueMass_eq
    (root : Player → PMF Bool) (who : Player) :
    quittingStationaryFixedOpponentsContinueMass root who =
      (root (next who) false).toReal *
        (root (other who) false).toReal :=
  QuittingSharedThreePlayer.quittingStationaryFixedOpponentsContinueMass_eq
    root who

@[simp] theorem quittingFixedOpponentsContinueMass_eq
    (roots : ℕ → Player → PMF Bool) (who : Player) (time : ℕ) :
    quittingFixedOpponentsContinueMass roots who time =
      (roots time (next who) false).toReal *
        (roots time (other who) false).toReal := by
  rw [← quittingStationaryFixedOpponentsContinueMass_apply roots who time]
  exact quittingStationaryFixedOpponentsContinueMass_eq (roots time) who

/-! ## Individual punishment floors -/

/-- Every individual punishment floor is `-1`. -/
theorem quittingPunishmentValue_eq_neg_one (who : Player) :
    quittingPunishmentValue reward who = -1 := by
  apply le_antisymm
  · have h := quittingPunishmentValue_le_stationaryUnilateralCap
      reward who (QuittingSureSetOwnerRepair.quittingPureSetRoot
        ({next who} : Finset Player))
    rw [quittingStationaryUnilateralCap_pureSetRoot] at h
    cases who <;> simpa [reward, next, other] using h
  · rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
    haveI : Nonempty (Player → PMF Bool) :=
      ⟨fun _ => PMF.pure false⟩
    exact le_ciInf fun root =>
      le_quittingStationaryUnilateralCap_of_forall_le reward who
        (by norm_num) (fun S => neg_one_le_reward S who) root

/-! ## Never is the exact best reply -/

private theorem neg_one_le_quittingRootSequencePureTimeTerminalValue
    (roots : ℕ → Player → PMF Bool) (who : Player)
    (choice : Option ℕ) (start : ℕ) :
    -1 ≤ quittingRootSequencePureTimeTerminalValue reward roots who
      choice start := by
  apply neg_le_of_abs_le
  simpa [quittingRootSequencePureTimeTerminalValue,
    quittingRootSequenceHazardTerminalValue,
    quittingRootSequenceTerminalValue] using
    (abs_quittingTerminalPayoff_le reward
      (quittingRootSequenceProfile reward
        (quittingRootSequenceUpdate roots who
          (quittingPureTimeHazard choice)) start)
      who (by norm_num) (fun S player => abs_reward_le_one S player))

/-- Quitting at any finite deterministic date is weakly worse than Never. -/
theorem quittingRootSequencePureTimeTerminalValue_some_le_none
    (roots : ℕ → Player → PMF Bool) (who : Player) :
    ∀ (start fuel : ℕ),
      quittingRootSequencePureTimeTerminalValue reward roots who
          (some (start + fuel)) start ≤
        quittingRootSequencePureTimeTerminalValue reward roots who none start := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      rw [quittingRootSequencePureTimeTerminalValue_some_add]
      simpa only [quittingLiveLedgerAccum_zero, add_zero,
        quittingOpponentSurvivalWeight, Finset.range_zero, Finset.prod_empty,
        quittingFixedOpponentsQuitValue_eq_neg_one, mul_neg, mul_one,
        zero_add] using
          (neg_one_le_quittingRootSequencePureTimeTerminalValue
            roots who none start)
  | succ fuel ih =>
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
      conv_rhs =>
        rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
      have hne : start ≠ start + (fuel + 1) := by omega
      rw [quittingPureTimeHazard_some_of_ne hne,
        quittingPureTimeHazard_none]
      simp only [PMF.pure_apply,
        if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
        if_true, ENNReal.toReal_one, zero_mul, one_mul, zero_add]
      have htime : start + (fuel + 1) = start + 1 + fuel := by omega
      rw [htime]
      change
        quittingFixedOpponentsContinueReward reward roots who start +
            quittingFixedOpponentsContinueMass roots who start *
              quittingRootSequencePureTimeTerminalValue reward roots who
                (some (start + 1 + fuel)) (start + 1) ≤
          quittingFixedOpponentsContinueReward reward roots who start +
            quittingFixedOpponentsContinueMass roots who start *
              quittingRootSequencePureTimeTerminalValue reward roots who
                none (start + 1)
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (ih (start + 1))
          (quittingFixedOpponentsContinueMass_nonneg roots who start))

/-- **Full stopping-exposure identity.**  Against every committed opponent
plan, Never is an exact best reply. -/
theorem quittingBestReplyValue_eq_alwaysContinue
    (profile : (quittingGame reward).BehaviorProfile) (who : Player) :
    quittingBestReplyValue reward profile who =
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingAlwaysContinueStrategy reward who)) who := by
  apply le_antisymm
  · apply quittingBestReplyValue_le
    intro strategy
    rw [quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
      reward profile who strategy (by norm_num)
      (fun S player => abs_reward_le_one S player)]
    calc
      expect (quittingBehaviorStoppingLaw reward strategy)
          (fun choice =>
            quittingTerminalPayoff reward
              (Function.update profile who
                (quittingPureTimeBehaviorStrategy reward who choice)) who) ≤
        expect (quittingBehaviorStoppingLaw reward strategy)
          (fun _ =>
            quittingTerminalPayoff reward
              (Function.update profile who
                (quittingAlwaysContinueStrategy reward who)) who) := by
          apply Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
          · intro choice
            cases choice with
            | none => rfl
            | some time =>
                rw [show quittingAlwaysContinueStrategy reward who =
                    quittingPureTimeBehaviorStrategy reward who none by rfl,
                  quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
                simpa using
                  (quittingRootSequencePureTimeTerminalValue_some_le_none
                    (quittingProfileLiveRoot reward profile) who 0 time)
          · intro choice
            exact abs_quittingTerminalPayoff_le reward
              (Function.update profile who
                (quittingPureTimeBehaviorStrategy reward who choice)) who
              (by norm_num) (fun S player => abs_reward_le_one S player)
          · intro _
            exact abs_quittingTerminalPayoff_le reward
              (Function.update profile who
                (quittingAlwaysContinueStrategy reward who)) who
              (by norm_num) (fun S player => abs_reward_le_one S player)
      _ = quittingTerminalPayoff reward
          (Function.update profile who
            (quittingAlwaysContinueStrategy reward who)) who :=
        expect_const _ _
  · exact le_quittingBestReplyValue reward profile who
      (quittingAlwaysContinueStrategy reward who)

end QuittingSharedThreePlayerDice

end GameTheory
