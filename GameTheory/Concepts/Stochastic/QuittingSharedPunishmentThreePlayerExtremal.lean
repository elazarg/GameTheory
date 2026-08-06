/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSharedPunishmentThreePlayerExact

/-!
# Extremal shared plans for the cyclic three-player table

The exact value `3/4` is decided at the first live row.  If that row is fair,
then every player's immediate Quit value is `-1/4`, and every Continue branch
has immediate contribution `-1/4` plus a nonpositive tail.  Thus the tail is
irrelevant: every designated best-reply value is exactly `-1/4`.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

namespace QuittingSharedThreePlayer

/-! ## Nonpositive tails -/

/-- Every finite-time absorbed-state mass is nonnegative. -/
theorem quittingAbsorbedMass_nonneg
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (S : {S : Finset Player // S.Nonempty}) :
    0 ≤ quittingAbsorbedMass reward profile time S := by
  unfold quittingAbsorbedMass StochasticGame.expectedStateValue
  apply expect_nonneg
  intro history
  by_cases hs : history.2 = some S <;>
    simp [quittingAbsorbedIndicator, hs]

/-- Every limiting absorbed-state mass is nonnegative. -/
theorem quittingAbsorbedMassLimit_nonneg
    (profile : (quittingGame reward).BehaviorProfile)
    (S : {S : Finset Player // S.Nonempty}) :
    0 ≤ quittingAbsorbedMassLimit reward profile S := by
  unfold quittingAbsorbedMassLimit
  have hbdd : BddAbove
      (Set.range fun time => quittingAbsorbedMass reward profile time S) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨time, rfl⟩
    exact quittingAbsorbedMass_le_one reward profile time S
  exact (quittingAbsorbedMass_nonneg profile 0 S).trans
    (le_ciSup hbdd 0)

/-- Every terminal payoff in the cyclic table is nonpositive. -/
theorem quittingTerminalPayoff_nonpos
    (profile : (quittingGame reward).BehaviorProfile) (who : Player) :
    quittingTerminalPayoff reward profile who ≤ 0 := by
  unfold quittingTerminalPayoff
  apply Finset.sum_nonpos
  intro S _
  exact mul_nonpos_of_nonneg_of_nonpos
    (quittingAbsorbedMassLimit_nonneg profile S) (reward_nonpos S who)

/-- Consequently every root-sequence hazard tail is nonpositive. -/
theorem quittingRootSequenceHazardTerminalValue_nonpos
    (roots : ℕ → Player → PMF Bool) (who : Player)
    (hazard : ℕ → PMF Bool) (start : ℕ) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard start ≤ 0 := by
  simpa [quittingRootSequenceHazardTerminalValue,
    quittingRootSequenceTerminalValue] using
    (quittingTerminalPayoff_nonpos
      (quittingRootSequenceProfile reward
        (quittingRootSequenceUpdate roots who hazard) start) who)

/-! ## A fair first row makes the tail irrelevant -/

/-- Against roots whose first row is fair, every hazard has value at most
`-1/4`, regardless of all later rows. -/
theorem quittingRootSequenceHazardTerminalValue_le_neg_quarter_of_first_eq_fair
    (roots : ℕ → Player → PMF Bool) (who : Player)
    (hazard : ℕ → PMF Bool) (hfair : roots 0 = fairRoot) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 ≤
      (-1 / 4 : ℝ) := by
  have hquit : quittingFixedOpponentsQuitValue reward roots who 0 =
      (-1 / 4 : ℝ) := by
    rw [← quittingStationaryFixedOpponentsQuitValue_apply
      reward roots who 0, hfair, fairRoot_quitValue]
  have hcontinue : quittingFixedOpponentsContinueReward reward roots who 0 =
      (-1 / 4 : ℝ) := by
    rw [← quittingStationaryFixedOpponentsContinueReward_apply
      reward roots who 0, hfair, fairRoot_continueReward]
  have hmass : quittingFixedOpponentsContinueMass roots who 0 =
      (1 / 4 : ℝ) := by
    rw [← quittingStationaryFixedOpponentsContinueMass_apply
      roots who 0, hfair, fairRoot_continueMass]
  have htail :=
    quittingRootSequenceHazardTerminalValue_nonpos roots who hazard 1
  have hsum :
      (hazard 0 true).toReal + (hazard 0 false).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using
      (pmf_toReal_sum_one (hazard 0))
  have hweightedTail :
      (hazard 0 false).toReal *
          quittingRootSequenceHazardTerminalValue reward roots who hazard 1 ≤
        0 :=
    mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg htail
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
    hquit, hcontinue, hmass]
  nlinarith

/-- A fair first live row caps every behavioral deviation at `-1/4`. -/
theorem quittingBestReplyValue_le_neg_quarter_of_first_eq_fair
    (profile : (quittingGame reward).BehaviorProfile) (who : Player)
    (hfair : quittingProfileLiveRoot reward profile 0 = fairRoot) :
    quittingBestReplyValue reward profile who ≤ (-1 / 4 : ℝ) := by
  apply quittingBestReplyValue_le
  intro deviation
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue]
  exact
    quittingRootSequenceHazardTerminalValue_le_neg_quarter_of_first_eq_fair
      (quittingProfileLiveRoot reward profile) who
      (quittingBehaviorLiveHazard reward deviation) hfair

/-- Quitting immediately attains `-1/4`, so the best-reply value is exact. -/
theorem quittingBestReplyValue_eq_neg_quarter_of_first_eq_fair
    (profile : (quittingGame reward).BehaviorProfile) (who : Player)
    (hfair : quittingProfileLiveRoot reward profile 0 = fairRoot) :
    quittingBestReplyValue reward profile who = (-1 / 4 : ℝ) := by
  apply le_antisymm
  · exact quittingBestReplyValue_le_neg_quarter_of_first_eq_fair
      profile who hfair
  · have hreply := le_quittingBestReplyValue reward profile who
      (quittingPureTimeBehaviorStrategy reward who (some 0))
    have hquit :
        quittingFixedOpponentsQuitValue reward
            (quittingProfileLiveRoot reward profile) who 0 =
          (-1 / 4 : ℝ) := by
      rw [← quittingStationaryFixedOpponentsQuitValue_apply reward
        (quittingProfileLiveRoot reward profile) who 0,
        hfair, fairRoot_quitValue]
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingRootSequencePureTimeTerminalValue_some_eq] at hreply
    simpa [quittingLiveLedgerAccum, quittingOpponentSurvivalWeight,
      hquit] using hreply

/-- **Tail irrelevance.**  Every behavior plan with a fair first live row is
an exact shared minimizer: its worst excess is `3/4`, independently of its
continuation after all players continue. -/
theorem quittingSharedPunishmentGap_eq_three_quarters_of_first_eq_fair
    (profile : (quittingGame reward).BehaviorProfile)
    (hfair : quittingProfileLiveRoot reward profile 0 = fairRoot) :
    quittingSharedPunishmentGap profile = (3 / 4 : ℝ) := by
  unfold quittingSharedPunishmentGap
  rw [quittingBestReplyValue_eq_neg_quarter_of_first_eq_fair
      profile Player.a hfair,
    quittingBestReplyValue_eq_neg_quarter_of_first_eq_fair
      profile Player.b hfair,
    quittingBestReplyValue_eq_neg_quarter_of_first_eq_fair
      profile Player.c hfair]
  simp [quittingPunishmentValue_eq_neg_one]
  norm_num

end QuittingSharedThreePlayer

end GameTheory
