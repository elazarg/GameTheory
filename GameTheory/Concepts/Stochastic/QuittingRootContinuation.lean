/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingAsymptotic

/-!
# Root continuation identities for quitting games

The all-continue outcome of a quitting-game root action does not have terminal
value zero merely because a proposed on-path absorption description ends
there.  It starts the continuation profile.  This module records the exact
profile-level root decomposition of expected terminal payoff.

Only this finite first-stage identity and its immediate bounds are proved
here.  No absorption-path/proper-path equivalence is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The quitter set selected by a Boolean joint action. -/
def quittingQuitters (action : ι → Bool) : Finset ι :=
  {who | action who = true}

omit [DecidableEq ι] in
@[simp] theorem quittingGame_transition_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (action : ι → Bool) :
    (quittingGame reward).transition none action =
      if h : ({who | action who = true} : Finset ι).Nonempty then
        PMF.pure (show (quittingGame reward).State from
          some ⟨({who | action who = true} : Finset ι), h⟩)
      else PMF.pure (show (quittingGame reward).State from none) :=
  rfl

omit [DecidableEq ι] in
@[simp] theorem quittingQuitters_nonempty_iff (action : ι → Bool) :
    (quittingQuitters action).Nonempty ↔ ∃ who, action who = true := by
  constructor
  · rintro ⟨who, hwho⟩
    exact ⟨who, by simpa [quittingQuitters] using hwho⟩
  · rintro ⟨who, hwho⟩
    exact ⟨who, by simp [quittingQuitters, hwho]⟩

/-- The value after one root action: a nonempty quitter set receives its
terminal reward, while all-continue starts the actual shifted continuation
profile. -/
def quittingRootContinuationPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (action : (quittingGame reward).JointAct) (who : ι) : ℝ :=
  if h : (quittingQuitters action).Nonempty then
    reward ⟨quittingQuitters action, h⟩ who
  else
    quittingTerminalPayoff reward
      ((quittingGame reward).shiftProfile profile (none, action)) who

omit [DecidableEq ι] in
theorem quittingRootContinuationPayoff_of_quitters
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (action : (quittingGame reward).JointAct) (who : ι)
    (h : (quittingQuitters action).Nonempty) :
    quittingRootContinuationPayoff reward profile action who =
      reward ⟨quittingQuitters action, h⟩ who := by
  simp [quittingRootContinuationPayoff, h]

omit [DecidableEq ι] in
theorem quittingRootContinuationPayoff_of_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (action : (quittingGame reward).JointAct) (who : ι)
    (h : ¬(quittingQuitters action).Nonempty) :
    quittingRootContinuationPayoff reward profile action who =
      quittingTerminalPayoff reward
        ((quittingGame reward).shiftProfile profile (none, action)) who := by
  simp [quittingRootContinuationPayoff, h]

omit [DecidableEq ι] in
/-- From an already absorbed state, every behavior profile receives the
terminal reward at every stage. -/
theorem expectedStagePayoff_quittingGame_some
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (S : {S : Finset ι // S.Nonempty}) (t : ℕ) (who : ι) :
    (quittingGame reward).expectedStagePayoff profile (some S) t who =
      reward S who := by
  unfold StochasticGame.expectedStagePayoff
  calc
    expect ((quittingGame reward).histDist profile (some S) t)
        (fun h => (quittingGame reward).stageEUAt profile h who) =
        expect ((quittingGame reward).histDist profile (some S) t)
          (fun _ => reward S who) := by
      apply Math.ProbabilityMassFunction.expect_congr_on_support
      intro h hh
      have hs :=
        (quittingGame reward).snd_eq_of_mem_support_histDist_of_isAbsorbingState
          (isAbsorbingState_quittingGame_some reward S) profile t h hh
      rw [stageEUAt_quittingGame_eq_stateReward, hs]
      rfl
    _ = reward S who := expect_const _ _

omit [DecidableEq ι] in
/-- First-stage disintegration of the expected stage payoff at every positive
time.  This is the finite-time precursor of the terminal root equation. -/
theorem expectedStagePayoff_succ_quittingGame_eq_rootContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (t : ℕ) (who : ι) :
    (quittingGame reward).expectedStagePayoff profile none (t + 1) who =
      expect ((quittingGame reward).stageActionDist profile
          ((quittingGame reward).emptyHist none)) fun action =>
        if h : (quittingQuitters action).Nonempty then
          reward ⟨quittingQuitters action, h⟩ who
        else
          (quittingGame reward).expectedStagePayoff
            ((quittingGame reward).shiftProfile profile (none, action))
            none t who := by
  classical
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ i : ι, Finite ((quittingGame reward).Act i) :=
    fun _ => inferInstanceAs (Finite Bool)
  unfold StochasticGame.expectedStagePayoff
  rw [(quittingGame reward).histDist_succ_shift, expect_bind]
  apply congrArg (expect
    ((quittingGame reward).stageActionDist profile
      ((quittingGame reward).emptyHist none)))
  funext action
  change ι → Bool at action
  rw [expect_bind]
  by_cases hquit : ({i | action i = true} : Finset ι).Nonempty
  · rw [quittingGame_transition_none, dif_pos hquit]
    rw [expect_pure, expect_map]
    simp only [quittingQuitters, dif_pos hquit]
    have habs := expectedStagePayoff_quittingGame_some reward
      ((quittingGame reward).shiftProfile profile (none, action))
      ⟨({i | action i = true} : Finset ι), hquit⟩ t who
    unfold StochasticGame.expectedStagePayoff at habs
    rw [← habs]
    apply Math.ProbabilityMassFunction.expect_congr_on_support
    intro h hh
    simp only [stageEUAt_quittingGame_eq_stateReward,
      (quittingGame reward).consHist_snd]
  · rw [quittingGame_transition_none, dif_neg hquit]
    rw [expect_pure, expect_map]
    rw [show (fun h =>
          (quittingGame reward).stageEUAt profile
            ((quittingGame reward).consHist (none, action) h) who) =
        (fun h =>
          (quittingGame reward).stageEUAt
            ((quittingGame reward).shiftProfile profile (none, action))
            h who) by
      funext h
      simp only [stageEUAt_quittingGame_eq_stateReward,
        (quittingGame reward).consHist_snd]]
    simp [quittingQuitters, hquit]

/-- **Correct terminal root equation.**  Expected terminal payoff equals the
root expectation of terminal reward on quitting actions and of the actual
shifted continuation payoff on the all-continue action. -/
theorem quittingTerminalPayoff_eq_expect_rootContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward profile who =
      expect ((quittingGame reward).stageActionDist profile
          ((quittingGame reward).emptyHist none))
        (fun action =>
          quittingRootContinuationPayoff reward profile action who) := by
  letI : ∀ i : ι, Fintype ((quittingGame reward).Act i) :=
    fun _ => inferInstanceAs (Fintype Bool)
  let rootLaw :=
    (quittingGame reward).stageActionDist profile
      ((quittingGame reward).emptyHist none)
  have hleft : Tendsto (fun t =>
      (quittingGame reward).expectedStagePayoff profile none (t + 1) who)
      atTop (nhds (quittingTerminalPayoff reward profile who)) :=
    (tendsto_expectedStagePayoff_quittingGame reward profile who).comp
      (tendsto_add_atTop_nat 1)
  have hright : Tendsto (fun t =>
      expect rootLaw fun action =>
        if h : (quittingQuitters action).Nonempty then
          reward ⟨quittingQuitters action, h⟩ who
        else
          (quittingGame reward).expectedStagePayoff
            ((quittingGame reward).shiftProfile profile (none, action))
            none t who) atTop
      (nhds (expect rootLaw fun action =>
        quittingRootContinuationPayoff reward profile action who)) := by
    classical
    rw [show (fun t => expect rootLaw fun action =>
        if h : (quittingQuitters action).Nonempty then
          reward ⟨quittingQuitters action, h⟩ who
        else
          (quittingGame reward).expectedStagePayoff
            ((quittingGame reward).shiftProfile profile (none, action))
            none t who) =
        fun t => ∑ action,
          (rootLaw action).toReal *
            (if h : (quittingQuitters action).Nonempty then
              reward ⟨quittingQuitters action, h⟩ who
            else
              (quittingGame reward).expectedStagePayoff
                ((quittingGame reward).shiftProfile profile (none, action))
                none t who) by
      funext t
      rw [expect_eq_sum]]
    rw [show expect rootLaw (fun action =>
        quittingRootContinuationPayoff reward profile action who) =
        ∑ action, (rootLaw action).toReal *
          quittingRootContinuationPayoff reward profile action who by
      rw [expect_eq_sum]]
    apply tendsto_finsetSum Finset.univ
    intro action ha
    by_cases hquit : (quittingQuitters action).Nonempty
    · simp [hquit, quittingRootContinuationPayoff]
    · simpa [hquit, quittingRootContinuationPayoff] using
        (tendsto_expectedStagePayoff_quittingGame reward
          ((quittingGame reward).shiftProfile profile (none, action)) who).const_mul
          (rootLaw action).toReal
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  exact Filter.Eventually.of_forall fun t =>
    (expectedStagePayoff_succ_quittingGame_eq_rootContinuation
      reward profile t who).symm

end GameTheory
