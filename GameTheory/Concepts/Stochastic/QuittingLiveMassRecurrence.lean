/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingLiveMass

/-!
# The stopping recurrence for live mass in a quitting game

This file turns the canonical live history into a quantitative stopping
coordinate.  Live mass is the expectation of the live-state indicator, and
one more stage multiplies it by the conditional probability of the unique
all-continue joint action at the live history.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Indicator of the unique live state of a quitting game. -/
def quittingLiveIndicator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingGame reward).State → ℝ
  | none => 1
  | some _ => 0

omit [DecidableEq ι] in
@[simp] theorem quittingLiveIndicator_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingLiveIndicator reward none = 1 :=
  rfl

omit [DecidableEq ι] in
@[simp] theorem quittingLiveIndicator_some
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : {S : Finset ι // S.Nonempty}) :
    quittingLiveIndicator reward (some S) = 0 :=
  rfl

/-- The conditional probability, at the canonical live history, that all
players continue for one more stage. -/
def quittingJointContinueMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (time : ℕ) : ℝ :=
  (((quittingGame reward).stageActionDist profile
      (quittingLiveHist reward time))
    (quittingAllContinueAction : ι → Bool)).toReal

omit [DecidableEq ι] in
theorem quittingJointContinueMass_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    0 ≤ quittingJointContinueMass reward profile time :=
  ENNReal.toReal_nonneg

omit [DecidableEq ι] in
theorem quittingJointContinueMass_le_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingJointContinueMass reward profile time ≤ 1 := by
  unfold quittingJointContinueMass
  rw [← ENNReal.toReal_one,
    ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by simp)]
  exact PMF.coe_le_one _ _

/-- The live-history coordinate is exactly the expected indicator of the
current state being live. -/
theorem quittingLiveMass_eq_expectedStateValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward profile time =
      (quittingGame reward).expectedStateValue profile none time
        (quittingLiveIndicator reward) := by
  classical
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ who : ι, Finite ((quittingGame reward).Act who) :=
    fun _ => inferInstanceAs (Finite Bool)
  letI : Fintype ((quittingGame reward).Hist time) :=
    Fintype.ofFinite _
  unfold quittingLiveMass StochasticGame.expectedStateValue
  rw [expect_eq_sum]
  symm
  calc
    ∑ history,
        (((quittingGame reward).histDist profile none time) history).toReal *
          quittingLiveIndicator reward history.2 =
        (((quittingGame reward).histDist profile none time)
          (quittingLiveHist reward time)).toReal *
            quittingLiveIndicator reward
              (quittingLiveHist reward time).2 := by
      apply Finset.sum_eq_single (quittingLiveHist reward time)
      · intro history _ hhistory
        by_cases hlive : history.2 = none
        · by_cases hmass :
              ((quittingGame reward).histDist profile none time) history = 0
          · simp [hmass]
          · have hsupported : history ∈
                ((quittingGame reward).histDist profile none time).support :=
              (PMF.mem_support_iff _ _).2 hmass
            have heq :=
              eq_quittingLiveHist_of_mem_support_histDist_of_snd_eq_none
                reward profile history hsupported hlive
            exact (hhistory heq).elim
        · cases hstate : history.2 with
          | none => exact (hlive hstate).elim
          | some S => simp [hstate, quittingLiveIndicator]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    _ = (((quittingGame reward).histDist profile none time)
          (quittingLiveHist reward time)).toReal := by
      simp

/-- Live mass is at most one. -/
theorem quittingLiveMass_le_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward profile time ≤ 1 := by
  unfold quittingLiveMass
  rw [← ENNReal.toReal_one,
    ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by simp)]
  exact PMF.coe_le_one _ _

/-- A PMF coordinate is the expectation of its singleton indicator. -/
theorem pmf_apply_toReal_eq_expect_indicator
    {Ω : Type} [Finite Ω] [DecidableEq Ω]
    (distribution : PMF Ω) (point : Ω) :
    (distribution point).toReal =
      expect distribution (fun other => if other = point then 1 else 0) := by
  classical
  letI : Fintype Ω := Fintype.ofFinite Ω
  rw [expect_eq_sum]
  simp

/-- From the live state, the next state remains live exactly under the
all-continue joint action. -/
theorem expect_quittingGame_transition_liveIndicator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (action : ι → Bool) :
    expect ((quittingGame reward).transition none action)
        (quittingLiveIndicator reward) =
      if action = quittingAllContinueAction then 1 else 0 := by
  classical
  by_cases hquit : (quittingQuitters action).Nonempty
  · have hraw : ({who | action who = true} : Finset ι).Nonempty := by
      simpa [quittingQuitters] using hquit
    have hne : action ≠ (quittingAllContinueAction : ι → Bool) := by
      intro heq
      subst action
      simpa using hquit
    rw [quittingGame_transition_none, dif_pos hraw]
    simp [hne, quittingLiveIndicator]
  · have heq :=
      eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty
        action hquit
    subst action
    have hraw :
        ¬({who | (quittingAllContinueAction : ι → Bool) who = true} :
          Finset ι).Nonempty := by
      simp [quittingAllContinueAction]
    rw [quittingGame_transition_none, dif_neg hraw]
    simp [quittingLiveIndicator]

/-- Conditional on a live current history, the expected next live indicator
is the all-continue action coordinate.  At an absorbed history it is zero. -/
theorem expect_stageAction_transition_quittingLiveIndicator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {time : ℕ} (history : (quittingGame reward).Hist time) :
    expect ((quittingGame reward).stageActionDist profile history) (fun action =>
        expect ((quittingGame reward).transition history.2 action)
          (quittingLiveIndicator reward)) =
      match history.2 with
      | none =>
          ((((quittingGame reward).stageActionDist profile history)
            (quittingAllContinueAction : ι → Bool)).toReal)
      | some _ => 0 := by
  classical
  cases hstate : history.2 with
  | none =>
      let distribution : PMF (ι → Bool) :=
        (quittingGame reward).stageActionDist profile history
      with_unfolding_all
        change expect distribution (fun action : ι → Bool =>
            expect ((quittingGame reward).transition none action)
              (fun state =>
                match state with | none => (1 : ℝ) | some _ => 0)) =
          (distribution quittingAllContinueAction).toReal
      rw [pmf_apply_toReal_eq_expect_indicator]
      apply congrArg (expect distribution)
      funext action
      by_cases hquit :
          ({who | action who = true} : Finset ι).Nonempty
      · rw [quittingGame_transition_none, dif_pos hquit]
        have hne :
            action ≠ (quittingAllContinueAction : ι → Bool) := by
          intro heq
          subst action
          simpa [quittingAllContinueAction] using hquit
        simp only [expect_pure]
        rw [if_neg hne]
      · rw [quittingGame_transition_none, dif_neg hquit]
        have heq :
            action = (quittingAllContinueAction : ι → Bool) := by
          funext who
          change action who = false
          cases ha : action who with
          | false => rfl
          | true => exact (hquit ⟨who, by simp [ha]⟩).elim
        simp [heq]
  | some S =>
      simp [quittingGame, quittingLiveIndicator]

/-- The stopping recurrence: current live mass times the conditional
all-continue probability is the live mass one stage later. -/
theorem quittingLiveMass_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward profile (time + 1) =
      quittingLiveMass reward profile time *
        quittingJointContinueMass reward profile time := by
  classical
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ who : ι, Finite ((quittingGame reward).Act who) :=
    fun _ => inferInstanceAs (Finite Bool)
  rw [quittingLiveMass_eq_expectedStateValue,
    (quittingGame reward).expectedStateValue_succ]
  calc
    expect ((quittingGame reward).histDist profile none time) (fun history =>
        expect ((quittingGame reward).stageActionDist profile history)
          (fun action => expect
            ((quittingGame reward).transition history.2 action)
              (quittingLiveIndicator reward))) =
      expect ((quittingGame reward).histDist profile none time) (fun history =>
        quittingJointContinueMass reward profile time *
          quittingLiveIndicator reward history.2) := by
        apply Math.ProbabilityMassFunction.expect_congr_on_support
        intro history hsupported
        rw [expect_stageAction_transition_quittingLiveIndicator]
        cases hstate : history.2 with
        | none =>
          have heq :=
            eq_quittingLiveHist_of_mem_support_histDist_of_snd_eq_none
              reward profile history hsupported hstate
          subst history
          simp [quittingJointContinueMass]
        | some S => simp [hstate, quittingLiveIndicator]
    _ = quittingJointContinueMass reward profile time *
        quittingLiveMass reward profile time := by
      rw [expect_const_mul, quittingLiveMass_eq_expectedStateValue]
      rfl
    _ = quittingLiveMass reward profile time *
        quittingJointContinueMass reward profile time := by ring

/-- Live mass is nonincreasing. -/
theorem quittingLiveMass_succ_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward profile (time + 1) ≤
      quittingLiveMass reward profile time := by
  rw [quittingLiveMass_succ]
  exact mul_le_of_le_one_right
    (quittingLiveMass_nonneg reward profile time)
    (quittingJointContinueMass_le_one reward profile time)

/-- Live mass is antitone in time. -/
theorem quittingLiveMass_antitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    Antitone (quittingLiveMass reward profile) :=
  antitone_nat_of_succ_le fun time =>
    quittingLiveMass_succ_le reward profile time

end GameTheory
