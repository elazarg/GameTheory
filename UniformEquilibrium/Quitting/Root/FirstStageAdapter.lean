/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.FirstBranch

/-!
# Adapting an arbitrary quitting profile to the sure-first branch

Every quitting-game behavior profile has a canonical root/continuation
representative: take its time-zero product marginals as the root law and use
the original profile shifted past the unique all-continue root action as the
continuation.  The representative can differ from the original profile after
a root action that already caused absorption, but those histories cannot
affect terminal reward.

This file proves the stronger fact actually needed by the `First` branch:
the canonical representative has exactly the same prescribed terminal payoff
and exactly the same terminal payoff under every fixed unilateral behavior
deviation.  Hence it is an asymptotic epsilon-Nash profile exactly when the
original profile is.  Combining this adapter with `QuittingFirstBranch` gives
an existential classification of all profiles that absorb surely at the
first stage, not only profiles initially presented as root/continuation
splices.

This is a classification of the exact sure-first branch.  It does not extract
a sure-first limit from profiles whose first-stage absorption probabilities
merely converge to one.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The unique joint action at which every player continues. -/
def quittingAllContinueAction : ι → Bool :=
  fun _ => false

/-- The time-zero mixed action of every player in a behavior profile. -/
def quittingProfileRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : ι → PMF Bool :=
  fun who => profile who 0 ((quittingGame reward).emptyHist none)

/-- The profile shifted past the unique all-continue root history. -/
def quittingProfileAllContinueContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  (quittingGame reward).shiftProfile profile
    (none, quittingAllContinueAction)

/-- The canonical root/continuation representative of an arbitrary profile. -/
def quittingFirstStageAdapter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward
    (quittingProfileRoot reward profile)
    (quittingProfileAllContinueContinuation reward profile)

/-- First-stage absorption is sure when the unique nonabsorbing root action
has probability zero. -/
def QuittingProfileAbsorbsSurelyAtFirstStage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : Prop :=
  (quittingGame reward).stageActionDist profile
      ((quittingGame reward).emptyHist none)
      quittingAllContinueAction = 0

omit [DecidableEq ι] in
@[simp] theorem stageActionDist_quittingProfileRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).stageActionDist profile
        ((quittingGame reward).emptyHist none) =
      pmfPi (quittingProfileRoot reward profile) :=
  rfl

omit [DecidableEq ι] in
/-- A profile absorbs surely at the first stage exactly when its extracted
root product action has a sure quitter. -/
theorem quittingProfileAbsorbsSurelyAtFirstStage_iff_rootHasSureQuitter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    QuittingProfileAbsorbsSurelyAtFirstStage reward profile ↔
      QuittingRootHasSureQuitter (quittingProfileRoot reward profile) := by
  change pmfPi (quittingProfileRoot reward profile)
      quittingAllContinueAction = 0 ↔ _
  simpa [quittingAllContinueAction] using
    (quittingRootHasSureQuitter_iff_allContinue_mass_zero
      (quittingProfileRoot reward profile)).symm

omit [DecidableEq ι] in
@[simp] theorem quittingProfileRoot_rootThenContinuationProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) :
    quittingProfileRoot reward
        (quittingRootThenContinuationProfile reward root continuation) =
      root := by
  funext who
  rfl

omit [DecidableEq ι] in
@[simp] theorem quittingProfileRoot_firstStageAdapter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingProfileRoot reward (quittingFirstStageAdapter reward profile) =
      quittingProfileRoot reward profile := by
  rw [quittingFirstStageAdapter,
    quittingProfileRoot_rootThenContinuationProfile]

omit [DecidableEq ι] in
@[simp] theorem quittingQuitters_allContinueAction :
    quittingQuitters (quittingAllContinueAction : ι → Bool) = ∅ := by
  ext who
  simp [quittingQuitters, quittingAllContinueAction]

omit [DecidableEq ι] in
/-- A Boolean joint action with no quitter is the all-continue action. -/
theorem eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty
    (action : ι → Bool) (h : ¬(quittingQuitters action).Nonempty) :
    action = quittingAllContinueAction := by
  funext who
  change action who = false
  cases haction : action who with
  | false => rfl
  | true =>
      exact (h ((quittingQuitters_nonempty_iff action).2
        ⟨who, haction⟩)).elim

/-- Shifting an updated arbitrary quitting profile updates its shifted
continuation by the correspondingly shifted behavior deviation. -/
theorem shiftProfile_update_quittingProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    (action : ι → Bool) :
    (quittingGame reward).shiftProfile
        (Function.update profile who deviation) (none, action) =
      Function.update
        ((quittingGame reward).shiftProfile profile (none, action)) who
        (quittingShiftBehaviorStrategy reward deviation action) := by
  funext player t history
  by_cases hp : player = who
  · subst player
    simp [StochasticGame.shiftProfile, quittingShiftBehaviorStrategy]
  · simp [StochasticGame.shiftProfile, Function.update_of_ne hp]

/-- After all-continue, an updated profile and its canonical representative
have exactly the same shifted profile. -/
theorem shiftProfile_update_firstStageAdapter_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    (quittingGame reward).shiftProfile
        (Function.update (quittingFirstStageAdapter reward profile)
          who deviation)
        (none, quittingAllContinueAction) =
      (quittingGame reward).shiftProfile
        (Function.update profile who deviation)
        (none, quittingAllContinueAction) := by
  unfold quittingFirstStageAdapter
  rw [shiftProfile_update_quittingRootThenContinuationProfile,
    shiftProfile_update_quittingProfile]
  rfl

/-- Updating a profile and its canonical representative by the same behavior
deviation gives the same time-zero joint-action law. -/
theorem stageActionDist_update_firstStageAdapter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    (quittingGame reward).stageActionDist
        (Function.update (quittingFirstStageAdapter reward profile)
          who deviation)
        ((quittingGame reward).emptyHist none) =
      (quittingGame reward).stageActionDist
        (Function.update profile who deviation)
        ((quittingGame reward).emptyHist none) := by
  unfold StochasticGame.stageActionDist
  congr 1
  funext player
  by_cases hp : player = who
  · subst player
    simp
  · simp [Function.update_of_ne hp, quittingFirstStageAdapter,
      quittingRootThenContinuationProfile, quittingProfileRoot]

omit [DecidableEq ι] in
/-- The canonical representative has exactly the prescribed terminal payoff
of the original profile. -/
@[simp] theorem quittingTerminalPayoff_firstStageAdapter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
        (quittingFirstStageAdapter reward profile) who =
      quittingTerminalPayoff reward profile who := by
  classical
  rw [quittingFirstStageAdapter,
    quittingTerminalPayoff_rootThenContinuation_eq,
    quittingTerminalPayoff_eq_expect_rootContinuation]
  unfold quittingRootExpectedPayoff
  rw [stageActionDist_quittingProfileRoot]
  apply congrArg (expect (pmfPi (quittingProfileRoot reward profile)))
  funext action
  by_cases hquit : (quittingQuitters action).Nonempty
  · simp [quittingRootPayoff, quittingRootContinuationPayoff, hquit]
  · have haction :=
      eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty
        action hquit
    subst action
    simp [quittingRootPayoff, quittingRootContinuationPayoff,
      quittingProfileAllContinueContinuation]

/-- The canonical representative and the original profile give every fixed
unilateral behavior deviation exactly the same terminal payoff. -/
@[simp] theorem quittingTerminalPayoff_update_firstStageAdapter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update (quittingFirstStageAdapter reward profile)
          who deviation) who =
      quittingTerminalPayoff reward
        (Function.update profile who deviation) who := by
  rw [quittingTerminalPayoff_eq_expect_rootContinuation,
    quittingTerminalPayoff_eq_expect_rootContinuation,
    stageActionDist_update_firstStageAdapter]
  apply congrArg (expect
    ((quittingGame reward).stageActionDist
      (Function.update profile who deviation)
      ((quittingGame reward).emptyHist none)))
  funext action
  by_cases hquit : (quittingQuitters action).Nonempty
  · simp [quittingRootContinuationPayoff, hquit]
  · have haction :=
      eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty
        action hquit
    rw [quittingRootContinuationPayoff_of_allContinue _ _ _ _ hquit,
      quittingRootContinuationPayoff_of_allContinue _ _ _ _ hquit]
    congr 1
    rw [haction]
    exact shiftProfile_update_firstStageAdapter_allContinue
      reward profile who deviation

/-- The canonical root/continuation representative is an asymptotic
epsilon-Nash profile exactly when the original profile is. -/
theorem isεAsymptoticNash_firstStageAdapter_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (ε : ℝ) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingFirstStageAdapter reward profile) ↔
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile := by
  constructor <;> intro hnash who deviation
  · simpa only [quittingTerminalPayoff_firstStageAdapter,
      quittingTerminalPayoff_update_firstStageAdapter] using
      hnash who deviation
  · simpa only [quittingTerminalPayoff_firstStageAdapter,
      quittingTerminalPayoff_update_firstStageAdapter] using
      hnash who deviation

/-- **Existential classification of the exact sure-first branch.**  A
surely first-stage absorbing asymptotic epsilon-Nash profile exists exactly
when some surely absorbing root and continuation satisfy the finite root
criterion with the continuation best-response vector. -/
theorem exists_sureFirst_isεAsymptoticNash_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {ε M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    (∃ profile : (quittingGame reward).BehaviorProfile,
      QuittingProfileAbsorbsSurelyAtFirstStage reward profile ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile) ↔
    ∃ root : ι → PMF Bool,
      ∃ continuation : (quittingGame reward).BehaviorProfile,
        QuittingRootHasSureQuitter root ∧
        IsεQuittingRootNash reward
          (quittingContinuationBestResponse reward continuation) ε root := by
  constructor
  · rintro ⟨profile, hfirst, hnash⟩
    let root := quittingProfileRoot reward profile
    let continuation :=
      quittingProfileAllContinueContinuation reward profile
    have hsure : QuittingRootHasSureQuitter root := by
      exact (quittingProfileAbsorbsSurelyAtFirstStage_iff_rootHasSureQuitter
        reward profile).mp hfirst
    refine ⟨root, continuation, hsure, ?_⟩
    apply
      isεQuittingRootNash_of_isεAsymptoticNash_quittingRootThenContinuation
        reward root continuation hM hreward hsure
    exact (isεAsymptoticNash_firstStageAdapter_iff
      reward profile ε).mpr hnash
  · rintro ⟨root, continuation, hsure, hroot⟩
    refine ⟨quittingRootThenContinuationProfile reward root continuation,
      ?_, ?_⟩
    · rw [quittingProfileAbsorbsSurelyAtFirstStage_iff_rootHasSureQuitter,
        quittingProfileRoot_rootThenContinuationProfile]
      exact hsure
    · exact
        isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash
          reward root continuation hM hreward hsure hroot

end GameTheory
