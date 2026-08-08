/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.OpponentActionMass

/-!
# Absorption involving an opponent

For a fixed player `who`, non-solo absorption means absorption at any quitter
set other than the singleton `{who}`.  Its one-step increment is live mass
times the conditional probability that some opponent quits.  This is the
stopping-process coordinate needed when opponent nonabsorption has positive
probability.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Indicator of an absorbed state whose original quitter set is not the
singleton `{who}`. -/
def quittingNonSoloIndicator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    (quittingGame reward).State → ℝ
  | none => 0
  | some S => if S = quittingSingletonTerminal who then 0 else 1

/-- Probability that absorption involving at least one opponent has occurred
by `time`. -/
def quittingNonSoloMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) : ℝ :=
  (quittingGame reward).expectedStateValue profile none time
    (quittingNonSoloIndicator reward who)

omit [DecidableEq ι] in
/-- If some opponent quits, the resulting quitter set is not `{who}`. -/
theorem quittingQuitters_ne_singleton_of_someOpponentQuits
    (who : ι) (action : ι → Bool)
    (hopponent : quittingSomeOpponentQuits who action)
    (hquit : (quittingQuitters action).Nonempty) :
    (⟨quittingQuitters action, hquit⟩ :
      {S : Finset ι // S.Nonempty}) ≠ quittingSingletonTerminal who := by
  classical
  rintro heq
  obtain ⟨other, hother, haction⟩ := hopponent
  have hmem : other ∈ quittingQuitters action := by
    simp [quittingQuitters, haction]
  have hsets : quittingQuitters action = {who} := by
    exact congrArg Subtype.val heq
  rw [hsets] at hmem
  simp [hother] at hmem

omit [DecidableEq ι] in
/-- If no opponent quits but `who` does, the quitter set is `{who}`. -/
theorem quittingQuitters_eq_singleton_of_noOpponent_of_self
    (who : ι) (action : ι → Bool)
    (hnoOpponent : ¬quittingSomeOpponentQuits who action)
    (hself : action who = true) :
    quittingQuitters action = {who} := by
  classical
  ext player
  by_cases hp : player = who
  · subst player
    simp [quittingQuitters, hself]
  · cases haction : action player with
    | false => simp [quittingQuitters, hp, haction]
    | true => exact (hnoOpponent ⟨player, hp, haction⟩).elim

omit [DecidableEq ι] in
/-- If neither `who` nor any opponent quits, the quitter set is empty. -/
theorem quittingQuitters_eq_empty_of_noOpponent_of_not_self
    (who : ι) (action : ι → Bool)
    (hnoOpponent : ¬quittingSomeOpponentQuits who action)
    (hself : action who = false) :
    quittingQuitters action = ∅ := by
  classical
  ext player
  by_cases hp : player = who
  · subst player
    simp [quittingQuitters, hself]
  · cases haction : action player with
    | false => simp [quittingQuitters, haction]
    | true => exact (hnoOpponent ⟨player, hp, haction⟩).elim

/-- Starting live, the next non-solo indicator is exactly the indicator that
some opponent quits in the current joint action. -/
theorem expect_transition_quittingNonSoloIndicator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (action : ι → Bool) :
    expect ((quittingGame reward).transition none action)
        (quittingNonSoloIndicator reward who) =
      quittingSomeOpponentQuitsIndicator who action := by
  classical
  by_cases hopponent : quittingSomeOpponentQuits who action
  · have hopponentFull := hopponent
    have hflag :=
      (quittingOpponentQuitFlag_eq_true_iff who action).2 hopponentFull
    obtain ⟨other, _, hother⟩ := hopponent
    have hquit : (quittingQuitters action).Nonempty := by
      exact (quittingQuitters_nonempty_iff action).2 ⟨other, hother⟩
    have hne := quittingQuitters_ne_singleton_of_someOpponentQuits
      who action hopponentFull hquit
    have hraw : ({player | action player = true} : Finset ι).Nonempty := by
      simpa [quittingQuitters] using hquit
    have hneRaw :
        (⟨({player | action player = true} : Finset ι), hraw⟩ :
          {S : Finset ι // S.Nonempty}) ≠
            quittingSingletonTerminal who := by
      simpa [quittingQuitters] using hne
    rw [quittingGame_transition_none, dif_pos hraw]
    simp [quittingNonSoloIndicator, hneRaw,
      quittingSomeOpponentQuitsIndicator, hflag]
  · have hflag : quittingOpponentQuitFlag who action ≠ true :=
      fun h => hopponent
        ((quittingOpponentQuitFlag_eq_true_iff who action).1 h)
    have hflagFalse : quittingOpponentQuitFlag who action = false := by
      cases h : quittingOpponentQuitFlag who action
      · rfl
      · exact (hflag h).elim
    cases hself : action who with
    | false =>
        have hempty :=
          quittingQuitters_eq_empty_of_noOpponent_of_not_self
            who action hopponent hself
        have hraw :
            ¬({player | action player = true} : Finset ι).Nonempty := by
          have hrawEmpty :
              ({player | action player = true} : Finset ι) = ∅ := by
            simpa [quittingQuitters] using hempty
          simp [hrawEmpty]
        rw [quittingGame_transition_none, dif_neg hraw]
        simp [quittingNonSoloIndicator,
          quittingSomeOpponentQuitsIndicator, hflagFalse]
    | true =>
        have hsingleton :=
          quittingQuitters_eq_singleton_of_noOpponent_of_self
            who action hopponent hself
        have hraw :
            ({player | action player = true} : Finset ι).Nonempty := by
          exact ⟨who, by simp [hself]⟩
        rw [quittingGame_transition_none, dif_pos hraw]
        have hterminalRaw :
            (⟨({player | action player = true} : Finset ι), hraw⟩ :
                {S : Finset ι // S.Nonempty}) =
              quittingSingletonTerminal who := by
          apply Subtype.ext
          change ({player | action player = true} : Finset ι) = {who}
          simpa [quittingQuitters] using hsingleton
        simp [quittingNonSoloIndicator, hterminalRaw,
          quittingSomeOpponentQuitsIndicator, hflagFalse]

/-- At the canonical live history under a unilateral deviation, conditional
next non-solo mass is one minus the opponents' all-continue probability. -/
theorem expect_stageAction_transition_nonSolo_live_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (time : ℕ) :
    expect ((quittingGame reward).stageActionDist
        (Function.update profile who deviation)
        (quittingLiveHist reward time)) (fun action =>
      expect ((quittingGame reward).transition none action)
        (quittingNonSoloIndicator reward who)) =
      1 - quittingJointContinueMass reward
        (quittingOpponentOnlyProfile reward profile who) time := by
  let root : ι → PMF Bool := fun player =>
    profile player time (quittingLiveHist reward time)
  have haction :
      (quittingGame reward).stageActionDist
          (Function.update profile who deviation)
          (quittingLiveHist reward time) =
        pmfPi (Function.update root who
          (deviation time (quittingLiveHist reward time))) := by
    unfold StochasticGame.stageActionDist
    congr 1
    funext player
    by_cases hp : player = who
    · subst player
      simp [root]
    · simp [root, Function.update_of_ne hp]
  have hcontinue :
      quittingJointContinueMass reward
          (quittingOpponentOnlyProfile reward profile who) time =
        ((pmfPi (Function.update root who (PMF.pure false)))
          (quittingAllContinueAction : ι → Bool)).toReal := by
    unfold quittingJointContinueMass quittingOpponentOnlyProfile
      StochasticGame.stageActionDist
    congr 3
    funext player
    by_cases hp : player = who
    · subst player
      simp [root, quittingAlwaysContinueStrategy]
      rfl
    · simp [root, Function.update_of_ne hp]
  rw [haction, hcontinue]
  simp_rw [expect_transition_quittingNonSoloIndicator]
  exact expect_pmfPi_someOpponentQuits_eq_one_sub_continueMass
    root who (deviation time (quittingLiveHist reward time))

/-- Exact one-step recurrence for non-solo absorption mass under a unilateral
deviation. -/
theorem quittingNonSoloMass_update_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (time : ℕ) :
    quittingNonSoloMass reward
        (Function.update profile who deviation) who (time + 1) =
      quittingNonSoloMass reward
          (Function.update profile who deviation) who time +
        quittingLiveMass reward
          (Function.update profile who deviation) time *
          (1 - quittingJointContinueMass reward
            (quittingOpponentOnlyProfile reward profile who) time) := by
  classical
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  unfold quittingNonSoloMass
  rw [(quittingGame reward).expectedStateValue_succ]
  let deviationProfile := Function.update profile who deviation
  let opponentContinue := quittingJointContinueMass reward
    (quittingOpponentOnlyProfile reward profile who) time
  calc
    expect ((quittingGame reward).histDist deviationProfile none time)
        (fun history =>
          expect ((quittingGame reward).stageActionDist deviationProfile history)
            (fun action => expect
              ((quittingGame reward).transition history.2 action)
                (quittingNonSoloIndicator reward who))) =
      expect ((quittingGame reward).histDist deviationProfile none time)
        (fun history =>
          quittingNonSoloIndicator reward who history.2 +
            (1 - opponentContinue) *
              quittingLiveIndicator reward history.2) := by
        apply Math.ProbabilityMassFunction.expect_congr_on_support
        intro history hsupported
        cases hstate : history.2 with
        | none =>
            have heq :=
              eq_quittingLiveHist_of_mem_support_histDist_of_snd_eq_none
                reward deviationProfile history hsupported hstate
            subst history
            rw [expect_stageAction_transition_nonSolo_live_update]
            simp [quittingNonSoloIndicator, quittingLiveIndicator,
              opponentContinue]
        | some S =>
            simp [quittingGame, quittingLiveIndicator]
    _ = quittingNonSoloMass reward deviationProfile who time +
        (1 - opponentContinue) *
          quittingLiveMass reward deviationProfile time := by
      rw [expect_add, expect_const_mul,
        quittingLiveMass_eq_expectedStateValue]
      rfl
    _ = quittingNonSoloMass reward deviationProfile who time +
        quittingLiveMass reward deviationProfile time *
          (1 - opponentContinue) := by ring

end GameTheory
