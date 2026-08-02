/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingRootContinuation

/-!
# Simple terminal branches in quitting games

This module proves the exact `Never` test from Question 101.  Against
opponents who always continue, a player can only reach their singleton
quitter state, so every deviation payoff lies between zero and that singleton
reward.  The all-continue profile is therefore a terminal
`ε`-equilibrium exactly when every singleton quitting reward is at most `ε`.

No claim about absorption paths or the non-simple branch is made.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The stationary profile under which every player always continues. -/
def quittingAlwaysContinueProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingGame reward).BehaviorProfile :=
  (quittingGame reward).stationaryBehaviorProfile fun _ => PMF.pure false

/-- The behavior strategy which always continues. -/
def quittingAlwaysContinueStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    (quittingGame reward).BehaviorStrategy who :=
  fun _ _ => PMF.pure false

/-- The behavior strategy which always quits. -/
def quittingAlwaysQuitStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    (quittingGame reward).BehaviorStrategy who :=
  fun _ _ => PMF.pure true

/-- The root action law after a unilateral deviation from all-continue. -/
theorem stageActionDist_update_quittingAlwaysContinueProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    {t : ℕ} (h : (quittingGame reward).Hist t) :
    (quittingGame reward).stageActionDist
        (Function.update (quittingAlwaysContinueProfile reward) who deviation) h =
      pmfPi (Function.update (fun _ : ι => PMF.pure false) who
        (deviation t h)) := by
  change (quittingGame reward).stageActionDist
      (Function.update ((quittingGame reward).stationaryBehaviorProfile
        fun _ : ι => PMF.pure false) who deviation) h = _
  exact (quittingGame reward).stageActionDist_update_stationaryBehaviorProfile
    (fun _ : ι => PMF.pure false) who deviation h

omit [DecidableEq ι] in
/-- The all-continue profile induces the pure all-false joint action. -/
@[simp] theorem stageActionDist_quittingAlwaysContinueProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {t : ℕ} (h : (quittingGame reward).Hist t) :
    (quittingGame reward).stageActionDist
        (quittingAlwaysContinueProfile reward) h =
      PMF.pure (show (quittingGame reward).JointAct from
        fun _ : ι => false) := by
  change (quittingGame reward).stageActionDist
      ((quittingGame reward).stationaryBehaviorProfile
        fun _ : ι => PMF.pure false) h = _
  rw [(quittingGame reward).stageActionDist_stationaryBehaviorProfile,
    pmfPi_pure]

/-- The singleton terminal state of one quitter. -/
def quittingSingletonTerminal (who : ι) :
    {S : Finset ι // S.Nonempty} :=
  ⟨{who}, Finset.singleton_nonempty who⟩

/-- Under a unilateral deviation from all-continue, every supported joint
action keeps every opponent at `continue`. -/
theorem action_eq_false_of_mem_support_update_quittingAlwaysContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    {t : ℕ} (h : (quittingGame reward).Hist t)
    (action : ι → Bool)
    (haction : action ∈ ((quittingGame reward).stageActionDist
      (Function.update (quittingAlwaysContinueProfile reward) who deviation)
      h).support)
    (other : ι) (hother : other ≠ who) : action other = false := by
  have hdist :=
    stageActionDist_update_quittingAlwaysContinueProfile
      reward who deviation h
  rw [hdist] at haction
  let factors : ι → PMF Bool :=
    Function.update (fun _ : ι => PMF.pure false) who (deviation t h)
  have hcoord : action other ∈
      (Math.ProbabilityMassFunction.pushforward (pmfPi factors)
        (fun joint => joint other)).support := by
    rw [Math.ProbabilityMassFunction.pushforward,
      PMF.mem_support_map_iff]
    exact ⟨action, haction, rfl⟩
  rw [pmfPi_push_coord factors other] at hcoord
  have hfactor : factors other = PMF.pure false := by
    simp [factors, Function.update_of_ne hother]
  rw [hfactor] at hcoord
  exact (PMF.mem_support_pure_iff _ _).mp (by simpa [hfactor] using hcoord)

/-- Under a unilateral deviation from all-continue, every supported history
is either still active or has absorbed at the deviator's singleton state. -/
theorem state_eq_none_or_singleton_of_mem_support_update_quittingAlwaysContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    ∀ (t : ℕ) (h : (quittingGame reward).Hist t),
      h ∈ ((quittingGame reward).histDist
        (Function.update (quittingAlwaysContinueProfile reward) who deviation)
        none t).support →
      h.2 = none ∨ h.2 = some (quittingSingletonTerminal who) := by
  classical
  intro t
  induction t with
  | zero =>
      intro h hh
      left
      have heq : h = (quittingGame reward).emptyHist none := by
        simpa using hh
      rw [heq]
      rfl
  | succ t ih =>
      intro h' hh'
      rw [(quittingGame reward).mem_support_histDist_succ] at hh'
      obtain ⟨h, hh, action, haction, next, hnext, rfl⟩ := hh'
      change (ι → Bool) at action
      rcases ih h hh with hactive | habsorbed
      · rw [hactive] at hnext
        by_cases hwho : action who = true
        · have hset : ({player | action player = true} : Finset ι) = {who} := by
            ext player
            by_cases hp : player = who
            · subst player
              simp [hwho]
            · have hfalse :=
                action_eq_false_of_mem_support_update_quittingAlwaysContinue
                  reward who deviation h action haction player hp
              simp [hp, hfalse]
          have hnonempty :
              ({player | action player = true} : Finset ι).Nonempty := by
            rw [hset]
            exact Finset.singleton_nonempty who
          rw [quittingGame_transition_none, dif_pos hnonempty] at hnext
          right
          have hstate : next = some (quittingSingletonTerminal who) := by
            simpa [quittingSingletonTerminal, hset] using hnext
          exact hstate
        · have hfalseWho : action who = false := by
            cases h : action who <;> simp_all
          have hset : ({player | action player = true} : Finset ι) = ∅ := by
            ext player
            by_cases hp : player = who
            · subst player
              simp [hfalseWho]
            · have hfalse :=
                action_eq_false_of_mem_support_update_quittingAlwaysContinue
                  reward who deviation h action haction player hp
              simp [hfalse]
          have hempty :
              ¬({player | action player = true} : Finset ι).Nonempty := by
            rw [hset]
            simp
          rw [quittingGame_transition_none, dif_neg hempty] at hnext
          left
          simpa using hnext
      · rw [habsorbed, show (quittingGame reward).transition
            (some (quittingSingletonTerminal who)) action =
            PMF.pure (some (quittingSingletonTerminal who)) by rfl] at hnext
        right
        exact (PMF.mem_support_pure_iff _ _).mp hnext

/-- Every unilateral terminal payoff against all-continue is at most the
larger of zero and the deviator's singleton quitting reward. -/
theorem quittingTerminalPayoff_update_quittingAlwaysContinue_le_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update (quittingAlwaysContinueProfile reward) who deviation)
        who ≤
      max 0 (reward (quittingSingletonTerminal who) who) := by
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  let profile :=
    Function.update (quittingAlwaysContinueProfile reward) who deviation
  have hstage : ∀ t : ℕ,
      (quittingGame reward).expectedStagePayoff profile none t who ≤
        max 0 (reward (quittingSingletonTerminal who) who) := by
    intro t
    unfold StochasticGame.expectedStagePayoff
    apply Math.ProbabilityMassFunction.expect_le_of_le_on_support
    intro h hh
    rw [stageEUAt_quittingGame_eq_stateReward]
    rcases state_eq_none_or_singleton_of_mem_support_update_quittingAlwaysContinue
        reward who deviation t h (by simpa [profile] using hh) with
      hnone | hsingleton
    · rw [hnone]
      exact le_max_left _ _
    · rw [hsingleton]
      exact le_max_right _ _
  exact le_of_tendsto'
    (tendsto_expectedStagePayoff_quittingGame reward profile who) hstage

/-- Under all-continue, every supported history remains active. -/
theorem state_eq_none_of_mem_support_quittingAlwaysContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∀ (t : ℕ) (h : (quittingGame reward).Hist t),
      h ∈ ((quittingGame reward).histDist
        (quittingAlwaysContinueProfile reward) none t).support → h.2 = none := by
  intro t
  induction t with
  | zero =>
      intro h hh
      have heq : h = (quittingGame reward).emptyHist none := by
        simpa using hh
      rw [heq]
      rfl
  | succ t ih =>
      intro h' hh'
      rw [(quittingGame reward).mem_support_histDist_succ] at hh'
      obtain ⟨h, hh, action, haction, next, hnext, rfl⟩ := hh'
      change (ι → Bool) at action
      have hstate := ih h hh
      have hdist : (quittingGame reward).stageActionDist
          (quittingAlwaysContinueProfile reward) h =
          PMF.pure (show (quittingGame reward).JointAct from
            fun _ : ι => false) :=
        stageActionDist_quittingAlwaysContinueProfile reward h
      rw [hdist] at haction
      have hactionEq : action = (fun _ : ι => false) :=
        (PMF.mem_support_pure_iff _ _).mp haction
      subst action
      rw [hstate, quittingGame_transition_none] at hnext
      simp at hnext
      simpa using hnext

/-- The all-continue profile has terminal payoff zero. -/
@[simp] theorem quittingTerminalPayoff_quittingAlwaysContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) who = 0 := by
  have hstage : ∀ t : ℕ,
      (quittingGame reward).expectedStagePayoff
        (quittingAlwaysContinueProfile reward) none t who = 0 := by
    intro t
    unfold StochasticGame.expectedStagePayoff
    calc
      expect ((quittingGame reward).histDist
          (quittingAlwaysContinueProfile reward) none t)
          (fun h => (quittingGame reward).stageEUAt
            (quittingAlwaysContinueProfile reward) h who) =
          expect ((quittingGame reward).histDist
            (quittingAlwaysContinueProfile reward) none t)
            (fun _ => (0 : ℝ)) := by
        apply Math.ProbabilityMassFunction.expect_congr_on_support
        intro h hh
        rw [stageEUAt_quittingGame_eq_stateReward,
          state_eq_none_of_mem_support_quittingAlwaysContinue reward t h hh]
        rfl
      _ = 0 := expect_const _ _
  apply tendsto_nhds_unique
    (tendsto_expectedStagePayoff_quittingGame reward
      (quittingAlwaysContinueProfile reward) who)
  simpa only [hstage] using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/-- Quitting immediately against all-continuing opponents yields the
singleton terminal reward. -/
theorem quittingTerminalPayoff_update_quittingAlwaysQuitStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingTerminalPayoff reward
        (Function.update (quittingAlwaysContinueProfile reward) who
          (quittingAlwaysQuitStrategy reward who)) who =
      reward (quittingSingletonTerminal who) who := by
  rw [quittingTerminalPayoff_eq_expect_rootContinuation]
  rw [stageActionDist_update_quittingAlwaysContinueProfile]
  let quitAction : ι → Bool :=
    Function.update (fun _ : ι => false) who true
  have hfamily :
      Function.update (fun _ : ι => PMF.pure false) who
          ((quittingAlwaysQuitStrategy reward who) 0
            ((quittingGame reward).emptyHist none)) =
        fun player => PMF.pure (quitAction player) := by
    funext player
    by_cases hp : player = who
    · subst player
      simp [quitAction, quittingAlwaysQuitStrategy]
      with_unfolding_all rfl
    · simp [Function.update_of_ne hp, quittingAlwaysQuitStrategy, quitAction]
  rw [hfamily, pmfPi_pure]
  with_unfolding_all
    change expect (PMF.pure quitAction)
        (fun action : ι → Bool =>
          quittingRootContinuationPayoff reward
            (Function.update (quittingAlwaysContinueProfile reward) who
              (quittingAlwaysQuitStrategy reward who)) action who) = _
  rw [expect_pure]
  have hset :
      quittingQuitters quitAction =
        {who} := by
    ext player
    by_cases hp : player = who <;> simp [quittingQuitters, quitAction, hp]
  have hnonempty :
      (quittingQuitters quitAction).Nonempty := by
    rw [hset]
    exact Finset.singleton_nonempty who
  rw [quittingRootContinuationPayoff_of_quitters _ _ _ _ hnonempty]
  congr

/-- Exact terminal `ε`-Nash test for the all-continue profile. -/
theorem isεAsymptoticNash_quittingAlwaysContinue_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingAlwaysContinueProfile reward) ↔
      ∀ who, reward (quittingSingletonTerminal who) who ≤ ε := by
  constructor
  · intro hnash who
    have hdev := hnash who (quittingAlwaysQuitStrategy reward who)
    rw [quittingTerminalPayoff_quittingAlwaysContinue,
      quittingTerminalPayoff_update_quittingAlwaysQuitStrategy] at hdev
    simpa using hdev
  · intro hsingleton who deviation
    rw [quittingTerminalPayoff_quittingAlwaysContinue]
    have hbound :=
      quittingTerminalPayoff_update_quittingAlwaysContinue_le_max
        reward who deviation
    have hmax : max 0 (reward (quittingSingletonTerminal who) who) ≤ ε :=
      max_le hε (hsingleton who)
    simpa using hbound.trans hmax

/-- The `Never` branch exists at every positive accuracy exactly when every
singleton quitting reward is nonpositive. -/
theorem always_isεAsymptoticNash_quittingAlwaysContinue_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∀ ε : ℝ, 0 < ε →
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingAlwaysContinueProfile reward)) ↔
      ∀ who, reward (quittingSingletonTerminal who) who ≤ 0 := by
  constructor
  · intro hall who
    by_contra hnot
    have hpos : 0 < reward (quittingSingletonTerminal who) who :=
      lt_of_not_ge hnot
    have hnash :=
      (isεAsymptoticNash_quittingAlwaysContinue_iff reward
        (show 0 ≤ reward (quittingSingletonTerminal who) who / 2 by positivity)).mp
        (hall _ (by positivity)) who
    linarith
  · intro hnonpos ε hε
    exact (isεAsymptoticNash_quittingAlwaysContinue_iff reward hε.le).mpr
      fun who => (hnonpos who).trans hε.le

end GameTheory
