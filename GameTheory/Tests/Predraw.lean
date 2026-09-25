/-
# One-participant predrawing with a forgetful randomized opponent

Both seats move twice. The predrawn seat counts rounds in `Nat`, while its
opponent has the same `Unit` information state at both moves and randomizes
afresh. Equalities below retain the full history, including both joint actions.
-/

import GameTheory.Protocol.Predraw

noncomputable section

namespace GameTheory.Tests.Predraw

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

/-- Two simultaneous rounds; actions remain recorded in the execution trace. -/
@[reducible] def rounds : ExecutionProtocol Bool where
  State := Nat
  Action _ := Bool
  init := 0
  active _ _ := True
  available _ _ := Set.univ
  terminal state := 2 ≤ state
  step state _ := PMF.pure (state + 1)
  progress _ _ := ⟨fun _ => some false, fun _ => ⟨True.intro, Set.mem_univ _⟩⟩

/-- The predrawn seat remembers the round, the opponent remembers nothing. -/
@[reducible] def RoundInfo : Bool → Type
  | true => Nat
  | false => Unit

@[reducible] def model : InformationModel rounds where
  PublicSignal := Unit
  PrivateSignal _ := Unit
  initialPublic := ()
  initialPrivate _ := ()
  publicSignal _ := ()
  privateSignal _ _ := ()
  InfoState := RoundInfo
  initInfo
    | true, _, _ => 0
    | false, _, _ => ()
  pushInfo
    | true, round, _, _, _ => round + 1
    | false, _, _, _, _ => ()
  menu _ _ := {choice | ∃ action, choice = some action}
  menu_adequate := by
    intro who state trace choice
    cases choice <;> simp [LegalOption]

theorem info_eq_length {state : rounds.State} (trace : rounds.Trace state) :
    model.infoOf true trace = trace.length := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      simpa [InfoSignals.infoOf_extend, Trace.length] using congrArg Nat.succ ih

/-- Freshness holds for all different-length histories, without a prefix premise. -/
theorem fresh : ∀ first later : rounds.History,
    first.trace.length < later.trace.length →
      model.infoOf true later.trace ≠ model.infoOf true first.trace := by
  intro first later hlength
  rw [info_eq_length, info_eq_length]
  exact Nat.ne_of_gt hlength

/-- The target information carrier is infinite despite the finite run. -/
example : Infinite (model.InfoState true) := inferInstance

def choice (who : Bool) (info : model.InfoState who) (action : Bool) :
    model.Choice who info := ⟨some action, action, rfl⟩

def fallback : model.Policy true := fun info => choice true info false

def coin (who : Bool) (info : model.InfoState who) :
    PMF (model.Choice who info) :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure (choice who info false)) (PMF.pure (choice who info true))

def targetPolicy : model.BehavioralPolicy true := fun info =>
  if info ∈ ({0, 1} : Finset Nat) then coin true info else PMF.pure (fallback info)

def profile : Profile model.behavioralSignature
  | true => targetPolicy
  | false => coin false

theorem targetPolicy_finite (info : model.InfoState true)
    (hout : info ∉ ({0, 1} : Finset Nat)) :
    targetPolicy info = PMF.pure (fallback info) := by
  simp [targetPolicy, hout]

/-- Both answers have positive mass for the forgetful opponent. -/
theorem opponent_has_both_answers (action : Bool) :
    choice false () action ∈ (profile false ()).support := by
  apply (PMF.mem_support_iff _ _).mpr
  cases action <;>
    norm_num [profile, coin, mix_apply, PMF.pure_apply, choice]

def firstHistory : rounds.History :=
  rounds.initHistory.extend (target := 1)
    (joint := fun _ => some false)
    ⟨by simp [rounds], fun _ => ⟨True.intro, Set.mem_univ _⟩⟩
    (by simp [rounds])

def terminalHistory : rounds.History :=
  firstHistory.extend (target := 2)
    (joint := fun _ => some true)
    ⟨by simp [rounds, firstHistory], fun _ => ⟨True.intro, Set.mem_univ _⟩⟩
    (by simp [rounds, firstHistory])

/-- The opponent violates freshness across actual consecutive decision sites. -/
theorem opponent_not_fresh : ¬ (∀ first later : rounds.History,
    first.trace.length < later.trace.length →
      model.infoOf false later.trace ≠ model.infoOf false first.trace) := by
  intro hfresh
  have hlength : rounds.initHistory.trace.length < firstHistory.trace.length := by
    simp [ExecutionProtocol.initHistory, firstHistory, ExecutionProtocol.History.extend,
      ExecutionProtocol.Trace.length]
  exact hfresh rounds.initHistory firstHistory hlength rfl

/-- Predrawing changes no opponent policy, including its repeated local draw. -/
example (policy : model.Policy true) :
    (Profile.update profile true policy.toBehavioral) false = coin false := by
  rw [Profile.update_of_ne _ _ (by decide)]
  rfl

/-- The explicit finite-table theorem covers a nontrivial two-step run. -/
theorem two_round_predraw :
    (targetPolicy.toMixedOn {0, 1} fallback).bind
        (fun policy => model.runBehavioralFrom
          (Profile.update profile true policy.toBehavioral) 2 rounds.initHistory) =
      model.runBehavioralFrom profile 2 rounds.initHistory := by
  simpa only [show targetPolicy = profile true from rfl, Profile.update_eq_self] using
    model.runBehavioralFrom_predrawOneOn true fresh profile 2 targetPolicy
      {0, 1} fallback rounds.initHistory targetPolicy_finite

private theorem profileChoicesFinite : ∀ history : rounds.History,
    ¬ rounds.terminal history.state → ∀ who,
      (profile who (model.infoOf who history.trace)).support.Finite := by
  have hcoin (who : Bool) (info : model.InfoState who) :
      (coin who info).support.Finite := by
    apply ((Set.finite_singleton (choice who info true)).insert
      (choice who info false)).subset
    intro actual hactual
    rw [PMF.mem_support_iff] at hactual
    by_contra hnot
    have hnfalse : actual ≠ choice who info false := by
      intro heq
      exact hnot (by simp [heq])
    have hntrue : actual ≠ choice who info true := by
      intro heq
      exact hnot (by simp [heq])
    have hzero : coin who info actual = 0 := by
      simp [coin, mix_apply, PMF.pure_apply, hnfalse, hntrue]
    exact hactual hzero
  have hpure (info : model.InfoState true) :
      (PMF.pure (fallback info)).support.Finite := by
    simpa only [PMF.support_pure] using Set.finite_singleton (fallback info)
  intro history _ who
  cases who with
  | false => exact hcoin false ()
  | true =>
      by_cases hmem : model.infoOf true history.trace ∈ ({0, 1} : Finset Nat)
      · simpa [profile, targetPolicy, hmem] using
          hcoin true (model.infoOf true history.trace)
      · simp [profile, targetPolicy, hmem]

private theorem stepSupportFinite
    {state : rounds.State}
    (draw : {joint : ∀ who, Option (rounds.Action who) // rounds.Legal state joint}) :
    (rounds.step state draw).support.Finite := by
  simp [rounds]

private theorem predrawSitesFinite :
    (model.behavioralSupportSitesFrom profile 2 rounds.initHistory true).Finite :=
  model.behavioralSupportSitesFrom_finite_of_finite_branching profile 2
    rounds.initHistory profileChoicesFinite (fun {_} draw => stepSupportFinite draw) true

/-- The existential API needs no finite instance for the target information. -/
example : ∃ policies : PMF (model.Policy true),
    policies.bind (fun policy => model.runBehavioralFrom
        (Profile.update profile true policy.toBehavioral) 2 rounds.initHistory) =
      model.runBehavioralFrom profile 2 rounds.initHistory :=
  model.exists_predrawOne true fresh profile 2 rounds.initHistory predrawSitesFinite

/-- Zero fuel still admits the same nontrivial finite-table draw. -/
example (start : rounds.History) :
    (targetPolicy.toMixedOn {0, 1} fallback).bind
        (fun policy => model.runBehavioralFrom
          (Profile.update profile true policy.toBehavioral) 0 start) =
      model.runBehavioralFrom profile 0 start := by
  simpa only [show targetPolicy = profile true from rfl, Profile.update_eq_self] using
    model.runBehavioralFrom_predrawOneOn true fresh profile 0 targetPolicy
      {0, 1} fallback start targetPolicy_finite

theorem terminalHistory_terminal : rounds.terminal terminalHistory.state := by
  simp [rounds, terminalHistory, firstHistory]

/-- Starting at a terminal history is absorbed for every horizon. -/
example (fuel : Nat) :
    (targetPolicy.toMixedOn {0, 1} fallback).bind
        (fun policy => model.runBehavioralFrom
          (Profile.update profile true policy.toBehavioral) fuel terminalHistory) =
      PMF.pure terminalHistory := by
  have heq := model.runBehavioralFrom_predrawOneOn true fresh profile fuel targetPolicy
    {0, 1} fallback terminalHistory targetPolicy_finite
  rw [model.runBehavioralFrom_of_terminal _ _ terminalHistory_terminal] at heq
  exact heq

end GameTheory.Tests.Predraw
