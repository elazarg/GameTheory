/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.Zermelo

/-! # Irreversible failure before a later decision

Four atomic decisions: seal A, choose B, disclose A, disclose B. The source
requires an openable A; the target also permits sealing an unopenable A.
There is no preparation step, computation cost, deadline, or network here.
Utilities depend only on the two public results. This isolates the strategic
effect of early irreversible failure; it is not a serviced-runtime adapter.
-/

noncomputable section

namespace GameTheory.Tests.IrreversibleFailure

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

/-- Reverse chronological decisions, retained as the player's own recall. -/
abbrev State := List Bool

def allowed (source : Bool) (state : State) : Set Bool :=
  if source = true ∧ state = [] then {true} else Set.univ

@[reducible] def arena (source : Bool) : ExecutionProtocol Unit where
  State := State
  Action _ := Bool
  init := []
  active state _ := state.length < 4
  available state _ := allowed source state
  terminal state := 4 ≤ state.length
  step state joint := FinDist.pure ((joint.1 ()).getD false :: state)
  progress := by
    intro state running
    refine ⟨fun _ => some true, fun _ => ?_⟩
    exact ⟨by omega, by simp only [allowed]; split <;> simp⟩

@[reducible] def signals (source : Bool) : InfoSignals (arena source) where
  PublicSignal := Unit
  PrivateSignal _ := State
  initialPublic := ()
  initialPrivate _ := []
  publicSignal _ := ()
  privateSignal _ event := event.target
  InfoState _ := State
  initInfo _ secret _ := secret
  pushInfo _ _ _ secret _ := secret

@[simp] theorem info_state (source : Bool) : ∀ {state : (arena source).State}
    (trace : (arena source).Trace state),
    (signals source).infoOf () trace = state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def menu (source : Bool) (state : State) : Set (Option Bool) :=
  {choice | match choice with
    | some action => state.length < 4 ∧ action ∈ allowed source state
    | none => ¬ state.length < 4}

@[reducible] def model (source : Bool) : InformationModel (arena source) where
  toInfoSignals := signals source
  menu _ := menu source
  menu_adequate := by
    intro who state trace choice
    cases who
    rw [info_state]
    cases choice <;> rfl

theorem rank_decreases (source : Bool) (before after : State)
    (step : (arena source).Successor after before) :
    4 - after.length < 4 - before.length := by
  obtain ⟨joint, legal, reached⟩ := step
  have running : before.length < 4 := by
    have stopped : ¬ 4 ≤ before.length := legal.1
    omega
  have eq := FinDist.mem_support_pure.mp reached
  subst after
  simp only [List.length_cons]
  omega

theorem terminates (source : Bool) : (arena source).WellFoundedPlay :=
  wellFoundedPlay_of_rank (fun state => 4 - state.length) (rank_decreases source)

theorem history_length (source : Bool) : ∀ {state : State} (trace : (arena source).Trace state),
    trace.length = state.length
  | _, .start => rfl
  | _, .extend prior joint _ reached => by
      have stateEq := FinDist.mem_support_pure.mp reached
      subst_vars
      simpa only [Trace.length, List.length_cons] using
        congrArg (· + 1) (history_length source prior)

theorem bounded (source : Bool) : (arena source).BoundedHorizon 4 := by
  intro state trace enough
  show 4 ≤ state.length
  rw [← history_length source trace]
  exact enough

def outcome (state : State) : Bool × Option Bool :=
  match state with
  | [openB, openA, choice, valid] => (valid && openA, if openB then some choice else none)
  | _ => (false, none)

def utility (prefer : Bool) (result : Bool × Option Bool) : ℝ :=
  match result.2 with
  | none => 0
  | some choice => if result.1 then 3 else if choice = prefer then 2 else 1

def payoff (source prefer : Bool) (history : (arena source).History) (_ : Unit) : ℝ :=
  utility prefer (outcome history.state)

def pick {source : Bool} (profile : Profile (model source).strategicSignature)
    (state : State) : Bool := ((profile ()).act state).getD false

/-- Closed-form terminal payoff after the remaining at most four decisions. -/
def continuationPayoff {source : Bool} (profile : Profile (model source).strategicSignature)
    (prefer : Bool) (state : State) : ℝ :=
  match state with
  | [] =>
      let valid := pick profile []
      let choice := pick profile [valid]
      let openA := pick profile [choice, valid]
      utility prefer (outcome [pick profile [openA, choice, valid], openA, choice, valid])
  | [valid] =>
      let choice := pick profile [valid]
      let openA := pick profile [choice, valid]
      utility prefer (outcome [pick profile [openA, choice, valid], openA, choice, valid])
  | [choice, valid] =>
      let openA := pick profile [choice, valid]
      utility prefer (outcome [pick profile [openA, choice, valid], openA, choice, valid])
  | [openA, choice, valid] =>
      utility prefer (outcome [pick profile [openA, choice, valid], openA, choice, valid])
  | _ => utility prefer (outcome state)

theorem continuationPayoff_step {source : Bool}
    (profile : Profile (model source).strategicSignature) (prefer : Bool)
    (state : State) (running : state.length < 4) :
    continuationPayoff profile prefer (pick profile state :: state) =
      continuationPayoff profile prefer state := by
  rcases state with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    simp_all [continuationPayoff]
  omega

theorem continuationPayoff_terminal {source : Bool}
    (profile : Profile (model source).strategicSignature) (prefer : Bool)
    (state : State) (stopped : 4 ≤ state.length) :
    continuationPayoff profile prefer state = utility prefer (outcome state) := by
  rcases state with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    simp_all [continuationPayoff]

/-- The closed form agrees with the canonical history-preserving SPE evaluator. -/
theorem backward_eq {source : Bool} (profile : Profile (model source).strategicSignature)
    (prefer : Bool) (history : (arena source).History) :
    (arena source).historyBackwardValue (terminates source)
      ((model source).historyChooser profile) (fun h => payoff source prefer h ()) history =
        continuationPayoff profile prefer history.state := by
  induction history using ((arena source).wellFounded_historySuccessor
      (terminates source)).induction with
  | _ history ih =>
      by_cases stopped : (arena source).terminal history.state
      · rw [(arena source).historyBackwardValue_of_terminal stopped]
        exact (continuationPayoff_terminal profile prefer history.state stopped).symm
      · rw [(arena source).historyBackwardValue_of_not_terminal stopped]
        have step : (arena source).step history.state
            ((model source).historyChooser profile history stopped) =
              FinDist.pure (pick profile history.state :: history.state) := by
          simp [arena, InformationModel.historyChooser, InformationModel.jointAt, pick]
        rw [(arena source).historyStepValue_of_step_eq_pure step]
        rw [ih _ ⟨_, _, show (pick profile history.state :: history.state) ∈
          ((arena source).step history.state
            ((model source).historyChooser profile history stopped)).support from by
              rw [step]; exact FinDist.mem_support_pure.mpr rfl⟩]
        exact continuationPayoff_step profile prefer history.state (by
          have stopped : ¬ 4 ≤ history.state.length := stopped
          omega)

def sourcePolicy : (model true).Policy () := fun state =>
  if running : state.length < 4 then
    ⟨some (if state.length = 1 then false else true), by
      simp only [menu, Set.mem_ofPred_eq]
      refine ⟨running, ?_⟩
      by_cases empty : state = []
      · simp [allowed, empty]
      · simp only [allowed, and_false, empty, ↓reduceIte, Set.mem_univ]⟩
  else ⟨none, running⟩

def sourceProfile : Profile (model true).strategicSignature := fun _ => sourcePolicy

theorem source_valid : ∀ {state : State} (_trace : (arena true).Trace state),
    state = [] ∨ state.getLast? = some true
  | _, .start => Or.inl rfl
  | _, .extend (source := state) prior joint legal reached => by
      have eq := FinDist.mem_support_pure.mp reached
      subst_vars
      right
      rcases source_valid prior with empty | last
      · subst state
        have authorized := (arena true).legalOption_of_legal legal ()
        cases action : joint () with
        | none => simp [action, LegalOption, arena] at authorized
        | some value =>
            have valueTrue : value = true := by
              simpa [action, LegalOption, arena, allowed] using authorized
            simp [action, valueTrue]
      · simp [List.getLast?_cons, last]

theorem utility_bounds (prefer valid openA openB choice : Bool) :
    0 ≤ utility prefer (outcome [openB, openA, choice, valid]) ∧
      utility prefer (outcome [openB, openA, choice, valid]) ≤ 3 := by
  cases prefer <;> cases valid <;> cases openA <;> cases openB <;> cases choice <;>
    norm_num [utility, outcome]

/-- The same source plan is SPE for both opposite preferences after failure. -/
theorem source_subgamePerfect (prefer : Bool) :
    (model true).IsSubgamePerfect (terminates true) sourceProfile (payoff true prefer) := by
  apply InformationModel.IsHistorywiseOptimal.isSubgamePerfect
  intro who alternative history
  cases who
  rw [backward_eq, backward_eq]
  have valid := source_valid history.trace
  rcases history with ⟨state, trace⟩
  dsimp only at valid ⊢
  rcases state with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  · have first : pick (Profile.update sourceProfile () alternative) [] = true := by
      have authorized := alternative.act_mem_menu []
      cases selected : alternative.act [] <;>
        simp_all [menu, allowed, pick, Profile.update_same]
    simp only [continuationPayoff, first]
    simpa [sourceProfile, sourcePolicy, pick, InformationModel.Policy.act, utility, outcome]
      using (utility_bounds prefer true
        (pick (Profile.update sourceProfile () alternative)
          [pick (Profile.update sourceProfile () alternative) [true], true])
        (pick (Profile.update sourceProfile () alternative)
          [pick (Profile.update sourceProfile () alternative)
            [pick (Profile.update sourceProfile () alternative) [true], true],
            pick (Profile.update sourceProfile () alternative) [true], true])
        (pick (Profile.update sourceProfile () alternative) [true])).2
  · have same : a = true := by simpa using valid
    subst a
    simp only [continuationPayoff]
    have bound := utility_bounds prefer true
      (pick (Profile.update sourceProfile () alternative)
        [pick (Profile.update sourceProfile () alternative) [true], true])
      (pick (Profile.update sourceProfile () alternative)
        [pick (Profile.update sourceProfile () alternative)
          [pick (Profile.update sourceProfile () alternative) [true], true],
          pick (Profile.update sourceProfile () alternative) [true], true])
      (pick (Profile.update sourceProfile () alternative) [true])
    simpa [sourceProfile, sourcePolicy, pick, InformationModel.Policy.act, utility, outcome]
      using bound.2
  · have same : b = true := by simpa using valid
    subst b
    have bound := utility_bounds prefer true
      (pick (Profile.update sourceProfile () alternative) [a, true])
      (pick (Profile.update sourceProfile () alternative)
        [pick (Profile.update sourceProfile () alternative) [a, true], a, true]) a
    simpa [continuationPayoff, sourceProfile, sourcePolicy, pick,
      InformationModel.Policy.act, utility, outcome] using bound.2
  · simp only [continuationPayoff]
    have bound := utility_bounds prefer c a true b
    cases pick (Profile.update sourceProfile () alternative) [a, b, c]
    · simpa [sourceProfile, sourcePolicy, pick, InformationModel.Policy.act,
        utility, outcome] using bound.1
    · simp [sourceProfile, sourcePolicy, pick, InformationModel.Policy.act]
  · exact le_rfl

theorem legal_some {source : Bool} {state : State} {joint : Unit → Option Bool}
    (legal : (arena source).Legal state joint) : ∃ action, joint () = some action := by
  have running : state.length < 4 := by
    have stopped : ¬ 4 ≤ state.length := legal.1
    omega
  exact LegalOption.exists_eq_some_of_active (E := arena source) (joint ())
    ((arena source).legalOption_of_legal legal ()) running

theorem tree_shaped (source : Bool) : (arena source).IsTreeShaped := by
  apply (arena source).isTreeShaped_of_predecessor_unique
  · intro state joint legal
    simp [arena]
  · intro target first second firstJoint secondJoint firstLegal secondLegal firstMem secondMem
    obtain ⟨a, firstChoice⟩ := legal_some firstLegal
    obtain ⟨b, secondChoice⟩ := legal_some secondLegal
    have firstEq : target = a :: first := by simpa [arena, firstChoice] using firstMem
    have secondEq : target = b :: second := by simpa [arena, secondChoice] using secondMem
    have equal := List.cons.inj (firstEq.symm.trans secondEq)
    refine ⟨equal.2, ?_⟩
    funext who
    cases who
    rw [firstChoice, secondChoice, equal.1]

theorem every_history_subgame (source : Bool) (root : (arena source).History) :
    (model source).IsSubgameRoot root := by
  apply (model source).isSubgameRoot_of_separatesDecisionHistories _ root
  intro who first second _ _ _ _ same
  cases who
  have states : first.state = second.state := by simpa using same
  rcases first with ⟨firstState, firstTrace⟩
  rcases second with ⟨secondState, secondTrace⟩
  dsimp only at states
  subst secondState
  have traces := (tree_shaped source firstState).elim firstTrace secondTrace
  cases traces
  rfl

def failedRoot : (arena false).History :=
  (arena false).initHistory.extend
    (joint := fun _ => some false)
    (by exact ⟨by simp [arena], fun _ => ⟨by simp [arena], by simp [allowed]⟩⟩)
    (target := [false]) (FinDist.mem_support_pure.mpr rfl)

/-- The failed-binding continuation is an actual off-path proper subgame. -/
theorem failedRoot_subgame : (model false).IsSubgameRoot failedRoot :=
  every_history_subgame false failedRoot

def targetPolicy (prefer : Bool) : (model false).Policy () := fun state =>
  if running : state.length < 4 then
    ⟨some (if state.length = 1 then prefer else true), by
      exact ⟨running, by simp only [allowed, Bool.false_eq_true, false_and, ↓reduceIte,
        Set.mem_univ]⟩⟩
  else ⟨none, running⟩

theorem failedRoot_best (prefer : Bool) (profile : Profile (model false).strategicSignature) :
    (arena false).historyBackwardValue (terminates false)
      ((model false).historyChooser (Profile.update profile () (targetPolicy prefer)))
      (fun h => payoff false prefer h ()) failedRoot = 2 := by
  rw [backward_eq]
  simp [failedRoot, History.extend, continuationPayoff, pick, Profile.update_same,
    InformationModel.Policy.act, targetPolicy, outcome, utility]

theorem failed_utility_sum (choice : Option Bool) :
    utility false (false, choice) + utility true (false, choice) ≤ 3 := by
  cases choice with
  | none => norm_num [utility]
  | some bit => cases bit <;> norm_num [utility]

theorem failedRoot_value_sum (profile : Profile (model false).strategicSignature) :
    (arena false).historyBackwardValue (terminates false)
        ((model false).historyChooser profile) (fun h => payoff false false h ()) failedRoot +
      (arena false).historyBackwardValue (terminates false)
        ((model false).historyChooser profile) (fun h => payoff false true h ()) failedRoot ≤
      3 := by
  rw [backward_eq, backward_eq]
  simpa only [failedRoot, History.extend, continuationPayoff, outcome, Bool.false_and] using
    failed_utility_sum
      (if pick profile [pick profile [pick profile [false], false], pick profile [false], false]
        then some (pick profile [false]) else none)

/-- No single target plan is SPE for both utilities, although the same source
plan is SPE for both. All target operations in this example are atomic. -/
theorem no_common_target_spe :
    ¬ ∃ profile : Profile (model false).strategicSignature,
      (model false).IsSubgamePerfect (terminates false) profile (payoff false false) ∧
      (model false).IsSubgamePerfect (terminates false) profile (payoff false true) := by
  rintro ⟨profile, first, second⟩
  have firstBound := first failedRoot failedRoot_subgame () (targetPolicy false)
  have secondBound := second failedRoot failedRoot_subgame () (targetPolicy true)
  rw [failedRoot_best] at firstBound secondBound
  have total := failedRoot_value_sum profile
  linarith

/-- A compiler given only the source plan cannot preserve SPE for all public
utilities when it introduces early irreversible failure. -/
theorem no_utility_independent_spe_compiler :
    ¬ ∃ compile : Profile (model true).strategicSignature →
        Profile (model false).strategicSignature,
      ∀ prefer, (model true).IsSubgamePerfect (terminates true) sourceProfile
          (payoff true prefer) →
        (model false).IsSubgamePerfect (terminates false) (compile sourceProfile)
          (payoff false prefer) := by
  rintro ⟨compile, preserves⟩
  exact no_common_target_spe ⟨compile sourceProfile,
    preserves false (source_subgamePerfect false), preserves true (source_subgamePerfect true)⟩

/-- Randomization cannot recover a common optimum after failure either: the
two utilities sum to at most three, while each has an attainable value two. -/
theorem no_randomized_common_completion (law : FinDist (Option Bool)) :
    ¬ (2 ≤ law.expect (fun choice => utility false (false, choice)) ∧
      2 ≤ law.expect (fun choice => utility true (false, choice))) := by
  rintro ⟨first, second⟩
  have total : law.expect (fun choice =>
      utility false (false, choice) + utility true (false, choice)) ≤ 3 :=
    FinDist.expect_le_of_forall _ _ _ (fun choice _ => failed_utility_sum choice)
  rw [FinDist.expect_add] at total
  linarith

end GameTheory.Tests.IrreversibleFailure
