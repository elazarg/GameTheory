/- Copyright (c) 2026 GameTheory contributors. All rights reserved. -/

import GameTheory.Protocol.Continuation
import GameTheory.Protocol.Zermelo
import GameTheory.Protocol.ContinuationLaw

/-! # A lottery deviation at an off-path proper subgame

The incumbent exits immediately. If it enters instead, the target admits a
fair lottery in addition to the source's two deterministic choices. Coverage
therefore needs a genuine mixture, including at the off-path decision root.
-/

noncomputable section

namespace GameTheory.Tests.ContinuationMixture

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

inductive State where
  | root | decision | done (value : Option Bool)
  deriving DecidableEq

def coin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure false) (FinDist.pure true)

def choiceLaw (action : Fin 3) : FinDist Bool :=
  if action = 0 then FinDist.pure false
  else if action = 1 then FinDist.pure true else coin

def rank : State → ℕ
  | .root => 2
  | .decision => 1
  | .done _ => 0

def allowed (lottery : Bool) (state : State) (action : Fin 3) : Prop :=
  action < 2 ∨ (lottery = true ∧ state = .decision)

@[reducible] def arena (lottery : Bool) : ExecutionProtocol Unit where
  State := State
  Action _ := Fin 3
  init := .root
  active state _ := 0 < rank state
  available state _ := {action | allowed lottery state action}
  terminal state := rank state = 0
  step state joint := match state with
    | .root => FinDist.pure (if joint.1 () = some 1 then .decision else .done none)
    | .decision => (choiceLaw ((joint.1 ()).getD 0)).map (fun bit => .done (some bit))
    | .done value => FinDist.pure (.done value)
  progress := by
    intro state running
    exact ⟨fun _ => some 0, fun _ => ⟨Nat.pos_of_ne_zero running, Or.inl (by decide)⟩⟩

@[reducible] def signals (lottery : Bool) : InfoSignals (arena lottery) where
  PublicSignal := State
  PrivateSignal _ := Unit
  initialPublic := .root
  initialPrivate _ := ()
  publicSignal event := event.target
  privateSignal _ _ := ()
  InfoState _ := State
  initInfo _ _ state := state
  pushInfo _ _ _ _ state := state

@[simp] theorem info_state (lottery : Bool) : ∀ {state : State}
    (trace : (arena lottery).Trace state), (signals lottery).infoOf () trace = state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def menu (lottery : Bool) (state : State) : Set (Option (Fin 3)) :=
  {choice | match choice with
    | some action => 0 < rank state ∧ allowed lottery state action
    | none => ¬ 0 < rank state}

@[reducible] def model (lottery : Bool) : InformationModel (arena lottery) where
  toInfoSignals := signals lottery
  menu _ := menu lottery
  menu_adequate := by
    intro who state trace choice
    cases who
    rw [info_state]
    cases choice <;> rfl

theorem rank_decreases (lottery : Bool) (before after : State)
    (step : (arena lottery).Successor after before) : rank after < rank before := by
  obtain ⟨joint, legal, reached⟩ := step
  cases before with
  | root =>
      have eq := FinDist.mem_support_pure.mp reached
      subst after
      split <;> decide
  | decision =>
      rw [FinDist.support_map] at reached
      obtain ⟨bit, _, rfl⟩ := reached
      norm_num [rank]
  | done value => exact False.elim (legal.1 rfl)

theorem terminates (lottery : Bool) : (arena lottery).WellFoundedPlay :=
  wellFoundedPlay_of_rank rank (rank_decreases lottery)

theorem trace_rank (lottery : Bool) : ∀ {state : State} (trace : (arena lottery).Trace state),
    trace.length + rank state ≤ 2
  | _, .start => by simp [Trace.length, rank]
  | _, .extend prior joint legal reached => by
      have previous := trace_rank lottery prior
      have decreased := rank_decreases lottery _ _ ⟨joint, legal, reached⟩
      simp only [Trace.length]
      omega

theorem bounded (lottery : Bool) : (arena lottery).BoundedHorizon 2 := by
  intro state trace enough
  have h := trace_rank lottery trace
  show rank state = 0
  omega

def decisionRoot (lottery : Bool) : (arena lottery).History :=
  (arena lottery).initHistory.extend (joint := fun _ => some 1)
    (by show (arena lottery).Legal .root _
        exact ⟨by simp [rank], fun _ => ⟨by simp [rank], Or.inl (by norm_num)⟩⟩)
    (target := .decision) (by simp [arena])

theorem history_root (lottery : Bool) : ∀ {state : State} (trace : (arena lottery).Trace state),
    state = .root → (⟨state, trace⟩ : (arena lottery).History) = (arena lottery).initHistory
  | _, .start, _ => rfl
  | _, .extend (source := before) _ joint legal reached, eq => by
      subst_vars
      have decreased := rank_decreases lottery before .root ⟨joint, legal, reached⟩
      have upper : rank before ≤ 2 := by cases before <;> simp [rank]
      have decreased : 2 < rank before := decreased
      omega

theorem history_decision (lottery : Bool) : ∀ {state : State} (trace : (arena lottery).Trace state),
    state = .decision → (⟨state, trace⟩ : (arena lottery).History) = decisionRoot lottery
  | _, .start, eq => by cases eq
  | _, .extend (source := before) prior joint legal reached, eq => by
      subst_vars
      cases before with
      | root =>
          have selected : joint () = some 1 := by
            by_contra h
            simp [arena, h] at reached
          have jointEq : joint = fun _ => some 1 := by funext who; cases who; exact selected
          subst joint
          have priorEq := history_root lottery prior rfl
          have traceEq : prior = .start := by cases priorEq; rfl
          rw [traceEq]
          rfl
      | decision =>
          rw [FinDist.support_map] at reached
          obtain ⟨bit, _, impossible⟩ := reached
          cases impossible
      | done value => exact False.elim (legal.1 rfl)

theorem every_root (lottery : Bool) (root : (arena lottery).History) :
    (model lottery).IsSubgameRoot root := by
  apply (model lottery).isSubgameRoot_of_separatesDecisionHistories _ root
  intro who first second firstRunning _ _ _ same
  cases who
  have states : first.state = second.state := by simpa using same
  rcases first with ⟨firstState, firstTrace⟩
  rcases second with ⟨secondState, secondTrace⟩
  dsimp only at states
  subst secondState
  cases firstState with
  | root =>
      exact (history_root lottery firstTrace rfl).trans
        (history_root lottery secondTrace rfl).symm
  | decision =>
      exact (history_decision lottery firstTrace rfl).trans
        (history_decision lottery secondTrace rfl).symm
  | done value => exact False.elim (firstRunning rfl)

def rootAt (lottery : Bool) : State → (arena lottery).History
  | .root => (arena lottery).initHistory
  | .decision => decisionRoot lottery
  | .done none => (arena lottery).initHistory.extend (joint := fun _ => some 0)
      (by show (arena lottery).Legal .root _
          exact ⟨by simp [rank], fun _ => ⟨by simp [rank], Or.inl (by norm_num)⟩⟩)
      (target := .done none) (by simp [arena])
  | .done (some bit) => (decisionRoot lottery).extend
      (joint := fun _ => some (if bit then 1 else 0))
      (by show (arena lottery).Legal .decision _
          cases bit <;> exact ⟨by simp [rank], fun _ => ⟨by simp [rank], Or.inl (by norm_num)⟩⟩)
      (target := .done (some bit)) (by
        show State.done (some bit) ∈ ((choiceLaw (if bit then 1 else 0)).map _).support
        cases bit <;> simp [choiceLaw])

@[simp] theorem rootAt_state (lottery : Bool) (state : State) :
    (rootAt lottery state).state = state := by
  cases state with
  | root => rfl
  | decision => rfl
  | done value => cases value <;> rfl

def policy (lottery : Bool) (enter bit : Bool) : (model lottery).Policy () := fun state =>
  match state with
  | .root => ⟨some (if enter then 1 else 0), by cases enter <;> simp [menu, rank, allowed]⟩
  | .decision => ⟨some (if bit then 1 else 0), by cases bit <;> simp [menu, rank, allowed]⟩
  | .done _ => ⟨none, by simp [menu, rank]⟩

def compile (_who : Unit) (original : (model false).Policy ()) : (model true).Policy () :=
  fun state => ⟨(original state).1, by
    have legal := (original state).2
    cases selected : (original state).1 with
    | none => simpa [menu, selected] using legal
    | some action =>
        show 0 < rank state ∧ allowed true state action
        have authorized : 0 < rank state ∧ allowed false state action := by
          simpa [menu, selected] using legal
        exact ⟨authorized.1, Or.inl (by simpa [allowed] using authorized.2)⟩⟩

def profile (lottery : Bool) : Profile (model lottery).strategicSignature :=
  fun _ => policy lottery false true

def selected {lottery : Bool} (profile : Profile (model lottery).strategicSignature)
    (state : State) : Fin 3 := ((profile ()).act state).getD 0

def readout : State → Option Bool
  | .done value => value
  | _ => none

def law {lottery : Bool} (profile : Profile (model lottery).strategicSignature) :
    State → FinDist (Option Bool)
  | .root => if selected profile .root = 1 then (choiceLaw (selected profile .decision)).map some
      else FinDist.pure none
  | .decision => (choiceLaw (selected profile .decision)).map some
  | .done value => FinDist.pure value

theorem run_law {lottery : Bool} (profile : Profile (model lottery).strategicSignature)
    (history : (arena lottery).History) :
    ((model lottery).runFrom profile 2 history).map (fun final => readout final.state) =
      law profile history.state := by
  rw [InformationModel.runFrom, ← (arena lottery).runRandomizedFor_toRandomized]
  apply runRandomizedFor_readout_eq ((model lottery).historyChooser profile).toRandomized
    rank (fun _ stopped => stopped)
    (fun history joint after reached => rank_decreases lottery history.state after
      ⟨joint.1, joint.2, reached⟩) readout (law profile)
  · intro state stopped
    cases state <;> simp_all [rank, law, readout]
  · intro history running
    simp only [HistoryChooser.toRandomized, FinDist.pure_bind]
    rcases history with ⟨state, trace⟩
    cases state with
    | root =>
        simp only [InformationModel.historyChooser, InformationModel.jointAt,
          info_state, arena, FinDist.pure_bind]
        cases chosen : (profile ()).act .root with
        | none => simp [chosen, law, selected]
        | some action => by_cases h : action = 1 <;> simp [chosen, law, selected, h]
    | decision =>
        simp [InformationModel.historyChooser, InformationModel.jointAt,
          FinDist.bind_map, law, selected]
        rfl
    | done value => exact False.elim (running rfl)
  · cases history.state <;> simp [rank]

@[simp] theorem compile_profile :
    Profile.map (target := (model true).strategicSignature) compile (profile false) =
      profile true := by
  funext who state
  apply Subtype.ext
  cases state <;> rfl

theorem law_profile (lottery : Bool) (state : State) :
    law (profile lottery) state = FinDist.pure (match state with
      | .root => none | .decision => some true | .done value => value) := by
  cases state <;> simp [law, selected, profile, policy, InformationModel.Policy.act, choiceLaw]

theorem law_replacement (enter bit : Bool) (state : State) :
    law (Profile.update (profile false) () (policy false enter bit)) state =
      FinDist.pure (match state with
        | .root => if enter then some bit else none
        | .decision => some bit
        | .done value => value) := by
  cases state <;> cases enter <;> cases bit <;>
    simp [law, selected, Profile.update_same, policy, InformationModel.Policy.act, choiceLaw]

theorem deviation_law (alternative : (model true).Policy ()) (state : State) :
    law (Profile.update (profile true) () alternative) state =
      ((choiceLaw ((alternative.act .decision).getD 0)).map
        (policy false (decide (alternative.act .root = some 1)))).bind fun replacement =>
        law (Profile.update (profile false) () replacement) state := by
  rw [FinDist.bind_map]
  simp only [law_replacement]
  cases state with
  | root =>
      simp only [law, selected, Profile.update_same]
      cases chosen : alternative.act .root with
      | none => simp
      | some action =>
          by_cases h : action = 1
          · simp only [Option.getD_some, h, ↓reduceIte, decide_true]
            rfl
          · simp [h]
  | decision => rfl
  | done value => simp [law]

theorem coverage : ∀ targetRoot, (model true).IsSubgameRoot targetRoot →
    ∃ sourceRoot, (model false).IsSubgameRoot sourceRoot ∧
      ((model true).runFrom
        (Profile.map (target := (model true).strategicSignature) compile (profile false))
          2 targetRoot).map
        (fun history => readout history.state) =
      ((model false).runFrom (profile false) 2 sourceRoot).map
        (fun history => readout history.state) ∧
      ∀ who (alternative : (model true).Policy who), ∃ mixture : FinDist ((model false).Policy who),
        ((model true).runFrom
          (Profile.update
            (Profile.map (target := (model true).strategicSignature) compile (profile false))
            who alternative) 2 targetRoot).map
            (fun history => readout history.state) =
        mixture.bind fun replacement =>
          ((model false).runFrom (Profile.update (profile false) who replacement) 2 sourceRoot).map
            (fun history => readout history.state) := by
  intro targetRoot _
  refine ⟨rootAt false targetRoot.state, every_root false _, ?_, ?_⟩
  · rw [compile_profile, run_law, run_law, rootAt_state, law_profile, law_profile]
  · intro who alternative
    cases who
    refine ⟨(choiceLaw ((alternative.act .decision).getD 0)).map
      (policy false (decide (alternative.act .root = some 1))), ?_⟩
    simp only [compile_profile, run_law, rootAt_state]
    exact deviation_law alternative targetRoot.state

def lotteryPolicy : (model true).Policy ()
  | .root => ⟨some 0, by simp [menu, rank, allowed]⟩
  | .decision => ⟨some 2, by simp [menu, rank, allowed]⟩
  | .done _ => ⟨none, by simp [menu, rank]⟩

theorem lottery_not_pure (bit : Bool) : coin.map some ≠ FinDist.pure (some bit) := by
  intro eq
  have recovered : coin = FinDist.pure bit := by
    have mapped := congrArg (FinDist.map (fun value : Option Bool => value.getD false)) eq
    simp only [FinDist.map_comp, FinDist.map_pure, Function.comp_def, Option.getD_some] at mapped
    have mapped : FinDist.map id coin = FinDist.pure bit := mapped
    rwa [FinDist.map_id] at mapped
  have masses := congrArg (fun law => law.prob (!bit)) recovered
  cases bit <;>
    norm_num [coin, FinDist.prob_mix, FinDist.prob_pure_eq_ite] at masses

/-- The target lottery cannot be covered by a single source replacement. -/
theorem lottery_requires_mixture (alternative : (model false).Policy ()) :
    ((model true).runFrom (Profile.update (profile true) () lotteryPolicy) 2
      (decisionRoot true)).map (fun history => readout history.state) ≠
    ((model false).runFrom (Profile.update (profile false) () alternative) 2
      (decisionRoot false)).map (fun history => readout history.state) := by
  rw [run_law, run_law]
  show coin.map some ≠ (choiceLaw ((alternative.act .decision).getD 0)).map some
  have authorized := alternative.act_mem_menu .decision
  cases chosen : alternative.act .decision with
  | none => simp [chosen, menu, rank] at authorized
  | some action =>
      fin_cases action
      · simpa [choiceLaw] using lottery_not_pure false
      · simpa [choiceLaw] using lottery_not_pure true
      · simp [chosen, menu, allowed] at authorized

theorem incumbent_run_one (lottery : Bool) :
    (model lottery).run (profile lottery) 1 =
      FinDist.pure (rootAt lottery (.done none)) := by
  have running : ¬ (arena lottery).terminal (arena lottery).initHistory.state := by
    show 2 ≠ 0
    decide
  have step : (arena lottery).step (arena lottery).initHistory.state
      ((model lottery).historyChooser (profile lottery) (arena lottery).initHistory running) =
        FinDist.pure (.done none) := rfl
  rw [InformationModel.run, InformationModel.runFrom,
    runHistoryFor_succ_of_not_terminal _ 0 running]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun _ => FinDist.pure (rootAt lottery (.done none)))]
  · exact FinDist.bind_const _ _
  · intro state reached
    have stateEq : state = .done none := by
      rwa [step, FinDist.mem_support_pure] at reached
    subst state
    rw [runHistoryFor_zero]
    congr 1

/-- Entering is legal, but the incumbent has already exited at this depth. -/
theorem decision_offPath (lottery : Bool) :
    (model lottery).IsSubgameRoot (decisionRoot lottery) ∧
      decisionRoot lottery ∉ ((model lottery).run (profile lottery) 1).support := by
  refine ⟨every_root lottery _, ?_⟩
  rw [incumbent_run_one, FinDist.mem_support_pure]
  intro eq
  have states := congrArg History.state eq
  have states : State.decision = .done none := states
  cases states

def utility : Option Bool → Unit → ℝ
  | none, _ => 2
  | some true, _ => 1
  | some false, _ => 0

theorem value_law {lottery : Bool} (policies : Profile (model lottery).strategicSignature)
    (history : (arena lottery).History) :
    (arena lottery).historyBackwardValue (terminates lottery)
      ((model lottery).historyChooser policies) (fun final => utility (readout final.state) ())
      history = (law policies history.state).expect (utility · ()) := by
  rw [(model lottery).historyBackwardValue_eq_expect_runFrom_of_bound
    (terminates lottery) (bounded lottery)]
  rw [← FinDist.expect_map (fun final : (arena lottery).History => readout final.state)
    ((model lottery).runFrom policies 2 history) (utility · ()), run_law]

theorem sourcePerfect : (model false).IsSubgamePerfect (terminates false) (profile false)
    (fun history who => utility (readout history.state) who) := by
  apply InformationModel.IsHistorywiseOptimal.isSubgamePerfect
  intro who alternative history
  cases who
  rw [value_law, value_law, law_profile, FinDist.expect_pure]
  cases history.state with
  | root =>
      apply FinDist.expect_le_of_forall
      intro outcome _
      cases outcome with
      | none => norm_num [utility]
      | some bit => cases bit <;> norm_num [utility]
  | decision =>
      simp only [law, FinDist.expect_map]
      apply FinDist.expect_le_of_forall
      intro bit _
      cases bit <;> norm_num [utility]
  | done value => simp [law]

/-- The nonidentity compiler preserves SPE at every target root. Its coverage
uses both pure source choices to realize the additional lottery deviation. -/
theorem targetPerfect : (model true).IsSubgamePerfect (terminates true) (profile true)
    (fun history who => utility (readout history.state) who) := by
  rw [← compile_profile]
  exact (model false).isSubgamePerfect_of_continuation_laws (model true)
    (terminates false) (terminates true) (bounded false) (bounded true) compile
    (fun history => readout history.state) (fun history => readout history.state)
    (profile false) coverage utility sourcePerfect

end GameTheory.Tests.ContinuationMixture
