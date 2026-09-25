/- Copyright (c) 2026 GameTheory contributors. All rights reserved. -/

import GameTheory.Protocol.Continuation
import GameTheory.Protocol.Zermelo
import GameTheory.Protocol.ContinuationLaw
import GameTheory.Math.Probability.Uniform

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

def coin : PMF Bool :=
  PMF.uniformOfFintype Bool

def choiceLaw (action : Fin 3) : PMF Bool :=
  if action = 0 then PMF.pure false
  else if action = 1 then PMF.pure true else coin

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
    | .root => PMF.pure (if joint.1 () = some 1 then .decision else .done none)
    | .decision => (choiceLaw ((joint.1 ()).getD 0)).map (fun bit => .done (some bit))
    | .done value => PMF.pure (.done value)
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
      rw [PMF.mem_support_pure_iff] at reached
      have eq := reached
      subst after
      split <;> decide
  | decision =>
      rw [PMF.support_map] at reached
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
          rw [PMF.support_map] at reached
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
    State → PMF (Option Bool)
  | .root => if selected profile .root = 1 then (choiceLaw (selected profile .decision)).map some
      else PMF.pure none
  | .decision => (choiceLaw (selected profile .decision)).map some
  | .done value => PMF.pure value

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
    simp only [HistoryChooser.toRandomized, PMF.pure_bind]
    rcases history with ⟨state, trace⟩
    cases state with
    | root =>
        simp only [InformationModel.historyChooser, InformationModel.jointAt,
          info_state, arena, PMF.pure_bind]
        cases chosen : (profile ()).act .root with
        | none => simp [chosen, law, selected]
        | some action => by_cases h : action = 1 <;> simp [chosen, law, selected, h]
    | decision =>
        simp [InformationModel.historyChooser, InformationModel.jointAt,
          PMF.bind_map, law, selected]
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
    law (profile lottery) state = PMF.pure (match state with
      | .root => none | .decision => some true | .done value => value) := by
  cases state <;> simp [law, selected, profile, policy, InformationModel.Policy.act,
    choiceLaw, PMF.pure_map]

theorem law_replacement (enter bit : Bool) (state : State) :
    law (Profile.update (profile false) () (policy false enter bit)) state =
      PMF.pure (match state with
        | .root => if enter then some bit else none
        | .decision => some bit
        | .done value => value) := by
  cases state <;> cases enter <;> cases bit <;>
    simp [law, selected, Profile.update_same, policy, InformationModel.Policy.act,
      choiceLaw, PMF.pure_map]

theorem deviation_law (alternative : (model true).Policy ()) (state : State) :
    law (Profile.update (profile true) () alternative) state =
      ((choiceLaw ((alternative.act .decision).getD 0)).map
        (policy false (decide (alternative.act .root = some 1)))).bind fun replacement =>
        law (Profile.update (profile false) () replacement) state := by
  rw [PMF.bind_map]
  simp only [Function.comp_def, law_replacement]
  cases state with
  | root =>
      simp only [law, selected, Profile.update_same]
      cases chosen : alternative.act .root with
      | none =>
          simp [InformationModel.Policy.act]
      | some action =>
          by_cases h : action = 1
          · simp only [h, InformationModel.Policy.act]
            exact (PMF.bind_pure_comp some _).symm
          · simp [h, InformationModel.Policy.act]
  | decision =>
      simp only [law, selected, Profile.update_same, InformationModel.Policy.act]
      exact (PMF.bind_pure_comp some _).symm
  | done value => simp [law]

theorem coverage : ∀ targetRoot, (model true).IsSubgameRoot targetRoot →
    ∃ sourceRoot, (model false).IsSubgameRoot sourceRoot ∧
      ((model true).runFrom
        (Profile.map (target := (model true).strategicSignature) compile (profile false))
          2 targetRoot).map
        (fun history => readout history.state) =
      ((model false).runFrom (profile false) 2 sourceRoot).map
        (fun history => readout history.state) ∧
      ∀ who (alternative : (model true).Policy who), ∃ mixture : PMF ((model false).Policy who),
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

theorem lottery_not_pure (bit : Bool) : coin.map some ≠ PMF.pure (some bit) := by
  intro heq
  have hsupport : some (!bit) ∈ (coin.map some).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨!bit, PMF.mem_support_uniformOfFintype _, rfl⟩
  rw [heq, PMF.mem_support_pure_iff] at hsupport
  cases bit <;> cases hsupport

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
      · simpa [choiceLaw, PMF.pure_map] using lottery_not_pure false
      · simpa [choiceLaw, PMF.pure_map] using lottery_not_pure true
      · simp [chosen, menu, allowed] at authorized

theorem incumbent_run_one (lottery : Bool) :
    (model lottery).run (profile lottery) 1 =
      PMF.pure (rootAt lottery (.done none)) := by
  have running : ¬ (arena lottery).terminal (arena lottery).initHistory.state := by
    show 2 ≠ 0
    decide
  have step : (arena lottery).step (arena lottery).initHistory.state
      ((model lottery).historyChooser (profile lottery) (arena lottery).initHistory running) =
        PMF.pure (.done none) := rfl
  rw [InformationModel.run, InformationModel.runFrom,
    runHistoryFor_succ_of_not_terminal _ 0 running]
  calc
    _ = ((arena lottery).step (arena lottery).initHistory.state
          ((model lottery).historyChooser (profile lottery)
            (arena lottery).initHistory running)).bind
          (fun _ => PMF.pure (rootAt lottery (.done none))) := by
        apply bindOnSupport_eq_bind_of_eq_on_support
        intro state reached
        have stateEq : state = .done none := by
          rw [step, PMF.mem_support_pure_iff] at reached
          exact reached
        subst state
        rw [runHistoryFor_zero]
        congr 1
    _ = _ := PMF.bind_const _ _

/-- Entering is legal, but the incumbent has already exited at this depth. -/
theorem decision_offPath (lottery : Bool) :
    (model lottery).IsSubgameRoot (decisionRoot lottery) ∧
      decisionRoot lottery ∉ ((model lottery).run (profile lottery) 1).support := by
  refine ⟨every_root lottery _, ?_⟩
  rw [incumbent_run_one, PMF.mem_support_pure_iff]
  intro eq
  have states := congrArg History.state eq
  have states : State.decision = .done none := states
  cases states

def utility : Option Bool → Unit → ℝ
  | none, _ => 2
  | some true, _ => 1
  | some false, _ => 0

private theorem utility_bound (result : Option Bool) : |utility result ()| ≤ 2 := by
  cases result with
  | none => norm_num [utility]
  | some bit => cases bit <;> norm_num [utility]

private theorem history_utility_guard {lottery : Bool}
    (law : PMF (arena lottery).History) :
    PayoffIntegrable law (fun final => utility (readout final.state) ()) := by
  apply payoffIntegrable_of_bounded law _ (C := 2)
  intro final
  exact utility_bound _

/-- The guarded backward value has the explicitly calculated public law. -/
theorem value_law {lottery : Bool} (certificate : (arena lottery).WellFoundedPlay)
    (policies : Profile (model lottery).strategicSignature)
    (history : (arena lottery).History)
    (hback : PayoffIntegrable
      ((arena lottery).historyBackwardLaw certificate
        ((model lottery).historyChooser policies) history)
      (fun final => utility (readout final.state) ()))
    (hlaw : PayoffIntegrable (law policies history.state) (utility · ())) :
    (arena lottery).historyBackwardValue certificate
      ((model lottery).historyChooser policies)
      (fun final => utility (readout final.state) ()) history hback =
        expect (law policies history.state) (utility · ()) hlaw := by
  let hrun := history_utility_guard ((model lottery).runFrom policies 2 history)
  have hlawRun :
      (((model lottery).runFrom policies 2 history).map
        (fun final => readout final.state)) =
      (law policies history.state).map id := by
    simpa only [PMF.map_id] using run_law policies history
  calc
    _ = expect ((model lottery).runFrom policies 2 history)
        (fun final => utility (readout final.state) ()) hrun :=
      (model lottery).historyBackwardValue_eq_expect_runFrom_of_bound
        certificate (bounded lottery) policies _ history hback hrun
    _ = expect (law policies history.state) (utility · ()) hlaw := by
      exact expect_observed_law_eq
        ((model lottery).runFrom policies 2 history) (law policies history.state)
        (fun final => readout final.state) id (utility · ()) hlawRun hrun hlaw

private theorem source_law_bound (alternative : (model false).Policy ())
    (state : State) :
    expect (law (Profile.update (profile false) () alternative) state)
        (utility · ()) (payoffIntegrable_of_finite _ _) ≤
      expect (law (profile false) state) (utility · ())
        (payoffIntegrable_of_finite _ _) := by
  cases state with
  | root =>
      calc
        _ ≤ expect (law (Profile.update (profile false) () alternative) .root)
            (fun _ => (2 : ℝ)) (payoffIntegrable_constant _ _) := by
          apply expect_mono
          intro result _
          exact le_trans (le_abs_self _) (utility_bound result)
        _ = 2 := expect_constant _ _ _
        _ = _ := by rw [law_profile]; simp [utility, expect_pure]
  | decision =>
      have hsup : ∀ result ∈
          (law (Profile.update (profile false) () alternative) .decision).support,
          utility result () ≤ 1 := by
        intro result hresult
        simp only [law, PMF.support_map] at hresult
        obtain ⟨bit, _, rfl⟩ := hresult
        cases bit <;> norm_num [utility]
      calc
        _ ≤ expect (law (Profile.update (profile false) () alternative) .decision)
            (fun _ => (1 : ℝ)) (payoffIntegrable_constant _ _) := by
          exact expect_mono hsup (payoffIntegrable_of_finite _ _)
            (payoffIntegrable_constant _ _)
        _ = 1 := expect_constant _ _ _
        _ = _ := by rw [law_profile]; simp [utility, expect_pure]
  | done value =>
      simp [law, expect_pure]

theorem sourcePerfect : (model false).IsSubgamePerfect (terminates false) (profile false)
    (fun history who => utility (readout history.state) who) := by
  apply ((model false).isSubgamePerfect_iff_isNash_continuation
    (terminates false) (bounded false) (profile false)
    (fun history who => utility (readout history.state) who)).mpr
  intro history _
  rw [isNash_iff]
  intro who alternative
  cases who
  let hrdev := history_utility_guard
    ((model false).runFrom (Profile.update (profile false) () alternative) 2 history)
  let hrbase := history_utility_guard ((model false).runFrom (profile false) 2 history)
  refine ⟨hrbase, hrdev, ?_⟩
  let hldev := payoffIntegrable_of_finite
    (law (Profile.update (profile false) () alternative) history.state) (utility · ())
  let hlbase := payoffIntegrable_of_finite (law (profile false) history.state) (utility · ())
  simp only [InformationModel.toContinuationGameForm, expectedUtility]
  have hdevValue : expect
      ((model false).runFrom (Profile.update (profile false) () alternative) 2 history)
      (fun final => utility (readout final.state) ()) hrdev =
        expect (law (Profile.update (profile false) () alternative) history.state)
          (utility · ()) hldev := by
    have hlaw :
        (((model false).runFrom
          (Profile.update (profile false) () alternative) 2 history).map
          (fun final => readout final.state)) =
        (law (Profile.update (profile false) () alternative) history.state).map id := by
      simpa only [PMF.map_id] using
        run_law (Profile.update (profile false) () alternative) history
    exact expect_observed_law_eq
      ((model false).runFrom (Profile.update (profile false) () alternative) 2 history)
      (law (Profile.update (profile false) () alternative) history.state)
      (fun final => readout final.state) id (utility · ()) hlaw hrdev hldev
  have hbaseValue : expect ((model false).runFrom (profile false) 2 history)
      (fun final => utility (readout final.state) ()) hrbase =
        expect (law (profile false) history.state) (utility · ()) hlbase := by
    have hlaw :
        (((model false).runFrom (profile false) 2 history).map
          (fun final => readout final.state)) =
        (law (profile false) history.state).map id := by
      simpa only [PMF.map_id] using run_law (profile false) history
    exact expect_observed_law_eq
      ((model false).runFrom (profile false) 2 history)
      (law (profile false) history.state)
      (fun final => readout final.state) id (utility · ()) hlaw hrbase hlbase
  calc
    _ = expect (law (Profile.update (profile false) () alternative) history.state)
        (utility · ()) hldev := hdevValue
    _ ≤ expect (law (profile false) history.state) (utility · ()) hlbase :=
      source_law_bound alternative history.state
    _ = _ := hbaseValue.symm

/-- The nonidentity compiler preserves SPE at every target root. Its coverage
uses both pure source choices to realize the additional lottery deviation. -/
theorem targetPerfect : (model true).IsSubgamePerfect (terminates true) (profile true)
    (fun history who => utility (readout history.state) who) := by
  rw [← compile_profile]
  exact (model false).isSubgamePerfect_of_continuation_laws (model true)
    (terminates false) (terminates true) (bounded false) (bounded true) compile
    (fun history => readout history.state) (fun history => readout history.state)
    (profile false) coverage utility
    (fun _ _ _ _ => history_utility_guard _) sourcePerfect

end GameTheory.Tests.ContinuationMixture
