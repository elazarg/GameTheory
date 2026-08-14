/-
# Information-set deviations do not characterize general SPE

Nature privately chooses a bit before one player moves twice.  The player
remembers its first action but never observes nature's bit, so the model has
perfect recall while every noninitial decision history cuts an information
set.  Payoff complementarity makes changing both decisions profitable even
though changing either information-state action alone is not.
-/

import GameTheory.Protocol.SubgamePerfect

noncomputable section

namespace GameTheory.Tests.SubgameOneShot

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Probability

inductive Stage
  | opening
  | first
  | second
  | done
  deriving DecidableEq

inductive State
  | root
  | first (hidden : Bool)
  | second (hidden firstAction : Bool)
  | done (hidden firstAction secondAction : Bool)
  deriving DecidableEq

def State.stage : State → Stage
  | .root => .opening
  | .first _ => .first
  | .second _ _ => .second
  | .done _ _ _ => .done

def State.isDecision : State → Prop
  | .first _ | .second _ _ => True
  | _ => False

def State.isTerminal : State → Prop
  | .done _ _ _ => True
  | _ => False

def natureLaw : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

theorem mem_support_natureLaw (hidden : Bool) :
    hidden ∈ natureLaw.support :=
  FinDist.prob_pos_iff.mp (by
    cases hidden <;>
      norm_num [natureLaw, FinDist.prob_pure_eq_ite])

def chosenAction (joint : Unit → Option Bool) : Bool :=
  (joint ()).getD false

@[reducible]
def twoStage : ExecutionProtocol Unit where
  State := State
  Action _ := Bool
  init := .root
  active state _ := state.isDecision
  available _ _ := Set.univ
  terminal := State.isTerminal
  step state joint :=
    match state with
    | .root => FinDist.map State.first natureLaw
    | .first hidden =>
        FinDist.pure (.second hidden (chosenAction joint.1))
    | .second hidden firstAction =>
        FinDist.pure (.done hidden firstAction (chosenAction joint.1))
    | .done hidden firstAction secondAction =>
        FinDist.pure (.done hidden firstAction secondAction)
  progress := by
    intro state hterm
    cases state with
    | root =>
        exact ⟨fun _ => none, by
          intro who
          cases who
          simp [State.isDecision]⟩
    | first hidden =>
        exact ⟨fun _ => some false, by
          intro who
          cases who
          simp [State.isDecision]⟩
    | second hidden firstAction =>
        exact ⟨fun _ => some false, by
          intro who
          cases who
          simp [State.isDecision]⟩
    | done hidden firstAction secondAction =>
        exact False.elim (hterm trivial)

def moveJoint (action : Bool) : Unit → Option Bool :=
  fun _ => some action

theorem root_not_terminal : ¬ twoStage.terminal .root := by simp [State.isTerminal]

theorem root_inactive (who : Unit) : ¬ twoStage.active .root who := by
  simp [State.isDecision]

theorem root_noop_legal : twoStage.Legal .root twoStage.noop :=
  twoStage.noop_isLegal root_not_terminal root_inactive

theorem first_mem_support (hidden : Bool) :
    State.first hidden ∈
      (twoStage.step .root ⟨twoStage.noop, root_noop_legal⟩).support := by
  rw [FinDist.support_map]
  exact ⟨hidden, mem_support_natureLaw hidden, rfl⟩

def firstHistory (hidden : Bool) : twoStage.History :=
  ⟨.first hidden,
    .extend .start twoStage.noop root_noop_legal
      (first_mem_support hidden)⟩

theorem first_not_terminal (hidden : Bool) :
    ¬ twoStage.terminal (.first hidden) := by simp [State.isTerminal]

theorem second_not_terminal (hidden firstAction : Bool) :
    ¬ twoStage.terminal (.second hidden firstAction) := by
  simp [State.isTerminal]

theorem first_active (hidden : Bool) :
    twoStage.active (firstHistory hidden).state () := by
  exact trivial

theorem moveJoint_legal_first (hidden action : Bool) :
    twoStage.Legal (.first hidden) (moveJoint action) := by
  refine twoStage.legal_of_legalOption (first_not_terminal hidden) ?_
  intro who
  cases who
  exact ⟨trivial, Set.mem_univ _⟩

theorem moveJoint_legal_second (hidden firstAction action : Bool) :
    twoStage.Legal (.second hidden firstAction) (moveJoint action) := by
  refine twoStage.legal_of_legalOption
    (second_not_terminal hidden firstAction) ?_
  intro who
  cases who
  exact ⟨trivial, Set.mem_univ _⟩

def secondHistory (hidden firstAction : Bool) : twoStage.History :=
  let isLegal := moveJoint_legal_first hidden firstAction
  ⟨.second hidden firstAction,
    (firstHistory hidden).trace.extend (moveJoint firstAction) isLegal
      (FinDist.mem_support_pure.mpr rfl)⟩

theorem second_active (hidden firstAction : Bool) :
    twoStage.active (secondHistory hidden firstAction).state () := by
  exact trivial

def terminalHistory (hidden firstAction secondAction : Bool) :
    twoStage.History :=
  let isLegal := moveJoint_legal_second hidden firstAction secondAction
  ⟨.done hidden firstAction secondAction,
    (secondHistory hidden firstAction).trace.extend
      (moveJoint secondAction) isLegal
      (FinDist.mem_support_pure.mpr rfl)⟩

abbrev ActionRecord := Stage × Bool
abbrev Knowledge := Stage × List ActionRecord

def pushKnowledge (prior : Knowledge) (own : Option Bool)
    (stage : Stage) : Knowledge :=
  (stage, match own with
    | none => prior.2
    | some action => (prior.1, action) :: prior.2)

@[reducible]
def signals : InfoSignals twoStage where
  PublicSignal := Stage
  PrivateSignal _ := Unit
  initialPublic := .opening
  initialPrivate _ := ()
  publicSignal event := event.target.stage
  privateSignal _ _ := ()
  InfoState _ := Knowledge
  initInfo _ _ signal := (signal, [])
  pushInfo _ prior own _ signal := pushKnowledge prior own signal

def stageMenu : Stage → Set (Option Bool)
  | .first | .second => {choice | ∃ action, choice = some action}
  | _ => {none}

def menu (_ : Unit) (knowledge : Knowledge) : Set (Option Bool) :=
  stageMenu knowledge.1

theorem knowledge_stage : ∀ {state : State} (trace : Trace twoStage state),
    (signals.infoOf () trace).1 = state.stage
  | _, .start => rfl
  | _, .extend prior joint isLegal realized => by
      rw [InfoSignals.infoOf_extend]
      rfl

theorem menu_adequate {state : State} (trace : Trace twoStage state)
    (choice : Option Bool) :
    choice ∈ menu () (signals.infoOf () trace) ↔
      LegalOption twoStage state () choice := by
  unfold menu
  rw [knowledge_stage trace]
  cases state <;> cases choice <;>
    simp [State.stage, stageMenu, LegalOption, State.isDecision]

@[reducible]
def information : InformationModel twoStage where
  toInfoSignals := signals
  menu := menu
  menu_adequate := by
    intro who state trace choice
    cases who
    exact menu_adequate trace choice

def decodeRecord : List ActionRecord → List (Knowledge × Bool)
  | [] => []
  | (stage, action) :: prior =>
      ((stage, prior), action) :: decodeRecord prior

theorem decodeRecord_infoOf_eq_ownPlay :
    ∀ {state : State} (trace : Trace twoStage state),
    decodeRecord (signals.infoOf () trace).2 =
      signals.ownPlay () trace
  | _, .start => rfl
  | _, .extend prior joint isLegal realized => by
      rw [InfoSignals.infoOf_extend, InfoSignals.ownPlay_extend]
      cases hchoice : joint () with
      | none =>
          exact decodeRecord_infoOf_eq_ownPlay prior
      | some action =>
          simp only [signals, pushKnowledge, decodeRecord, Prod.eta]
          exact congrArg
            (List.cons (signals.infoOf () prior, action))
            (decodeRecord_infoOf_eq_ownPlay prior)

theorem information_perfectRecall : information.PerfectRecall := by
  intro who first second firstTrace secondTrace hinfo
  cases who
  rw [← decodeRecord_infoOf_eq_ownPlay firstTrace,
    ← decodeRecord_infoOf_eq_ownPlay secondTrace]
  exact congrArg (fun knowledge : Knowledge =>
    decodeRecord knowledge.2) hinfo

theorem information_actsOnce : information.ActsOnceWhereItMatters :=
  information.actsOnceWhereItMatters_of_perfectRecall
    information_perfectRecall

theorem legal_joint_eq_noop {joint : Unit → Option Bool}
    (isLegal : twoStage.Legal .root joint) : joint = twoStage.noop := by
  funext who
  cases who
  have hinactive : ¬ twoStage.active State.root () := by
    simp [State.isDecision]
  exact LegalOption.eq_none_of_inactive (joint ())
    (twoStage.legalOption_of_legal isLegal ()) hinactive

theorem exists_action_joint_eq {state : State}
    (hactive : state.isDecision) {joint : Unit → Option Bool}
    (isLegal : twoStage.Legal state joint) :
    ∃ action, joint = moveJoint action := by
  obtain ⟨action, haction⟩ :=
    LegalOption.exists_eq_some_of_active (joint ())
      (twoStage.legalOption_of_legal isLegal ())
      (show twoStage.active state () from hactive)
  refine ⟨action, ?_⟩
  funext who
  cases who
  exact haction

theorem root_not_mem_step (source : State) (joint : Unit → Option Bool)
    (isLegal : twoStage.Legal source joint) :
    State.root ∉ (twoStage.step source ⟨joint, isLegal⟩).support := by
  cases source with
  | root =>
      rw [FinDist.support_map]
      rintro ⟨hidden, _, hroot⟩
      cases hroot
  | first hidden =>
      rw [FinDist.mem_support_pure]
      simp
  | second hidden firstAction =>
      rw [FinDist.mem_support_pure]
      simp
  | done hidden firstAction secondAction =>
      exact False.elim (isLegal.1 trivial)

theorem step_predecessor_unique
    {target firstSource secondSource : State}
    {firstJoint secondJoint : Unit → Option Bool}
    (firstLegal : twoStage.Legal firstSource firstJoint)
    (secondLegal : twoStage.Legal secondSource secondJoint)
    (firstRealized :
      target ∈
        (twoStage.step firstSource ⟨firstJoint, firstLegal⟩).support)
    (secondRealized :
      target ∈
        (twoStage.step secondSource ⟨secondJoint, secondLegal⟩).support) :
    firstSource = secondSource ∧ firstJoint = secondJoint := by
  cases firstSource with
  | root =>
      have hfirstJoint := legal_joint_eq_noop firstLegal
      subst firstJoint
      rw [FinDist.support_map] at firstRealized
      obtain ⟨hidden, _, rfl⟩ := firstRealized
      cases secondSource with
      | root =>
          have hsecondJoint := legal_joint_eq_noop secondLegal
          subst secondJoint
          exact ⟨rfl, rfl⟩
      | first secondHidden =>
          rw [FinDist.mem_support_pure] at secondRealized
          cases secondRealized
      | second secondHidden secondFirst =>
          rw [FinDist.mem_support_pure] at secondRealized
          cases secondRealized
      | done secondHidden secondFirst secondSecond =>
          exact False.elim (secondLegal.1 trivial)
  | first hidden =>
      obtain ⟨firstAction, hfirstJoint⟩ :=
        exists_action_joint_eq (state := .first hidden) trivial firstLegal
      subst firstJoint
      rw [FinDist.mem_support_pure] at firstRealized
      subst target
      cases secondSource with
      | root =>
          rw [FinDist.support_map] at secondRealized
          obtain ⟨secondHidden, _, htarget⟩ := secondRealized
          cases htarget
      | first secondHidden =>
          obtain ⟨secondAction, hsecondJoint⟩ :=
            exists_action_joint_eq (state := .first secondHidden) trivial secondLegal
          subst secondJoint
          rw [FinDist.mem_support_pure] at secondRealized
          simp [chosenAction, moveJoint] at secondRealized
          obtain ⟨rfl, rfl⟩ := secondRealized
          exact ⟨rfl, rfl⟩
      | second secondHidden secondFirst =>
          rw [FinDist.mem_support_pure] at secondRealized
          cases secondRealized
      | done secondHidden secondFirst secondSecond =>
          exact False.elim (secondLegal.1 trivial)
  | second hidden firstAction =>
      obtain ⟨chosen, hfirstJoint⟩ :=
        exists_action_joint_eq (state := .second hidden firstAction)
          trivial firstLegal
      subst firstJoint
      rw [FinDist.mem_support_pure] at firstRealized
      subst target
      cases secondSource with
      | root =>
          rw [FinDist.support_map] at secondRealized
          obtain ⟨secondHidden, _, htarget⟩ := secondRealized
          cases htarget
      | first secondHidden =>
          rw [FinDist.mem_support_pure] at secondRealized
          cases secondRealized
      | second secondHidden secondFirst =>
          obtain ⟨secondAction, hsecondJoint⟩ :=
            exists_action_joint_eq
              (state := .second secondHidden secondFirst)
              trivial secondLegal
          subst secondJoint
          rw [FinDist.mem_support_pure] at secondRealized
          simp [chosenAction, moveJoint] at secondRealized
          obtain ⟨rfl, rfl, rfl⟩ := secondRealized
          exact ⟨rfl, rfl⟩
      | done secondHidden secondFirst secondSecond =>
          exact False.elim (secondLegal.1 trivial)
  | done hidden firstAction secondAction =>
      exact False.elim (firstLegal.1 trivial)

theorem treeShaped : twoStage.IsTreeShaped :=
  twoStage.isTreeShaped_of_predecessor_unique root_not_mem_step
    (fun firstLegal secondLegal firstRealized secondRealized =>
      step_predecessor_unique firstLegal secondLegal
        firstRealized secondRealized)

theorem history_eq_of_state_eq {first second : twoStage.History}
    (hstate : first.state = second.state) : first = second := by
  rcases first with ⟨firstState, firstTrace⟩
  rcases second with ⟨secondState, secondTrace⟩
  simp only at hstate
  subst secondState
  congr
  exact (treeShaped firstState).elim firstTrace secondTrace

def rank : State → ℕ
  | .root => 3
  | .first _ => 2
  | .second _ _ => 1
  | .done _ _ _ => 0

theorem rank_decreases (source target : State)
    (hsuccessor : twoStage.Successor target source) :
    rank target < rank source := by
  rcases hsuccessor with ⟨joint, isLegal, realized⟩
  cases source with
  | root =>
      rw [FinDist.support_map] at realized
      obtain ⟨hidden, _, rfl⟩ := realized
      norm_num [rank]
  | first hidden =>
      rw [FinDist.mem_support_pure] at realized
      subst target
      norm_num [rank]
  | second hidden firstAction =>
      rw [FinDist.mem_support_pure] at realized
      subst target
      norm_num [rank]
  | done hidden firstAction secondAction =>
      exact False.elim (isLegal.1 trivial)

theorem wellFoundedPlay : twoStage.WellFoundedPlay :=
  wellFoundedPlay_of_rank rank rank_decreases

def prescribedPolicy (firstAction secondAction : Bool) :
    information.Policy () :=
  fun knowledge =>
    match hstage : knowledge.1 with
    | .first => ⟨some firstAction, by
        simp [menu, stageMenu, hstage]⟩
    | .second => ⟨some secondAction, by
        simp [menu, stageMenu, hstage]⟩
    | .opening => ⟨none, by simp [menu, stageMenu, hstage]⟩
    | .done => ⟨none, by simp [menu, stageMenu, hstage]⟩

def incumbent : Profile information.strategicSignature :=
  fun _ => prescribedPolicy false false

def jointAlternative : information.Policy () :=
  prescribedPolicy true true

def utility (history : twoStage.History) (_ : Unit) : ℝ :=
  match history.state with
  | .done _ true true => 1
  | _ => 0

theorem done_utility_match (hidden firstAction secondAction : Bool) :
    (match State.done hidden firstAction secondAction with
      | .done _ true true => (1 : ℝ)
      | _ => 0) =
      if firstAction && secondAction then 1 else 0 := by
  cases firstAction <;> cases secondAction <;> rfl

def profileOf (policy : information.Policy ()) :
    Profile information.strategicSignature :=
  fun _ => policy

def continuationValue (profile : Profile information.strategicSignature)
    (history : twoStage.History) : ℝ :=
  twoStage.historyBackwardValue wellFoundedPlay
    (information.historyChooser profile)
    (fun outcome => utility outcome ()) history

theorem infoOf_firstHistory (hidden : Bool) :
    signals.infoOf () (firstHistory hidden).trace = (.first, []) := by
  rw [firstHistory, InfoSignals.infoOf_extend, InfoSignals.infoOf_start]
  rfl

theorem infoOf_secondHistory (hidden firstAction : Bool) :
    signals.infoOf () (secondHistory hidden firstAction).trace =
      (.second, [(.first, firstAction)]) := by
  rw [secondHistory, InfoSignals.infoOf_extend, infoOf_firstHistory]
  rfl

theorem historyChooser_prescribed_first (hidden firstAction secondAction : Bool) :
    information.historyChooser
        (profileOf (prescribedPolicy firstAction secondAction))
        (firstHistory hidden) (first_not_terminal hidden) =
      ⟨moveJoint firstAction,
        moveJoint_legal_first hidden firstAction⟩ := by
  apply Subtype.ext
  funext who
  cases who
  simp only [InformationModel.historyChooser, InformationModel.jointAt,
    profileOf, InformationModel.Policy.act]
  rw [infoOf_firstHistory]
  rfl

theorem historyChooser_prescribed_second
    (hidden firstAction prescribedFirst prescribedSecond : Bool) :
    information.historyChooser
        (profileOf (prescribedPolicy prescribedFirst prescribedSecond))
        (secondHistory hidden firstAction)
        (second_not_terminal hidden firstAction) =
      ⟨moveJoint prescribedSecond,
        moveJoint_legal_second hidden firstAction prescribedSecond⟩ := by
  apply Subtype.ext
  funext who
  cases who
  simp only [InformationModel.historyChooser, InformationModel.jointAt,
    profileOf, InformationModel.Policy.act]
  rw [infoOf_secondHistory]
  rfl

theorem continuationValue_prescribed_second
    (hidden firstAction prescribedFirst prescribedSecond : Bool) :
    continuationValue
        (profileOf (prescribedPolicy prescribedFirst prescribedSecond))
        (secondHistory hidden firstAction) =
      if firstAction && prescribedSecond then 1 else 0 := by
  rw [continuationValue,
    twoStage.historyBackwardValue_of_not_terminal
      (second_not_terminal hidden firstAction),
    historyChooser_prescribed_second]
  let chosen :
      {joint : Unit → Option Bool //
        twoStage.Legal (.second hidden firstAction) joint} :=
    ⟨moveJoint prescribedSecond,
      moveJoint_legal_second hidden firstAction prescribedSecond⟩
  calc
    twoStage.historyStepValue (secondHistory hidden firstAction) chosen
        (fun target realized =>
          twoStage.historyBackwardValue wellFoundedPlay
            (information.historyChooser
              (profileOf (prescribedPolicy prescribedFirst prescribedSecond)))
            (fun outcome => utility outcome ())
            ((secondHistory hidden firstAction).extend chosen.2 realized)) =
      twoStage.historyStepValue (secondHistory hidden firstAction) chosen
        (fun _target _realized =>
          if firstAction && prescribedSecond then 1 else 0) := by
            apply ExecutionProtocol.historyStepValue_congr
            intro target realized
            have htarget :
                target = .done hidden firstAction prescribedSecond := by
              have hpure : target ∈
                  (FinDist.pure
                    (.done hidden firstAction prescribedSecond)).support :=
                realized
              exact FinDist.mem_support_pure.mp hpure
            subst target
            rw [twoStage.historyBackwardValue_of_terminal]
            · cases firstAction <;> cases prescribedSecond <;>
                norm_num [utility]
            · simp [State.isTerminal]
    _ = if firstAction && prescribedSecond then 1 else 0 := by
      simp [ExecutionProtocol.historyStepValue]

theorem continuationValue_prescribed_first
    (hidden prescribedFirst prescribedSecond : Bool) :
    continuationValue
        (profileOf (prescribedPolicy prescribedFirst prescribedSecond))
        (firstHistory hidden) =
      if prescribedFirst && prescribedSecond then 1 else 0 := by
  rw [continuationValue,
    twoStage.historyBackwardValue_of_not_terminal
      (first_not_terminal hidden),
    historyChooser_prescribed_first]
  let chosen :
      {joint : Unit → Option Bool //
        twoStage.Legal (.first hidden) joint} :=
    ⟨moveJoint prescribedFirst,
      moveJoint_legal_first hidden prescribedFirst⟩
  calc
    twoStage.historyStepValue (firstHistory hidden) chosen
        (fun target realized =>
          twoStage.historyBackwardValue wellFoundedPlay
            (information.historyChooser
              (profileOf (prescribedPolicy prescribedFirst prescribedSecond)))
            (fun outcome => utility outcome ())
            ((firstHistory hidden).extend chosen.2 realized)) =
      twoStage.historyStepValue (firstHistory hidden) chosen
        (fun _target _realized =>
          if prescribedFirst && prescribedSecond then 1 else 0) := by
            apply ExecutionProtocol.historyStepValue_congr
            intro target realized
            have htarget : target = .second hidden prescribedFirst := by
              have hpure : target ∈
                  (FinDist.pure (.second hidden prescribedFirst)).support :=
                realized
              exact FinDist.mem_support_pure.mp hpure
            subst target
            have hhistory :
                (firstHistory hidden).extend chosen.2 realized =
                  secondHistory hidden prescribedFirst :=
              history_eq_of_state_eq rfl
            rw [hhistory]
            exact continuationValue_prescribed_second hidden prescribedFirst
              prescribedFirst prescribedSecond
    _ = if prescribedFirst && prescribedSecond then 1 else 0 := by
      simp [ExecutionProtocol.historyStepValue]

theorem historyChooser_prescribed_root (firstAction secondAction : Bool) :
    information.historyChooser
        (profileOf (prescribedPolicy firstAction secondAction))
        twoStage.initHistory root_not_terminal =
      ⟨twoStage.noop, root_noop_legal⟩ := by
  apply Subtype.ext
  funext who
  cases who
  rfl

theorem continuationValue_prescribed_root
    (firstAction secondAction : Bool) :
    continuationValue
        (profileOf (prescribedPolicy firstAction secondAction))
        twoStage.initHistory =
      if firstAction && secondAction then 1 else 0 := by
  rw [continuationValue,
    twoStage.historyBackwardValue_of_not_terminal root_not_terminal,
    historyChooser_prescribed_root]
  let chosen :
      {joint : Unit → Option Bool // twoStage.Legal .root joint} :=
    ⟨twoStage.noop, root_noop_legal⟩
  calc
    twoStage.historyStepValue twoStage.initHistory chosen
        (fun target realized =>
          twoStage.historyBackwardValue wellFoundedPlay
            (information.historyChooser
              (profileOf (prescribedPolicy firstAction secondAction)))
            (fun outcome => utility outcome ())
            (twoStage.initHistory.extend chosen.2 realized)) =
      twoStage.historyStepValue twoStage.initHistory chosen
        (fun _target _realized =>
          if firstAction && secondAction then 1 else 0) := by
            apply ExecutionProtocol.historyStepValue_congr
            intro target realized
            have hmap : target ∈
                (FinDist.map State.first natureLaw).support := realized
            rw [FinDist.support_map] at hmap
            obtain ⟨hidden, _, htarget⟩ := hmap
            subst target
            have hhistory :
                twoStage.initHistory.extend chosen.2 realized =
                  firstHistory hidden :=
              history_eq_of_state_eq rfl
            rw [hhistory]
            exact continuationValue_prescribed_first hidden firstAction
              secondAction
    _ = if firstAction && secondAction then 1 else 0 := by
      simp [ExecutionProtocol.historyStepValue]

def firstKnowledge : Knowledge := (.first, [])

def secondKnowledge (firstAction : Bool) : Knowledge :=
  (.second, [(.first, firstAction)])

def policyAction (policy : information.Policy ())
    (knowledge : Knowledge) : Bool :=
  (policy knowledge).1.getD false

theorem policy_choice_first_eq_some (policy : information.Policy ()) :
    (policy firstKnowledge).1 =
      some (policyAction policy firstKnowledge) := by
  rcases (policy firstKnowledge).2 with ⟨action, haction⟩
  simp [policyAction, haction]

theorem policy_choice_second_eq_some (policy : information.Policy ())
    (firstAction : Bool) :
    (policy (secondKnowledge firstAction)).1 =
      some (policyAction policy (secondKnowledge firstAction)) := by
  rcases (policy (secondKnowledge firstAction)).2 with ⟨action, haction⟩
  simp [policyAction, haction]

theorem historyChooser_policy_first (policy : information.Policy ())
    (hidden : Bool) :
    information.historyChooser (profileOf policy)
        (firstHistory hidden) (first_not_terminal hidden) =
      ⟨moveJoint (policyAction policy firstKnowledge),
        moveJoint_legal_first hidden
          (policyAction policy firstKnowledge)⟩ := by
  apply Subtype.ext
  funext who
  cases who
  simp only [InformationModel.historyChooser, InformationModel.jointAt,
    profileOf, InformationModel.Policy.act]
  rw [infoOf_firstHistory]
  exact policy_choice_first_eq_some policy

theorem historyChooser_policy_second (policy : information.Policy ())
    (hidden firstAction : Bool) :
    information.historyChooser (profileOf policy)
        (secondHistory hidden firstAction)
        (second_not_terminal hidden firstAction) =
      ⟨moveJoint (policyAction policy (secondKnowledge firstAction)),
        moveJoint_legal_second hidden firstAction
          (policyAction policy (secondKnowledge firstAction))⟩ := by
  apply Subtype.ext
  funext who
  cases who
  simp only [InformationModel.historyChooser, InformationModel.jointAt,
    profileOf, InformationModel.Policy.act]
  rw [infoOf_secondHistory]
  exact policy_choice_second_eq_some policy firstAction

theorem continuationValue_policy_second (policy : information.Policy ())
    (hidden firstAction : Bool) :
    continuationValue (profileOf policy)
        (secondHistory hidden firstAction) =
      if firstAction && policyAction policy (secondKnowledge firstAction)
        then 1 else 0 := by
  rw [continuationValue,
    twoStage.historyBackwardValue_of_not_terminal
      (second_not_terminal hidden firstAction),
    historyChooser_policy_second]
  let secondAction := policyAction policy (secondKnowledge firstAction)
  let chosen :
      {joint : Unit → Option Bool //
        twoStage.Legal (.second hidden firstAction) joint} :=
    ⟨moveJoint secondAction,
      moveJoint_legal_second hidden firstAction secondAction⟩
  calc
    twoStage.historyStepValue (secondHistory hidden firstAction) chosen
        (fun target realized =>
          twoStage.historyBackwardValue wellFoundedPlay
            (information.historyChooser (profileOf policy))
            (fun outcome => utility outcome ())
            ((secondHistory hidden firstAction).extend chosen.2 realized)) =
      twoStage.historyStepValue (secondHistory hidden firstAction) chosen
        (fun _target _realized =>
          if firstAction && secondAction then 1 else 0) := by
            apply ExecutionProtocol.historyStepValue_congr
            intro target realized
            have htarget : target = .done hidden firstAction secondAction := by
              have hpure : target ∈
                  (FinDist.pure (.done hidden firstAction secondAction)).support :=
                realized
              exact FinDist.mem_support_pure.mp hpure
            subst target
            rw [twoStage.historyBackwardValue_of_terminal]
            · exact done_utility_match hidden firstAction secondAction
            · simp [State.isTerminal]
    _ = if firstAction && secondAction then 1 else 0 := by
      simp [ExecutionProtocol.historyStepValue]

theorem continuationValue_policy_first (policy : information.Policy ())
    (hidden : Bool) :
    continuationValue (profileOf policy) (firstHistory hidden) =
      let firstAction := policyAction policy firstKnowledge
      if firstAction && policyAction policy (secondKnowledge firstAction)
        then 1 else 0 := by
  rw [continuationValue,
    twoStage.historyBackwardValue_of_not_terminal
      (first_not_terminal hidden),
    historyChooser_policy_first]
  let firstAction := policyAction policy firstKnowledge
  let chosen :
      {joint : Unit → Option Bool //
        twoStage.Legal (.first hidden) joint} :=
    ⟨moveJoint firstAction, moveJoint_legal_first hidden firstAction⟩
  calc
    twoStage.historyStepValue (firstHistory hidden) chosen
        (fun target realized =>
          twoStage.historyBackwardValue wellFoundedPlay
            (information.historyChooser (profileOf policy))
            (fun outcome => utility outcome ())
            ((firstHistory hidden).extend chosen.2 realized)) =
      twoStage.historyStepValue (firstHistory hidden) chosen
        (fun _target _realized =>
          if firstAction && policyAction policy (secondKnowledge firstAction)
            then 1 else 0) := by
            apply ExecutionProtocol.historyStepValue_congr
            intro target realized
            have htarget : target = .second hidden firstAction := by
              have hpure : target ∈
                  (FinDist.pure (.second hidden firstAction)).support := realized
              exact FinDist.mem_support_pure.mp hpure
            subst target
            have hhistory :
                (firstHistory hidden).extend chosen.2 realized =
                  secondHistory hidden firstAction :=
              history_eq_of_state_eq rfl
            rw [hhistory]
            exact continuationValue_policy_second policy hidden firstAction
    _ = if firstAction && policyAction policy (secondKnowledge firstAction)
          then 1 else 0 := by
      simp [ExecutionProtocol.historyStepValue]

theorem historyChooser_policy_root (policy : information.Policy ()) :
    information.historyChooser (profileOf policy)
        twoStage.initHistory root_not_terminal =
      ⟨twoStage.noop, root_noop_legal⟩ := by
  apply Subtype.ext
  funext who
  cases who
  have hchoice := (policy (signals.infoOf () twoStage.initHistory.trace)).2
  simp only [InformationModel.historyChooser, InformationModel.jointAt,
    profileOf, InformationModel.Policy.act, ExecutionProtocol.noop]
  exact Set.mem_singleton_iff.mp hchoice

theorem continuationValue_policy_root (policy : information.Policy ()) :
    continuationValue (profileOf policy) twoStage.initHistory =
      let firstAction := policyAction policy firstKnowledge
      if firstAction && policyAction policy (secondKnowledge firstAction)
        then 1 else 0 := by
  rw [continuationValue,
    twoStage.historyBackwardValue_of_not_terminal root_not_terminal,
    historyChooser_policy_root]
  let firstAction := policyAction policy firstKnowledge
  let result : ℝ :=
    if firstAction && policyAction policy (secondKnowledge firstAction)
      then 1 else 0
  let chosen :
      {joint : Unit → Option Bool // twoStage.Legal .root joint} :=
    ⟨twoStage.noop, root_noop_legal⟩
  calc
    twoStage.historyStepValue twoStage.initHistory chosen
        (fun target realized =>
          twoStage.historyBackwardValue wellFoundedPlay
            (information.historyChooser (profileOf policy))
            (fun outcome => utility outcome ())
            (twoStage.initHistory.extend chosen.2 realized)) =
      twoStage.historyStepValue twoStage.initHistory chosen
        (fun _target _realized => result) := by
            apply ExecutionProtocol.historyStepValue_congr
            intro target realized
            have hmap : target ∈
                (FinDist.map State.first natureLaw).support := realized
            rw [FinDist.support_map] at hmap
            obtain ⟨hidden, _, htarget⟩ := hmap
            subst target
            have hhistory :
                twoStage.initHistory.extend chosen.2 realized =
                  firstHistory hidden :=
              history_eq_of_state_eq rfl
            rw [hhistory]
            exact continuationValue_policy_first policy hidden
    _ = result := by simp [ExecutionProtocol.historyStepValue]

theorem update_unit_eq_profileOf
    (profile : Profile information.strategicSignature)
    (alternative : information.Policy ()) :
    Profile.update profile () alternative = profileOf alternative := by
  funext who
  cases who
  exact Profile.update_same profile () alternative

theorem incumbent_eq_profileOf :
    incumbent = profileOf (prescribedPolicy false false) := rfl

theorem replace_first_value
    (choice : information.Choice () firstKnowledge) :
    continuationValue
        (profileOf
          ((incumbent ()).replaceAt firstKnowledge choice))
        twoStage.initHistory = 0 := by
  rw [continuationValue_policy_root]
  rcases choice.2 with ⟨action, hchoice⟩
  cases action <;>
    simp [policyAction, firstKnowledge, secondKnowledge, incumbent,
      prescribedPolicy, hchoice]

theorem replace_second_false_value
    (choice : information.Choice () (secondKnowledge false)) :
    continuationValue
        (profileOf
          ((incumbent ()).replaceAt (secondKnowledge false) choice))
        twoStage.initHistory = 0 := by
  rw [continuationValue_policy_root]
  simp [policyAction, firstKnowledge, secondKnowledge, incumbent,
    prescribedPolicy]

theorem replace_second_true_value
    (choice : information.Choice () (secondKnowledge true)) :
    continuationValue
        (profileOf
          ((incumbent ()).replaceAt (secondKnowledge true) choice))
        twoStage.initHistory = 0 := by
  rw [continuationValue_policy_root]
  simp [policyAction, firstKnowledge, secondKnowledge, incumbent,
    prescribedPolicy]

theorem incumbent_value :
    continuationValue incumbent twoStage.initHistory = 0 := by
  rw [incumbent_eq_profileOf, continuationValue_prescribed_root]
  rfl

theorem jointAlternative_value :
    continuationValue (profileOf jointAlternative) twoStage.initHistory = 1 := by
  rw [jointAlternative, continuationValue_prescribed_root]
  rfl

/-- The incumbent is not SPE: changing both information-state actions is
strictly profitable in the initial (and always proper) subgame. -/
theorem incumbent_not_isSubgamePerfect :
    ¬ information.IsSubgamePerfect wellFoundedPlay incumbent utility := by
  intro hspe
  have hdeviation := hspe twoStage.initHistory
    information.initHistory_isSubgameRoot () jointAlternative
  have hdeviation' :
      continuationValue
          (Profile.update incumbent () jointAlternative)
          twoStage.initHistory ≤
        continuationValue incumbent twoStage.initHistory :=
    hdeviation
  rw [update_unit_eq_profileOf, jointAlternative_value,
    incumbent_value] at hdeviation'
  norm_num at hdeviation'

/-- The natural single-information-set test: in every proper subgame, replace
the incumbent choice at one reachable decision information state and then
return to the incumbent policy. -/
def HasNoProfitableSingleInformationDeviationInSubgames
    (profile : Profile information.strategicSignature) : Prop :=
  ∀ (root : twoStage.History), information.IsSubgameRoot root →
    ∀ (decision : twoStage.History),
      twoStage.HistoryReaches root decision →
      ¬ twoStage.terminal decision.state →
      twoStage.active decision.state () →
      ∀ choice : information.Choice ()
          (information.infoOf () decision.trace),
        continuationValue
            (Profile.update profile ()
              ((profile ()).replaceAt
                (information.infoOf () decision.trace) choice)) root ≤
        continuationValue profile root

theorem exists_replaceAt_eq_of_info_eq
    (policy : information.Policy ())
    {first second : Knowledge} (hinfo : first = second)
    (choice : information.Choice () first) :
    ∃ secondChoice : information.Choice () second,
      policy.replaceAt first choice =
        policy.replaceAt second secondChoice := by
  subst second
  exact ⟨choice, rfl⟩

theorem nonterminal_of_reaches_nonterminal
    {root decision : twoStage.History}
    (hreach : twoStage.HistoryReaches root decision)
    (hdecision : ¬ twoStage.terminal decision.state) :
    ¬ twoStage.terminal root.state := by
  intro hroot
  rcases hreach with ⟨fuel, hreach⟩
  cases hreach with
  | refl => exact hdecision hroot
  | step joint isLegal realized rest => exact isLegal.1 hroot

/-- The initial history is the only nonterminal proper subgame root.  First-
and second-decision histories each cut their information set across nature's
two hidden branches. -/
theorem nonterminal_subgameRoot_eq_init (root : twoStage.History)
    (hroot : information.IsSubgameRoot root)
    (hterm : ¬ twoStage.terminal root.state) :
    root = twoStage.initHistory := by
  rcases root with ⟨state, trace⟩
  cases state with
  | root =>
      exact history_eq_of_state_eq rfl
  | first hidden =>
      have hhere :
          ({state := .first hidden, trace := trace} : twoStage.History) =
            firstHistory hidden :=
        history_eq_of_state_eq rfl
      rw [hhere] at hroot
      have hcross := hroot () (firstHistory hidden) (firstHistory (!hidden))
        (HistoryReaches.refl twoStage (firstHistory hidden))
        (first_not_terminal hidden) (first_active hidden)
        (first_not_terminal (!hidden)) (first_active (!hidden))
        (by rw [infoOf_firstHistory, infoOf_firstHistory])
      rcases hcross with ⟨fuel, hreach⟩
      have hequal := ReachesWithin.eq_of_trace_length_eq hreach (by rfl)
      have hstate := congrArg (fun history : twoStage.History => history.state) hequal
      simp [firstHistory] at hstate
  | second hidden firstAction =>
      have hhere :
          ({state := .second hidden firstAction, trace := trace} :
            twoStage.History) = secondHistory hidden firstAction :=
        history_eq_of_state_eq rfl
      rw [hhere] at hroot
      have hcross := hroot ()
        (secondHistory hidden firstAction)
        (secondHistory (!hidden) firstAction)
        (HistoryReaches.refl twoStage (secondHistory hidden firstAction))
        (second_not_terminal hidden firstAction)
        (second_active hidden firstAction)
        (second_not_terminal (!hidden) firstAction)
        (second_active (!hidden) firstAction)
        (by rw [infoOf_secondHistory, infoOf_secondHistory])
      rcases hcross with ⟨fuel, hreach⟩
      have hequal := ReachesWithin.eq_of_trace_length_eq hreach (by rfl)
      have hstate := congrArg (fun history : twoStage.History => history.state) hequal
      simp [secondHistory] at hstate
  | done hidden firstAction secondAction =>
      exact False.elim (hterm trivial)

/-- Every single-information-set deviation is harmless for the incumbent.
The first change leaves the second action false; either second change leaves
the first action false. -/
theorem incumbent_hasNoProfitableSingleInformationDeviationInSubgames :
    HasNoProfitableSingleInformationDeviationInSubgames incumbent := by
  intro root hroot decision hreach hdecision hactive choice
  have hrootTerm := nonterminal_of_reaches_nonterminal hreach hdecision
  have hrootEq := nonterminal_subgameRoot_eq_init root hroot hrootTerm
  subst root
  rcases decision with ⟨state, trace⟩
  cases state with
  | root =>
      exact False.elim (by simp [State.isDecision] at hactive)
  | first hidden =>
      have hhere :
          ({state := .first hidden, trace := trace} : twoStage.History) =
            firstHistory hidden :=
        history_eq_of_state_eq rfl
      have hinfo :
          information.infoOf ()
              ({state := .first hidden, trace := trace} :
                twoStage.History).trace = firstKnowledge := by
        rw [hhere]
        exact infoOf_firstHistory hidden
      obtain ⟨firstChoice, hreplace⟩ :=
        exists_replaceAt_eq_of_info_eq (incumbent ()) hinfo choice
      rw [hreplace, update_unit_eq_profileOf,
        replace_first_value, incumbent_value]
  | second hidden firstAction =>
      have hhere :
          ({state := .second hidden firstAction, trace := trace} :
            twoStage.History) = secondHistory hidden firstAction :=
        history_eq_of_state_eq rfl
      have hinfo :
          information.infoOf ()
              ({state := .second hidden firstAction, trace := trace} :
                twoStage.History).trace = secondKnowledge firstAction := by
        rw [hhere]
        exact infoOf_secondHistory hidden firstAction
      obtain ⟨secondChoice, hreplace⟩ :=
        exists_replaceAt_eq_of_info_eq (incumbent ()) hinfo choice
      rw [hreplace]
      cases firstAction with
      | false =>
          rw [update_unit_eq_profileOf,
            replace_second_false_value, incumbent_value]
      | true =>
          rw [update_unit_eq_profileOf,
            replace_second_true_value, incumbent_value]
  | done hidden firstAction secondAction =>
      exact False.elim (hdecision trivial)

/-- The proposed general imperfect-information one-shot characterization is
false even on finite well-founded perfect-recall play. -/
theorem singleInformationDeviations_do_not_characterize_subgamePerfection :
    HasNoProfitableSingleInformationDeviationInSubgames incumbent ∧
      ¬ information.IsSubgamePerfect wellFoundedPlay incumbent utility :=
  ⟨incumbent_hasNoProfitableSingleInformationDeviationInSubgames,
    incumbent_not_isSubgamePerfect⟩

end GameTheory.Tests.SubgameOneShot
