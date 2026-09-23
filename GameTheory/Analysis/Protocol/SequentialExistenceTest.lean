/-
# Sequential existence with asynchronous imperfect information

Nature sends one branch directly to a decision and the other through an idle
step. The player cannot tell these two decision histories apart, even though
their lengths differ. Terminal observations retain the player's own action,
so perfect recall holds on every legal history.
-/

import GameTheory.Analysis.Protocol.EFGExistence
import GameTheory.Analysis.Protocol.CounterfactualDecomposition
import GameTheory.Analysis.Protocol.SequentialExistenceBoundaryTest

noncomputable section

namespace GameTheory.Tests.SequentialExistence

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

set_option backward.isDefEq.respectTransparency false in
inductive State
  | root
  | waiting
  | decision (hidden : Bool)
  | terminal (hidden action : Bool)
  deriving DecidableEq, Fintype

def State.active : State → Prop
  | .decision _ => True
  | _ => False

def State.stopped : State → Prop
  | .terminal _ _ => True
  | _ => False

def rootLaw : FinDist State :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (.decision false)) (FinDist.pure .waiting)

@[simp] theorem rootLaw_support (state : State) :
    state ∈ rootLaw.support ↔ state = .decision false ∨ state = .waiting := by
  exact FinDist.mem_support_mix_pure_iff _ _ _ (by norm_num) (by norm_num) _ _ _

@[reducible] def execution : ExecutionProtocol Unit where
  State := State
  Action _ := Bool
  init := .root
  active state _ := state.active
  available _ _ := Set.univ
  terminal := State.stopped
  step state joint :=
    match state with
    | .root => rootLaw
    | .waiting => FinDist.pure (.decision true)
    | .decision hidden => FinDist.pure (.terminal hidden ((joint.1 ()).getD false))
    | .terminal hidden action => FinDist.pure (.terminal hidden action)
  progress := by
    intro state running
    cases state with
    | root => exact ⟨fun _ => none, fun _ => by simp [State.active]⟩
    | waiting => exact ⟨fun _ => none, fun _ => by simp [State.active]⟩
    | decision hidden => exact ⟨fun _ => some false, fun _ => ⟨trivial, Set.mem_univ _⟩⟩
    | terminal hidden action => exact False.elim (running trivial)

def jointAt : State → Bool → Unit → Option Bool
  | .decision _, action => fun _ => some action
  | _, _ => fun _ => none

theorem legal_joint {state : State} {joint : Unit → Option Bool}
    (legal : execution.Legal state joint) : ∃ action, joint = jointAt state action := by
  cases state with
  | root =>
      exact ⟨false, execution.eq_noop_of_legal_of_inactive legal (fun _ => by simp [State.active])⟩
  | waiting =>
      exact ⟨false, execution.eq_noop_of_legal_of_inactive legal (fun _ => by simp [State.active])⟩
  | decision hidden =>
      have active : execution.active (.decision hidden) () := trivial
      obtain ⟨action, haction⟩ := LegalOption.exists_eq_some_of_active
        (joint ()) (execution.legalOption_of_legal legal ()) active
      refine ⟨action, ?_⟩
      funext who
      cases who
      exact haction
  | terminal hidden action => exact False.elim (legal.1 trivial)

theorem no_return (source : State) (joint : Unit → Option Bool)
    (legal : execution.Legal source joint) :
    State.root ∉ (execution.step source ⟨joint, legal⟩).support := by
  cases source <;> simp [execution]

theorem predecessor_unique {target first second : State}
    {firstJoint secondJoint : Unit → Option Bool}
    (firstLegal : execution.Legal first firstJoint)
    (secondLegal : execution.Legal second secondJoint)
    (firstReached : target ∈ (execution.step first ⟨firstJoint, firstLegal⟩).support)
    (secondReached : target ∈ (execution.step second ⟨secondJoint, secondLegal⟩).support) :
    first = second ∧ firstJoint = secondJoint := by
  obtain ⟨firstAction, rfl⟩ := legal_joint firstLegal
  obtain ⟨secondAction, rfl⟩ := legal_joint secondLegal
  have firstRunning := firstLegal.1
  have secondRunning := secondLegal.1
  cases first <;> cases second <;>
    simp_all [execution, jointAt, State.stopped, FinDist.mem_support_pure]

theorem treeShaped : execution.IsTreeShaped :=
  isTreeShaped_of_predecessor_unique no_return predecessor_unique

set_option backward.isDefEq.respectTransparency false in
inductive View
  | waiting
  | acting
  | done (action : Bool)
  deriving DecidableEq, Fintype

def viewOf : State → View
  | .root | .waiting => .waiting
  | .decision _ => .acting
  | .terminal _ action => .done action

@[reducible] def signals : InfoSignals execution where
  PublicSignal := Unit
  PrivateSignal _ := View
  initialPublic := ()
  initialPrivate _ := .waiting
  publicSignal _ := ()
  privateSignal _ event := viewOf event.target
  InfoState _ := View
  initInfo _ view _ := view
  pushInfo _ _ _ view _ := view

@[simp] theorem infoOf (who : Unit) :
    ∀ {state : State} (trace : execution.Trace state), signals.infoOf who trace = viewOf state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

@[reducible] def information : InformationModel execution where
  toInfoSignals := signals
  menu _ view := match view with
    | .acting => Set.range some
    | _ => {none}
  menu_adequate := by
    intro who state trace choice
    rw [infoOf]
    cases state <;> cases choice <;> simp [viewOf, LegalOption, State.active]

theorem ownPlay : ∀ {state : State} (trace : execution.Trace state),
    signals.ownPlay () trace = match state with
      | .terminal _ action => [(View.acting, action)]
      | _ => []
  | _, .start => rfl
  | _, .extend (source := source) (target := target) prior joint legal realized => by
      have ih := ownPlay prior
      obtain ⟨action, rfl⟩ := legal_joint legal
      have running := legal.1
      rw [InfoSignals.ownPlay_extend]
      cases source with
      | root =>
          have realized : target ∈ rootLaw.support := realized
          rw [rootLaw_support] at realized
          rcases realized with rfl | rfl <;> simp [jointAt, ih]
      | waiting =>
          have realized : target ∈ (FinDist.pure (.decision true)).support := realized
          rw [FinDist.mem_support_pure] at realized
          subst target
          simp [jointAt, ih]
      | decision hidden =>
          have realized : target ∈ (FinDist.pure (.terminal hidden action)).support := realized
          rw [FinDist.mem_support_pure] at realized
          subst target
          simp [jointAt, ih, viewOf]
      | terminal hidden action => exact False.elim (running trivial)
termination_by _ trace => trace.length
decreasing_by simp [Trace.length]

/-- Retaining one's action in the terminal view discharges recall there too. -/
theorem perfectRecall : information.PerfectRecall := by
  intro who first second firstTrace secondTrace equalInfo
  cases who
  have equalView : viewOf first = viewOf second := by simpa using equalInfo
  simp only [ownPlay]
  cases first <;> cases second <;> simp_all [viewOf]

theorem antichain : information.DecisionInformationAntichain :=
  information.decisionInformationAntichain_of_perfectRecall perfectRecall

@[reducible] def game : Languages.EFG.Game Unit where
  execution := execution
  information := information
  treeShaped := treeShaped
  singleMover := by intros; exact Subsingleton.elim _ _

def fallback (_ : Unit) : information.Policy ()
  | .waiting => ⟨none, by simp⟩
  | .acting => ⟨some false, by simp⟩
  | .done _ => ⟨none, by simp⟩

/-- Every raw information-state menu has a legal choice. -/
theorem nonempty_menus (who : Unit) (info : View) : Nonempty (information.Choice who info) := by
  cases who
  exact ⟨fallback () info⟩

theorem root_legal : execution.Legal .root execution.noop :=
  execution.noop_isLegal (by simp [State.stopped]) (fun _ => by simp [State.active])

theorem waiting_legal : execution.Legal .waiting execution.noop :=
  execution.noop_isLegal (by simp [State.stopped]) (fun _ => by simp [State.active])

@[reducible] def earlyHistory : execution.History :=
  execution.initHistory.extend (target := .decision false) root_legal (by simp [execution])

@[reducible] def waitingHistory : execution.History :=
  execution.initHistory.extend (target := .waiting) root_legal (by simp [execution])

@[reducible] def lateHistory : execution.History :=
  waitingHistory.extend (target := .decision true) waiting_legal (by
    show State.decision true ∈ (FinDist.pure (.decision true)).support
    simp)

theorem same_information : information.infoOf () earlyHistory.trace =
    information.infoOf () lateHistory.trace := rfl

theorem early_length : earlyHistory.trace.length = 1 := rfl

theorem late_length : lateHistory.trace.length = 2 := rfl

def actingSite : information.InformationSite () :=
  information.informationSite () earlyHistory false (by show ¬ False; simp)
    (by show some false ∈ Set.range (@some Bool); simp)

def earlyInformationHistory : information.InformationHistory () actingSite.1 :=
  ⟨earlyHistory, rfl⟩

def lateInformationHistory : information.InformationHistory () actingSite.1 :=
  ⟨lateHistory, rfl⟩

/-- The public common-depth certificate is refuted on the decision fiber. -/
theorem no_commonDepth :
    ¬ ∃ depth, InformationModel.InformationSite.CommonDepth information actingSite depth := by
  rintro ⟨depth, common⟩
  have early : 1 = depth := common earlyInformationHistory
  have late : 2 = depth := common lateInformationHistory
  omega

/-- The shared decision fiber is genuinely imperfect information and has no
common trace depth. -/
theorem distinct_histories : earlyHistory ≠ lateHistory := by
  intro equal
  have := congrArg (fun history : execution.History => history.trace.length) equal
  norm_num [early_length, late_length] at this

def stage : State → ℕ
  | .root => 0
  | .waiting | .decision false => 1
  | .decision true | .terminal false _ => 2
  | .terminal true _ => 3

theorem trace_length : ∀ {state : State} (trace : execution.Trace state),
    trace.length = stage state
  | _, .start => rfl
  | _, .extend (source := source) (target := target) prior joint legal realized => by
      have ih := trace_length prior
      obtain ⟨action, rfl⟩ := legal_joint legal
      have running := legal.1
      cases source with
      | root =>
          have realized : target ∈ rootLaw.support := realized
          rw [rootLaw_support] at realized
          rcases realized with rfl | rfl <;> simp [Trace.length, ih, stage]
      | waiting =>
          have realized : target ∈ (FinDist.pure (.decision true)).support := realized
          rw [FinDist.mem_support_pure] at realized
          subst target
          simp [Trace.length, ih, stage]
      | decision hidden =>
          have realized : target ∈ (FinDist.pure (.terminal hidden action)).support := realized
          rw [FinDist.mem_support_pure] at realized
          subst target
          cases hidden <;> simp [Trace.length, ih, stage]
      | terminal hidden action => exact False.elim (running trivial)
termination_by _ trace => trace.length
decreasing_by simp [Trace.length]

theorem bounded_three : execution.BoundedHorizon 3 := by
  intro state trace lengthBound
  rw [trace_length trace] at lengthBound
  cases state with
  | root => simp [stage] at lengthBound
  | waiting => simp [stage] at lengthBound
  | decision hidden => cases hidden <;> simp [stage] at lengthBound
  | terminal hidden action => trivial

/-- Terminal payoffs depend on the chosen action and nature's hidden bit. -/
def payoff (_ : Unit) (history : execution.History) : ℝ :=
  match history.state with
  | .terminal hidden action => if action = hidden then 1 else 0
  | _ => 0

/-- General finite perfect-recall existence applies despite unequal decision
depths. All structural hypotheses are discharged by this concrete fixture. -/
theorem exists_sequential_equilibrium :
    ∃ assessment : information.BehavioralAssessment,
      game.IsSequentialEquilibriumWithin antichain assessment payoff 3 :=
  game.exists_isSequentialEquilibriumWithin perfectRecall fallback payoff 3
    (by decide) bounded_three

/-- The truncation counterexample has an equilibrium at its certified full
horizon. This uses the general existence theorem, alongside the earlier
proof that the same game's two-step predicate has no assessment. -/
theorem boundary_exists_at_full_horizon :
    ∃ assessment : SequentialExistenceBoundary.information.BehavioralAssessment,
      SequentialExistenceBoundary.game.IsSequentialEquilibriumWithin
        SequentialExistenceBoundary.antichain assessment
        SequentialExistenceBoundary.payoff 3 :=
  SequentialExistenceBoundary.game.exists_isSequentialEquilibriumWithin
    SequentialExistenceBoundary.perfectRecall
    (fun _ => SequentialExistenceBoundary.forcedChoice)
    SequentialExistenceBoundary.payoff 3 (by decide)
    SequentialExistenceBoundary.bounded_three

end GameTheory.Tests.SequentialExistence
