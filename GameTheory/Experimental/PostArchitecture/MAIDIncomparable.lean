/-
# EXP-037: incomparable MAID decisions

This hostile slice tests frontier batching before any general MAID API is made
public. A fair Boolean chance node feeds two Boolean decision nodes owned by
different agents. The decisions are causally incomparable and therefore occur
in one simultaneous Protocol joint-action step. A final administrative step
evaluates utility from both decisions.

The native direct law draws chance, applies both information-local rules, and
evaluates utility. The main theorem proves that the canonical Protocol runner
has exactly that terminal state law.
-/

import GameTheory.Protocol.Information

noncomputable section

namespace GameTheory.Experimental.MAIDIncomparable

open GameTheory.Protocol GameTheory.Probability
open GameTheory.Protocol.ExecutionProtocol

inductive Agent
  | left
  | right
  deriving DecidableEq, Fintype

/-- The compiled frontier state. There is deliberately no constructor that
contains only one decision: incomparable decisions commit together. -/
inductive State
  | start
  | chanceKnown (signal : Bool)
  | decisionsMade (signal left right : Bool)
  | resolved (signal left right : Bool) (value : ℝ)

def payoff (signal left right : Bool) : ℝ :=
  (if left = signal then 1 else 0) +
    (if right = signal then 1 else 0)

def payoffValue : State → ℝ
  | .resolved _ _ _ value => value
  | _ => 0

def leftValue : State → ℝ
  | .decisionsMade _ left _ | .resolved _ left _ _ =>
      if left then 1 else 0
  | _ => 0

def rightValue : State → ℝ
  | .decisionsMade _ _ right | .resolved _ _ right _ =>
      if right then 1 else 0
  | _ => 0

def fairCoin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

def terminal : State → Prop
  | .resolved _ _ _ _ => True
  | _ => False

def active : State → Agent → Prop
  | .chanceKnown _, _ => True
  | _, _ => False

def available (_state : State) (_who : Agent) : Set Bool := Set.univ

def decisionValue : (choice : Option Bool) → choice ≠ none → Bool
  | some value, _ => value
  | none, hne => (hne rfl).elim

theorem eq_some_decisionValue :
    ∀ (choice : Option Bool) (hne : choice ≠ none),
      choice = some (decisionValue choice hne)
  | some _, _ => rfl
  | none, hne => (hne rfl).elim

theorem choice_ne_none {signal : Bool}
    (cert :
      { joint : Agent → Option Bool //
        ¬ terminal (.chanceKnown signal) ∧
          IsLegalJoint (active (.chanceKnown signal))
            (available (.chanceKnown signal)) joint })
    (who : Agent) :
    cert.1 who ≠ none := by
  intro hnone
  have hlegal := cert.2.2 who
  rw [hnone] at hlegal
  exact hlegal trivial

def transition : (state : State) →
    { joint : Agent → Option Bool //
      ¬ terminal state ∧
        IsLegalJoint (active state) (available state) joint } →
    FinDist State
  | .start, _ => FinDist.map State.chanceKnown fairCoin
  | .chanceKnown signal, cert =>
      FinDist.pure (.decisionsMade signal
        (decisionValue (cert.1 .left) (choice_ne_none cert .left))
        (decisionValue (cert.1 .right) (choice_ne_none cert .right)))
  | .decisionsMade signal left right, _ =>
      FinDist.pure (.resolved signal left right
        (payoff signal left right))
  | .resolved _ _ _ _, cert => (cert.2.1 trivial).elim

/-- The Protocol compiler uses exactly the source agents and decision
alphabets. Chance and utility introduce no player or action. -/
@[reducible]
def protocol : ExecutionProtocol Agent where
  State := State
  Action _ := Bool
  init := .start
  active := active
  available := available
  terminal := terminal
  step := transition
  progress := by
    intro state
    cases state with
    | start =>
        exact fun _ => ⟨fun _ => none, fun who => by
          simp [active]⟩
    | chanceKnown signal =>
        exact fun _ => ⟨fun _ => some false, fun _ =>
          ⟨trivial, Set.mem_univ _⟩⟩
    | decisionsMade signal left right =>
        exact fun _ => ⟨fun _ => none, fun who => by
          simp [active]⟩
    | resolved signal left right value =>
        exact fun hterm => False.elim (hterm trivial)

theorem start_not_terminal : ¬ protocol.terminal .start := by
  simp [terminal]

theorem chanceKnown_not_terminal (signal : Bool) :
    ¬ protocol.terminal (.chanceKnown signal) := by
  simp [terminal]

theorem decisionsMade_not_terminal (signal left right : Bool) :
    ¬ protocol.terminal (.decisionsMade signal left right) := by
  simp [terminal]

theorem resolved_terminal (signal left right : Bool) (value : ℝ) :
    protocol.terminal (.resolved signal left right value) := by
  simp [terminal]

theorem both_active (signal : Bool) (who : Agent) :
    protocol.active (.chanceKnown signal) who := by
  trivial

theorem step_start (joint : Agent → Option Bool)
    (isLegal : protocol.Legal .start joint) :
    protocol.step .start ⟨joint, isLegal⟩ =
      FinDist.map State.chanceKnown fairCoin := rfl

theorem step_decisionsMade (signal left right : Bool)
    (joint : Agent → Option Bool)
    (isLegal : protocol.Legal (.decisionsMade signal left right) joint) :
    protocol.step (.decisionsMade signal left right) ⟨joint, isLegal⟩ =
      FinDist.pure (.resolved signal left right
        (payoff signal left right)) := rfl

/-! ## Information locality -/

inductive View
  | waiting
  | deciding (signal : Bool)
  | scoring
  | done
  deriving DecidableEq, Fintype

def viewOfState : State → View
  | .start => .waiting
  | .chanceKnown signal => .deciding signal
  | .decisionsMade _ _ _ => .scoring
  | .resolved _ _ _ _ => .done

@[reducible]
def signals : InfoSignals protocol where
  PublicSignal := View
  PrivateSignal _ := Unit
  initialPublic := .waiting
  initialPrivate _ := ()
  publicSignal event := viewOfState event.target
  privateSignal _ _ := ()
  InfoState _ := View
  initInfo _ _ announced := announced
  pushInfo _ _ _ _ announced := announced

theorem infoOf_eq_viewOfState (who : Agent) :
    ∀ {state : State} (trace : protocol.Trace state),
      signals.infoOf who trace = viewOfState state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def menu : View → Set (Option Bool)
  | .deciding _ => Set.range some
  | _ => {none}

theorem menu_adequate_state (who : Agent) (state : State)
    (choice : Option Bool) :
    choice ∈ menu (viewOfState state) ↔
      LegalOption protocol state who choice := by
  cases state <;> cases choice <;>
    simp [menu, viewOfState, LegalOption, protocol, active, available]

@[reducible]
def model : InformationModel protocol where
  toInfoSignals := signals
  menu _ := menu
  menu_adequate := by
    intro who state trace choice
    rw [infoOf_eq_viewOfState]
    exact menu_adequate_state who state choice

theorem act_ne_none (who : Agent) (policy : model.Policy who)
    (signal : Bool) :
    policy.act (.deciding signal) ≠ none := by
  intro hnone
  have hmem := policy.act_mem_menu (.deciding signal)
  rw [hnone] at hmem
  simp [menu] at hmem

/-- A policy's decision rule depends on the common chance parent only. It does
not receive the other decision's current action. -/
def ruleOf (who : Agent) (policy : model.Policy who)
    (signal : Bool) : Bool :=
  decisionValue (policy.act (.deciding signal))
    (act_ne_none who policy signal)

theorem act_eq_some_ruleOf (who : Agent) (policy : model.Policy who)
    (signal : Bool) :
    policy.act (.deciding signal) =
      some (ruleOf who policy signal) :=
  eq_some_decisionValue _ (act_ne_none who policy signal)

def jointOf (profile : (who : Agent) → model.Policy who)
    (state : State) (who : Agent) : Option Bool :=
  (profile who).act (viewOfState state)

theorem jointOf_legalOption
    (profile : (who : Agent) → model.Policy who)
    (state : State) (who : Agent) :
    LegalOption protocol state who (jointOf profile state who) :=
  (menu_adequate_state who state _).mp
    ((profile who).act_mem_menu (viewOfState state))

def chooserOf (profile : (who : Agent) → model.Policy who) :
    protocol.Chooser := fun state hterm =>
  ⟨jointOf profile state,
    ExecutionProtocol.legal_of_legalOption hterm
      (jointOf_legalOption profile state)⟩

theorem chooserOf_eq_jointAt
    (profile : (who : Agent) → model.Policy who)
    {state : State} (trace : protocol.Trace state)
    (hterm : ¬ protocol.terminal state) :
    (chooserOf profile state hterm).1 = model.jointAt profile trace := by
  funext who
  exact congrArg (profile who).act
    (infoOf_eq_viewOfState who trace).symm

theorem chooserOf_toHistoryChooser_eq
    (profile : (who : Agent) → model.Policy who) :
    (chooserOf profile).toHistoryChooser =
      model.historyChooser profile := by
  funext history hterm
  apply Subtype.ext
  exact chooserOf_eq_jointAt profile history.trace hterm

theorem step_chanceKnown_chooser
    (profile : (who : Agent) → model.Policy who) (signal : Bool) :
    protocol.step (.chanceKnown signal)
        (chooserOf profile (.chanceKnown signal)
          (chanceKnown_not_terminal signal)) =
      FinDist.pure (.decisionsMade signal
        (ruleOf .left (profile .left) signal)
        (ruleOf .right (profile .right) signal)) := rfl

theorem step_start_chooser
    (profile : (who : Agent) → model.Policy who) :
    protocol.step .start
        (chooserOf profile .start start_not_terminal) =
      FinDist.map State.chanceKnown fairCoin := rfl

theorem step_decisionsMade_chooser
    (profile : (who : Agent) → model.Policy who)
    (signal left right : Bool) :
    protocol.step (.decisionsMade signal left right)
        (chooserOf profile (.decisionsMade signal left right)
          (decisionsMade_not_terminal signal left right)) =
      FinDist.pure (.resolved signal left right
        (payoff signal left right)) := rfl

/-! ## Direct and compiled evaluation -/

def intendedOutcome
    (leftRule rightRule : Bool → Bool) : FinDist State :=
  FinDist.map
    (fun signal =>
      .resolved signal (leftRule signal) (rightRule signal)
        (payoff signal (leftRule signal) (rightRule signal)))
    fairCoin

theorem runFor_eq_intendedOutcome
    (profile : (who : Agent) → model.Policy who) :
    protocol.runFor (chooserOf profile) 3 protocol.init =
      intendedOutcome
        (ruleOf .left (profile .left))
        (ruleOf .right (profile .right)) := by
  have hcont : ∀ signal : Bool,
      protocol.runFor (chooserOf profile) 2 (.chanceKnown signal) =
        FinDist.pure (.resolved signal
          (ruleOf .left (profile .left) signal)
          (ruleOf .right (profile .right) signal)
          (payoff signal
            (ruleOf .left (profile .left) signal)
            (ruleOf .right (profile .right) signal))) := by
    intro signal
    rw [ExecutionProtocol.runFor_succ_of_not_terminal
        (chooserOf profile) 1 (chanceKnown_not_terminal signal),
      step_chanceKnown_chooser, FinDist.pure_bind,
      ExecutionProtocol.runFor_succ_of_not_terminal
        (chooserOf profile) 0
        (decisionsMade_not_terminal signal
          (ruleOf .left (profile .left) signal)
          (ruleOf .right (profile .right) signal)),
      step_decisionsMade_chooser, FinDist.pure_bind,
      ExecutionProtocol.runFor_zero]
  rw [ExecutionProtocol.runFor_succ_of_not_terminal
      (chooserOf profile) 2 start_not_terminal,
    step_start_chooser, FinDist.bind_map, intendedOutcome,
    FinDist.map_eq_bind]
  exact FinDist.bind_congr fun signal _ => hcont signal

/-- The information-local history runner has the same terminal state law as
direct frontier evaluation. -/
theorem map_state_run_eq_intendedOutcome
    (profile : (who : Agent) → model.Policy who) :
    FinDist.map History.state (model.run profile 3) =
      intendedOutcome
        (ruleOf .left (profile .left))
        (ruleOf .right (profile .right)) := by
  unfold InformationModel.run InformationModel.runFrom
  rw [← chooserOf_toHistoryChooser_eq profile,
    ExecutionProtocol.map_state_runHistoryFor]
  exact runFor_eq_intendedOutcome profile

/-- The simultaneous decision transition records both actions at once. Every
supported target has both decisions, so no hidden serialization state exists. -/
theorem decisions_commit_together
    (profile : (who : Agent) → model.Policy who) (signal : Bool)
    {target : State}
    (htarget :
      target ∈
        (protocol.step (.chanceKnown signal)
          (chooserOf profile (.chanceKnown signal)
            (chanceKnown_not_terminal signal))).support) :
    target = .decisionsMade signal
      (ruleOf .left (profile .left) signal)
      (ruleOf .right (profile .right) signal) := by
  rw [step_chanceKnown_chooser, FinDist.mem_support_pure] at htarget
  exact htarget

/-! ## Hostile non-vacuity probes -/

def policyOfRule (rule : Bool → Bool) (who : Agent) :
    model.Policy who
  | .deciding signal => ⟨some (rule signal), by simp [menu]⟩
  | .waiting => ⟨none, by simp [menu]⟩
  | .scoring => ⟨none, by simp [menu]⟩
  | .done => ⟨none, by simp [menu]⟩

@[simp]
theorem ruleOf_policyOfRule (rule : Bool → Bool)
    (who : Agent) (signal : Bool) :
    ruleOf who (policyOfRule rule who) signal = rule signal := rfl

def profileOfRules (leftRule rightRule : Bool → Bool) :
    (who : Agent) → model.Policy who
  | .left => policyOfRule leftRule .left
  | .right => policyOfRule rightRule .right

def constant (value : Bool) : Bool → Bool := fun _ => value

def responsive : Bool → Bool := fun signal => signal

theorem expect_fairCoin (score : Bool → ℝ) :
    fairCoin.expect score =
      1 / 2 * score false + (1 - 1 / 2) * score true := by
  rw [fairCoin, FinDist.expect_mix,
    FinDist.expect_pure, FinDist.expect_pure]

theorem expect_payoff_intendedOutcome
    (leftRule rightRule : Bool → Bool) :
    (intendedOutcome leftRule rightRule).expect payoffValue =
      fairCoin.expect fun signal =>
        payoff signal (leftRule signal) (rightRule signal) := by
  rw [intendedOutcome, FinDist.expect_map]
  rfl

theorem expect_left_intendedOutcome
    (leftRule rightRule : Bool → Bool) :
    (intendedOutcome leftRule rightRule).expect leftValue =
      fairCoin.expect fun signal =>
        if leftRule signal then 1 else 0 := by
  rw [intendedOutcome, FinDist.expect_map]
  rfl

theorem expect_right_intendedOutcome
    (leftRule rightRule : Bool → Bool) :
    (intendedOutcome leftRule rightRule).expect rightValue =
      fairCoin.expect fun signal =>
        if rightRule signal then 1 else 0 := by
  rw [intendedOutcome, FinDist.expect_map]
  rfl

theorem outcome_law_depends_on_left :
    FinDist.map History.state
        (model.run (profileOfRules (constant false) (constant false)) 3) ≠
      FinDist.map History.state
        (model.run (profileOfRules (constant true) (constant false)) 3) := by
  intro hequal
  have hscore := congrArg (fun law => law.expect leftValue) hequal
  rw [map_state_run_eq_intendedOutcome,
    map_state_run_eq_intendedOutcome,
    expect_left_intendedOutcome, expect_left_intendedOutcome,
    expect_fairCoin, expect_fairCoin] at hscore
  norm_num [profileOfRules, constant] at hscore

theorem outcome_law_depends_on_right :
    FinDist.map History.state
        (model.run (profileOfRules (constant false) (constant false)) 3) ≠
      FinDist.map History.state
        (model.run (profileOfRules (constant false) (constant true)) 3) := by
  intro hequal
  have hscore := congrArg (fun law => law.expect rightValue) hequal
  rw [map_state_run_eq_intendedOutcome,
    map_state_run_eq_intendedOutcome,
    expect_right_intendedOutcome, expect_right_intendedOutcome,
    expect_fairCoin, expect_fairCoin] at hscore
  norm_num [profileOfRules, constant] at hscore

theorem expect_responsive :
    (FinDist.map History.state
      (model.run (profileOfRules responsive responsive) 3)).expect
        payoffValue = 2 := by
  rw [map_state_run_eq_intendedOutcome,
    expect_payoff_intendedOutcome, expect_fairCoin]
  norm_num [profileOfRules, responsive, payoff]

theorem expect_both_constant_false :
    (FinDist.map History.state
      (model.run
        (profileOfRules (constant false) (constant false)) 3)).expect
        payoffValue = 1 := by
  rw [map_state_run_eq_intendedOutcome,
    expect_payoff_intendedOutcome, expect_fairCoin]
  norm_num [profileOfRules, constant, payoff]

/-- Observing the common chance parent is behaviorally load-bearing. -/
theorem outcome_law_depends_on_observation :
    FinDist.map History.state
        (model.run (profileOfRules responsive responsive) 3) ≠
      FinDist.map History.state
        (model.run
          (profileOfRules (constant false) (constant false)) 3) := by
  intro hequal
  have hscore := congrArg (fun law => law.expect payoffValue) hequal
  rw [expect_responsive, expect_both_constant_false] at hscore
  norm_num at hscore

end GameTheory.Experimental.MAIDIncomparable
