/-
# A three-node MAID on the shared execution base

The encoding that argues hardest against a
single execution interface. A multi-agent influence diagram is not a state
machine: it is a DAG of chance, decision, and utility nodes, each reading its
parents, with no notion of a state, a step, a run, or a terminal position.
The question is whether that shape compiles into `ExecutionProtocol` and
`InformationModel` *honestly*, because the shared execution base is worthless if the
encoding needs fake players, fake actions beyond the canonical `noop`, or
language-specific escape fields.

The diagram is the smallest interesting one: one chance node (`forecast`), one decision node
(`plan`) whose only parent is the chance node, and one utility node (`payoff`)
reading both. It carries two agents rather than one, because a *multi*-agent
influence diagram in which one agent's decision determines another agent's
utility is the smallest thing worth calling a MAID: `planner` owns the decision
node, `sponsor` owns the utility node and never acts.

Four results decide the experiment.

* `runFor_eq_intendedOutcome` — the compiled run law is exactly the diagram's
  intended outcome law, written from the syntax alone: draw the chance node,
  apply the decision rule to the parent it observes, evaluate the utility
  table. `expect_payoffValue_runFor` turns that into the MAID's expected-utility
  semantics.
* `act_eq_some_ruleOf` and `chooserOf_eq_jointAt` — a MAID decision rule *is*
  an information-local policy, and running the compiled protocol with the
  reconstructed chooser is running those policies.
* The discriminating probes `outcome_law_depends_on_decision` and
  `outcome_law_depends_on_observation` — two policies induce different outcome
  laws, and a policy that reads the parent beats every constant one. Without
  them the theorems above would be satisfied by an encoding that quietly
  resolved the decision node itself.
* The `## Workarounds` section, which is the actual deliverable: an unsparing
  list of every language-specific concession, each backed by a theorem where a
  theorem is possible.

Read that section before concluding anything from the theorems.
-/

import GameTheory.Protocol.Information

noncomputable section

namespace GameTheory.Languages.MAID

open GameTheory.Protocol GameTheory.Probability
open GameTheory.Protocol.ExecutionProtocol (Trace StepEvent)

/-! ## Native syntax

The diagram's skeleton is fixed — three nodes, one edge set — so this is a
concrete MAID and deliberately not a DAG framework. -/

/-- The agents of the diagram. `planner` owns the only decision node; `sponsor`
owns the only utility node and never acts. There is deliberately no `nature`
constructor: chance is not an agent in a MAID, and adding one here would be
exactly the fake player a dishonest encoding would introduce. -/
inductive Agent
  | /-- The agent that owns the decision node. -/
    planner
  | /-- The agent that owns the utility node and owns no decision node. -/
    sponsor
  deriving DecidableEq

/-- The three kinds of node a MAID distinguishes. -/
inductive Kind
  | /-- A node nature resolves. -/
    chance
  | /-- A node an agent resolves. -/
    decision
  | /-- A node that scores an agent. -/
    utility
  deriving DecidableEq

/-- The diagram's three nodes. -/
inductive Node
  | /-- The chance node. -/
    forecast
  | /-- The decision node. -/
    plan
  | /-- The utility node. -/
    payoff
  deriving DecidableEq

/-- Each node's kind. -/
def Node.kind : Node → Kind
  | .forecast => .chance
  | .plan => .decision
  | .payoff => .utility

/-- Each node's owner. A chance node has none, and that is the fact which lets
the compiled protocol run chance without a chance player. -/
def Node.owner : Node → Option Agent
  | .forecast => none
  | .plan => some .planner
  | .payoff => some .sponsor

/-- Each node's parents. The decision node observes the chance node; the
utility node reads both. -/
def Node.parents : Node → List Node
  | .forecast => []
  | .plan => [.forecast]
  | .payoff => [.forecast, .plan]

/-- Chance is ownerless. -/
theorem owner_forecast : Node.owner .forecast = none := rfl

/-- The decision node observes exactly one parent: the chance node. This is the
observation the compiled information model has to deliver. -/
theorem parents_plan : Node.parents .plan = [Node.forecast] := rfl

/-- The utility node reads both other nodes, so the compiled state has to carry
both values when it is resolved. -/
theorem parents_payoff : Node.parents .payoff = [Node.forecast, Node.plan] := rfl

/-- The numeric content of the diagram: the two alphabets, the chance node's
law, and the utility node's table. -/
structure Diagram where
  /-- The chance node's alphabet. -/
  Forecast : Type
  /-- The decision node's alphabet. -/
  Plan : Type
  /-- The chance node's law. It has no parents, so this is unconditional. -/
  forecastLaw : FinDist Forecast
  /-- The utility node's table, read off its two parents. -/
  payoff : Forecast → Plan → ℝ
  /-- A decision node's alphabet is nonempty. Native MAID syntax leaves this
  implicit; `ExecutionProtocol.progress` makes it a real obligation, because a
  state where an agent is active and has nothing available would have no legal
  joint action. -/
  planNonempty : Nonempty Plan

/-! ## Compilation: states

The DAG is linearized along its unique topological order. A state records the
prefix of that order already resolved, together with the value each resolved
node took — nothing else. -/

/-- Execution states of the compiled diagram. -/
inductive Stage (D : Diagram)
  | /-- No node resolved yet. -/
    start
  | /-- The chance node took `forecast`. -/
    forecastKnown (forecast : D.Forecast)
  | /-- The decision node took `plan`. -/
    planChosen (forecast : D.Forecast) (plan : D.Plan)
  | /-- The utility node took `payoff`; the diagram is exhausted. -/
    resolved (forecast : D.Forecast) (plan : D.Plan) (payoff : ℝ)

/-- The next node to resolve, and `none` once the diagram is exhausted. -/
def Stage.pending {D : Diagram} : Stage D → Option Node
  | .start => some .forecast
  | .forecastKnown _ => some .plan
  | .planChosen _ _ => some .payoff
  | .resolved _ _ _ => none

/-- The chance node's value, once it has one. -/
def Stage.forecastValue {D : Diagram} : Stage D → Option D.Forecast
  | .start => none
  | .forecastKnown forecast => some forecast
  | .planChosen forecast _ => some forecast
  | .resolved forecast _ _ => some forecast

/-- The utility node's value, as an observable on states. The protocol has no
payoff notion of its own, so a MAID's real-valued semantics is recovered by
taking expectations of this function; before the utility node is resolved it
reports zero, and the run law never gives those states positive mass. -/
def Stage.payoffValue {D : Diagram} : Stage D → ℝ
  | .resolved _ _ value => value
  | _ => 0

/-! ## Compilation: the execution protocol -/

/-- Each agent's action alphabet: the decision node's alphabet for its owner,
and nothing at all for an agent that owns no decision node. `Empty` is the
point: no padding action, canonical or otherwise, had to be invented for the
sponsor. -/
def actionOf (D : Diagram) : Agent → Type
  | .planner => D.Plan
  | .sponsor => Empty

/-- Execution stops when every node has been resolved. -/
def isTerminal (D : Diagram) (state : Stage D) : Prop := state.pending = none

/-- Who must act: the owner of the pending node, when that node is a decision
node. Chance nodes are ownerless and utility nodes are owned by a non-deciding
agent, so this activates exactly one agent at exactly one stage — and never
turns chance into an agent. -/
def isActive (D : Diagram) (state : Stage D) (agent : Agent) : Prop :=
  ∃ node, state.pending = some node ∧ node.kind = .decision ∧ node.owner = some agent

/-- What an active agent may choose: every value of its decision node's
alphabet. A MAID puts no constraint on a decision node's domain, so this is
`Set.univ` rather than a language-specific restriction. -/
def availableAt (D : Diagram) (_state : Stage D) (agent : Agent) :
    Set (actionOf D agent) := Set.univ

/-- Activity, unfolded: only the planner is ever active, and only while the
decision node is pending. -/
theorem isActive_iff (D : Diagram) (state : Stage D) (agent : Agent) :
    isActive D state agent ↔ state.pending = some Node.plan ∧ agent = Agent.planner := by
  constructor
  · rintro ⟨node, hpending, hkind, howner⟩
    cases node with
    | forecast => exact absurd howner (by simp [Node.owner])
    | plan => exact ⟨hpending, by simpa [Node.owner] using howner.symm⟩
    | payoff => exact absurd hkind (by simp [Node.kind])
  · rintro ⟨hpending, rfl⟩
    exact ⟨Node.plan, hpending, rfl, rfl⟩

/-- The value a legal contribution at a decision node carries. Legality already
proves the contribution is not `none`, so the compiled transition never has to
invent an outcome for a joint action the protocol forbids. -/
def decisionValue {α : Type} : (choice : Option α) → choice ≠ none → α
  | some value, _ => value
  | none, hne => (hne rfl).elim

/-- And the extracted value is the one that was there. -/
theorem eq_some_decisionValue {α : Type} :
    ∀ (choice : Option α) (hne : choice ≠ none), choice = some (decisionValue choice hne)
  | some _, _ => rfl
  | none, hne => (hne rfl).elim

/-- At the decision stage the planner's contribution cannot be `none`, because
legality says an active agent supplies an action. This is what removes the dead
branch from `transition`. -/
theorem plan_choice_ne_none {D : Diagram} {forecast : D.Forecast}
    {joint : (agent : Agent) → Option (actionOf D agent)}
    (hlegal : IsLegalJoint (isActive D (.forecastKnown forecast))
      (availableAt D (.forecastKnown forecast)) joint) :
    joint .planner ≠ none := by
  intro hnone
  have hplanner := hlegal Agent.planner
  rw [hnone] at hplanner
  exact hplanner ((isActive_iff D (.forecastKnown forecast) Agent.planner).mpr ⟨rfl, rfl⟩)

/-- The compiled transition law: resolve the pending node.

The chance node contributes its own law; the decision node reads the planner's
action out of the legality certificate; the utility node evaluates its table
into a point mass. The exhausted stage is discharged by the certificate's
non-terminality conjunct, so no branch of this definition invents behaviour for
a step the protocol forbids. -/
def transition (D : Diagram) : (state : Stage D) →
    { joint : (agent : Agent) → Option (actionOf D agent) //
      ¬ isTerminal D state ∧ IsLegalJoint (isActive D state) (availableAt D state) joint } →
    FinDist (Stage D)
  | .start, _ => FinDist.map Stage.forecastKnown D.forecastLaw
  | .forecastKnown forecast, cert =>
      FinDist.pure (.planChosen forecast
        (decisionValue (cert.1 .planner) (plan_choice_ne_none cert.2.2)))
  | .planChosen forecast plan, _ =>
      FinDist.pure (.resolved forecast plan (D.payoff forecast plan))
  | .resolved _ _ _, cert => (cert.2.1 rfl).elim

/-- The joint action in which the planner plays `plan` and the sponsor passes. -/
def plannerPlays {D : Diagram} (plan : D.Plan) :
    (agent : Agent) → Option (actionOf D agent)
  | .planner => some plan
  | .sponsor => none

/-- The compiled protocol.

Marked `@[reducible]` for the reason `coinThenMove` and `hiddenCard` are:
without it `(protocol D).State` does not reduce to `Stage D` at `instances`
transparency, and `rw`, instance search, and `simp` fail on the concrete
protocol. -/
@[reducible]
def protocol (D : Diagram) : ExecutionProtocol Agent where
  State := Stage D
  Action := actionOf D
  init := .start
  active := isActive D
  available := availableAt D
  terminal := isTerminal D
  step := transition D
  progress := by
    intro state
    cases state with
    | start =>
        exact fun _ => ⟨fun _ => none, fun agent => by
          simp [isActive_iff, Stage.pending]⟩
    | forecastKnown forecast =>
        refine fun _ => ⟨plannerPlays D.planNonempty.some, fun agent => ?_⟩
        cases agent with
        | planner =>
            exact ⟨(isActive_iff D (.forecastKnown forecast) Agent.planner).mpr ⟨rfl, rfl⟩,
              Set.mem_univ _⟩
        | sponsor => simp [plannerPlays, isActive_iff]
    | planChosen _ _ =>
        exact fun _ => ⟨fun _ => none, fun agent => by
          simp [isActive_iff, Stage.pending]⟩
    | resolved _ _ _ => exact fun hstop => absurd rfl hstop

/-! ### The compiled protocol, unfolded

These are the bridge lemmas the rest of the module rewrites with; each is
`rfl`, so nothing below depends on how the structure literal was written. -/

/-- Play starts before any node is resolved. -/
theorem protocol_init (D : Diagram) : (protocol D).init = Stage.start := rfl

/-- Terminality is exhaustion of the diagram. -/
theorem protocol_terminal (D : Diagram) (state : Stage D) :
    (protocol D).terminal state ↔ state.pending = none := Iff.rfl

/-- Activity is ownership of the pending decision node. -/
theorem protocol_active (D : Diagram) (state : Stage D) (agent : Agent) :
    (protocol D).active state agent ↔
      state.pending = some Node.plan ∧ agent = Agent.planner :=
  isActive_iff D state agent

/-- Every value of the decision node's alphabet is available. -/
theorem protocol_available (D : Diagram) (state : Stage D) (agent : Agent) :
    (protocol D).available state agent = Set.univ := rfl

/-- The sponsor is never active: it owns no decision node. -/
theorem sponsor_never_active (D : Diagram) (state : Stage D) :
    ¬ (protocol D).active state Agent.sponsor := by
  simp [isActive_iff]

theorem init_not_terminal (D : Diagram) : ¬ (protocol D).terminal (protocol D).init := by
  simp [isTerminal, Stage.pending]

theorem forecastKnown_not_terminal (D : Diagram) (forecast : D.Forecast) :
    ¬ (protocol D).terminal (Stage.forecastKnown forecast) := by
  simp [isTerminal, Stage.pending]

theorem planChosen_not_terminal (D : Diagram) (forecast : D.Forecast) (plan : D.Plan) :
    ¬ (protocol D).terminal (Stage.planChosen forecast plan) := by
  simp [isTerminal, Stage.pending]

theorem resolved_terminal (D : Diagram) (forecast : D.Forecast) (plan : D.Plan)
    (value : ℝ) : (protocol D).terminal (Stage.resolved forecast plan value) := rfl

/-- The chance node's step, for every legal joint action: the joint action is
irrelevant, because nobody is active there. -/
theorem step_init (D : Diagram)
    (cert : { joint : (agent : Agent) → Option ((protocol D).Action agent) //
      (protocol D).Legal (protocol D).init joint }) :
    (protocol D).step (protocol D).init cert =
      FinDist.map Stage.forecastKnown D.forecastLaw := rfl

/-- The utility node's step: a point mass on the value of its table. -/
theorem step_planChosen (D : Diagram) (forecast : D.Forecast) (plan : D.Plan)
    (cert : { joint : (agent : Agent) → Option ((protocol D).Action agent) //
      (protocol D).Legal (Stage.planChosen forecast plan) joint }) :
    (protocol D).step (Stage.planChosen forecast plan) cert =
      FinDist.pure (Stage.resolved forecast plan (D.payoff forecast plan)) := rfl

/-! ### Chance, and the no-op

Both non-decision nodes are stepped through under the canonical no-op. The
chance node's law is the diagram's own law; the utility node's is a point
mass. -/

/-- The chance node compiles to a chance state: play continues and nobody
acts. -/
theorem init_isChance (D : Diagram) : (protocol D).IsChance (protocol D).init :=
  ⟨init_not_terminal D, fun agent hactive => by
    simp [isActive_iff, Stage.pending] at hactive⟩

/-- And its law is the chance node's own law, pushed into the state space. No
dummy probability data appears anywhere. -/
theorem chanceLaw_init (D : Diagram) :
    (protocol D).chanceLaw (init_isChance D) =
      FinDist.map Stage.forecastKnown D.forecastLaw := rfl

/-- **A cost, recorded.** The utility node is *also* a chance state by the
protocol's definition, since `IsChance` means only "play continues and nobody
acts". -/
theorem planChosen_isChance (D : Diagram) (forecast : D.Forecast) (plan : D.Plan) :
    (protocol D).IsChance (Stage.planChosen forecast plan) :=
  ⟨planChosen_not_terminal D forecast plan, fun agent hactive => by
    simp [isActive_iff, Stage.pending] at hactive⟩

/-- What distinguishes the utility node from the chance node is not `IsChance`
but the law: this one is a point mass. -/
theorem chanceLaw_planChosen (D : Diagram) (forecast : D.Forecast) (plan : D.Plan) :
    (protocol D).chanceLaw (planChosen_isChance D forecast plan) =
      FinDist.pure (Stage.resolved forecast plan (D.payoff forecast plan)) := rfl

/-- **No fake actions.** Wherever the decision node is not pending, the *only*
legal joint action is the canonical no-op. Both the chance node and the utility
node are therefore driven by `E.noop` alone. -/
theorem legal_eq_noop_of_pending_ne_plan (D : Diagram) {state : Stage D}
    (hpending : state.pending ≠ some Node.plan)
    {joint : (agent : Agent) → Option ((protocol D).Action agent)}
    (hlegal : (protocol D).Legal state joint) : joint = (protocol D).noop := by
  funext agent
  exact LegalOption.eq_none_of_inactive (joint agent)
    (ExecutionProtocol.legalOption_of_legal hlegal agent)
    (fun hactive => hpending ((protocol_active D state agent).mp hactive).1)

/-! ## Compilation: the information model

A MAID decision node observes its parents. Here that is the chance node, so the
planner is privately told the forecast when it is drawn, and everyone publicly
sees how far the diagram has been resolved. -/

/-- Each agent's private signal alphabet. The planner is told the value of the
parent it observes; the sponsor, which never acts, is told nothing. -/
def Whisper (D : Diagram) : Agent → Type
  | .planner => Option D.Forecast
  | .sponsor => Unit

/-- Each agent's information state: for the planner, the public stage together
with the observed parent's value; for the sponsor, nothing. -/
def View (D : Diagram) : Agent → Type
  | .planner => Option Node × Option D.Forecast
  | .sponsor => Unit

/-- Nothing is whispered before the diagram is touched. -/
def initialWhisper (D : Diagram) : (agent : Agent) → Whisper D agent
  | .planner => none
  | .sponsor => ()

/-- The private signal of a realized transition: the planner is told the value
of its decision node's parent as soon as that node has one. -/
def whisperOf (D : Diagram) : (agent : Agent) → StepEvent (protocol D) → Whisper D agent
  | .planner, event => Stage.forecastValue event.target
  | .sponsor, _ => ()

/-- The information state an agent starts from. -/
def initView (D : Diagram) :
    (agent : Agent) → Whisper D agent → Option Node → View D agent
  | .planner, whisper, report => (report, whisper)
  | .sponsor, _, _ => ()

/-- How a transition updates an information state. It keeps only the latest
signals: the private signal already carries the observed parent's value in
full, so nothing has to be remembered from earlier steps. -/
def pushView (D : Diagram) : (agent : Agent) → View D agent →
    Option (actionOf D agent) → Whisper D agent → Option Node → View D agent
  | .planner, _, _, whisper, report => (report, whisper)
  | .sponsor, _, _, _, _ => ()

/-- The observation half of the model. The public signal is the pending node,
which in a MAID is common knowledge: the diagram's shape is part of its
syntax. -/
@[reducible]
def signals (D : Diagram) : InfoSignals (protocol D) where
  PublicSignal := Option Node
  PrivateSignal := Whisper D
  initialPublic := some Node.forecast
  initialPrivate := initialWhisper D
  publicSignal := fun event => Stage.pending event.target
  privateSignal := whisperOf D
  InfoState := View D
  initInfo := initView D
  pushInfo := pushView D

/-- The information state a stage induces. That this is a function of the
*state* — not only of the history — is special to this diagram; see the
workaround list. -/
def viewOf (D : Diagram) : (agent : Agent) → Stage D → View D agent
  | .planner, state => (Stage.pending state, Stage.forecastValue state)
  | .sponsor, _ => ()

/-- After any history, an agent's information state is the view of the stage it
reached. -/
theorem infoOf_eq_viewOf (D : Diagram) (agent : Agent) {state : (protocol D).State}
    (trace : Trace (protocol D) state) :
    (signals D).infoOf agent trace = viewOf D agent state := by
  induction trace with
  | start => cases agent <;> rfl
  | extend _ _ _ _ _ =>
      rw [InfoSignals.infoOf_extend]
      cases agent <;> rfl

/-- The options an agent faces, as a function of its own information state. The
planner may act exactly when the public part of its view says the decision node
is pending; the sponsor may only pass. -/
def menuAt (D : Diagram) :
    (agent : Agent) → View D agent → Set (Option (actionOf D agent))
  | .planner, view =>
      if view.1 = some Node.plan then { choice | ∃ plan, choice = some plan } else {none}
  | .sponsor, _ => {none}

/-- **Menu adequacy, at the state.** The information-local menu is the
protocol's legal option set at every stage producing that view. This is
stronger than the law `InformationModel` requires, which quantifies over
histories; the diagram earns the stronger form because a stage records the
value of every node already resolved. -/
theorem menuAt_adequate (D : Diagram) (agent : Agent) (state : Stage D)
    (choice : Option (actionOf D agent)) :
    choice ∈ menuAt D agent (viewOf D agent state) ↔
      LegalOption (protocol D) state agent choice := by
  cases agent with
  | planner =>
      by_cases hpending : Stage.pending state = some Node.plan
      · cases choice with
        | none => simp [menuAt, viewOf, hpending, LegalOption, isActive_iff]
        | some plan =>
            simp [menuAt, viewOf, hpending, LegalOption, isActive_iff, availableAt]
      · cases choice with
        | none => simp [menuAt, viewOf, hpending, LegalOption, isActive_iff]
        | some plan =>
            simp [menuAt, viewOf, hpending, LegalOption, isActive_iff]
  | sponsor =>
      cases choice with
      | none => simp [menuAt, LegalOption, isActive_iff]
      | some action => exact action.elim

/-- The information model. -/
@[reducible]
def model (D : Diagram) : InformationModel (protocol D) where
  toInfoSignals := signals D
  menu := menuAt D
  menu_adequate := by
    intro agent state trace choice
    rw [infoOf_eq_viewOf D agent trace]
    exact menuAt_adequate D agent state choice

/-- The model's menu is the one defined above. -/
theorem model_menu (D : Diagram) (agent : Agent) (view : View D agent) :
    (model D).menu agent view = menuAt D agent view := rfl

/-- The model's information states are the views. -/
theorem model_infoOf (D : Diagram) (agent : Agent) {state : (protocol D).State}
    (trace : Trace (protocol D) state) :
    (model D).infoOf agent trace = viewOf D agent state :=
  infoOf_eq_viewOf D agent trace

/-! ## Decision rules are information-local policies -/

/-- The sponsor's only policy: it owns no decision node, so it always passes.
No action had to exist for it to be a policy. -/
def sponsorPolicy (D : Diagram) : (model D).Policy Agent.sponsor := fun _ => ⟨none, rfl⟩

/-- At the decision stage a policy's choice is an action: the menu excludes
passing there. -/
theorem act_ne_none (D : Diagram) (policy : (model D).Policy Agent.planner)
    (forecast : D.Forecast) :
    policy.act (viewOf D Agent.planner (Stage.forecastKnown forecast)) ≠ none := by
  intro hnone
  have hlegal : LegalOption (protocol D) (Stage.forecastKnown forecast) Agent.planner
      (policy.act (viewOf D Agent.planner (Stage.forecastKnown forecast))) :=
    (menuAt_adequate D Agent.planner (Stage.forecastKnown forecast) _).mp
      (policy.act_mem_menu (viewOf D Agent.planner (Stage.forecastKnown forecast)))
  rw [hnone] at hlegal
  exact hlegal ((protocol_active D (Stage.forecastKnown forecast) Agent.planner).mpr
    ⟨rfl, rfl⟩)

/-- **The MAID decision rule an information-local policy is**: a function from
the value of the decision node's observed parent to a value of the decision
node's own alphabet. Nothing is projected away and nothing is added. -/
def ruleOf (D : Diagram) (policy : (model D).Policy Agent.planner)
    (forecast : D.Forecast) : D.Plan :=
  decisionValue (policy.act (viewOf D Agent.planner (Stage.forecastKnown forecast)))
    (act_ne_none D policy forecast)

/-- And the policy really plays that rule. -/
theorem act_eq_some_ruleOf (D : Diagram) (policy : (model D).Policy Agent.planner)
    (forecast : D.Forecast) :
    policy.act (viewOf D Agent.planner (Stage.forecastKnown forecast)) =
      some (ruleOf D policy forecast) :=
  eq_some_decisionValue _ (act_ne_none D policy forecast)

/-- The joint action an information-local policy produces at a stage: the
planner's policy applied to its own view, and silence from the sponsor. -/
def jointOf (D : Diagram) (policy : (model D).Policy Agent.planner) (state : Stage D) :
    (agent : Agent) → Option (actionOf D agent)
  | .planner => policy.act (viewOf D Agent.planner state)
  | .sponsor => none

theorem jointOf_legalOption (D : Diagram) (policy : (model D).Policy Agent.planner)
    (state : Stage D) (agent : Agent) :
    LegalOption (protocol D) state agent (jointOf D policy state agent) := by
  cases agent with
  | planner =>
      exact (menuAt_adequate D Agent.planner state _).mp
        (policy.act_mem_menu (viewOf D Agent.planner state))
  | sponsor => exact sponsor_never_active D state

/-- The runner's input, reconstructed from a decision rule. `runFor` consumes a
*state*-indexed chooser while a policy is history-indexed, so the bridge reads
the planner's view out of the stage — which `infoOf_eq_viewOf` shows loses
nothing. -/
def chooserOf (D : Diagram) (policy : (model D).Policy Agent.planner) :
    (protocol D).Chooser := fun state hterm =>
  ⟨jointOf D policy state,
    ExecutionProtocol.legal_of_legalOption hterm (jointOf_legalOption D policy state)⟩

/-- Both agents' policies, assembled. -/
def policiesOf (D : Diagram) (policy : (model D).Policy Agent.planner) :
    (agent : Agent) → (model D).Policy agent
  | .planner => policy
  | .sponsor => sponsorPolicy D

/-- **The bridge is faithful.** Running the compiled protocol with the
reconstructed chooser is running the information-local policies: after every
history, the chooser's joint action is the one the policies take. So the
state-indexed runner is not a second, better-informed strategy type. -/
theorem chooserOf_eq_jointAt (D : Diagram) (policy : (model D).Policy Agent.planner)
    {state : (protocol D).State} (trace : Trace (protocol D) state)
    (hterm : ¬ (protocol D).terminal state) :
    (chooserOf D policy state hterm).1 = (model D).jointAt (policiesOf D policy) trace := by
  funext agent
  cases agent with
  | planner => exact congrArg policy.act (model_infoOf D Agent.planner trace).symm
  | sponsor => rfl

/-! ## The evaluation fact

The compiled run law reproduces the diagram's intended outcome law. -/

/-- The outcome law the diagram intends: draw the chance node, apply the
decision rule to the parent it observes, evaluate the utility table. This is
written from the syntax alone — no state, step, fuel, or trace occurs in it. -/
def intendedOutcome (D : Diagram) (rule : D.Forecast → D.Plan) : FinDist (Stage D) :=
  FinDist.map (fun forecast =>
      Stage.resolved forecast (rule forecast) (D.payoff forecast (rule forecast)))
    D.forecastLaw

/-- The decision node's step under the reconstructed chooser. -/
theorem step_forecastKnown_chooser (D : Diagram)
    (policy : (model D).Policy Agent.planner) (forecast : D.Forecast) :
    (protocol D).step (Stage.forecastKnown forecast)
        (chooserOf D policy (Stage.forecastKnown forecast)
          (forecastKnown_not_terminal D forecast)) =
      FinDist.pure (Stage.planChosen forecast (ruleOf D policy forecast)) := rfl

/-- **The evaluation fact.** Three steps — one per node — take the compiled
protocol from its initial state to the diagram's intended outcome law. -/
theorem runFor_eq_intendedOutcome (D : Diagram)
    (policy : (model D).Policy Agent.planner) :
    (protocol D).runFor (chooserOf D policy) 3 (protocol D).init =
      intendedOutcome D (ruleOf D policy) := by
  have hcont : ∀ forecast : D.Forecast,
      (protocol D).runFor (chooserOf D policy) 2 (Stage.forecastKnown forecast) =
        FinDist.pure (Stage.resolved forecast (ruleOf D policy forecast)
          (D.payoff forecast (ruleOf D policy forecast))) := by
    intro forecast
    rw [ExecutionProtocol.runFor_succ_of_not_terminal (chooserOf D policy) 1
        (forecastKnown_not_terminal D forecast),
      step_forecastKnown_chooser D policy forecast, FinDist.pure_bind,
      ExecutionProtocol.runFor_succ_of_not_terminal (chooserOf D policy) 0
        (planChosen_not_terminal D forecast (ruleOf D policy forecast)),
      step_planChosen, FinDist.pure_bind, ExecutionProtocol.runFor_zero]
  rw [ExecutionProtocol.runFor_succ_of_not_terminal (chooserOf D policy) 2
      (init_not_terminal D), step_init, FinDist.bind_map, intendedOutcome,
    FinDist.map_eq_bind]
  exact FinDist.bind_congr fun forecast _ => hcont forecast

/-- The run stops within three steps, so the fuelled runner is a total
evaluator here. -/
theorem stopsWithin_three (D : Diagram) (policy : (model D).Policy Agent.planner) :
    (protocol D).StopsWithin (chooserOf D policy) 3 (protocol D).init := by
  intro reached hreached
  rw [runFor_eq_intendedOutcome, intendedOutcome, FinDist.support_map] at hreached
  obtain ⟨forecast, _, rfl⟩ := hreached
  exact resolved_terminal D forecast (ruleOf D policy forecast) _

/-- Hence three is not a magic number: every fuel that reaches the end of the
diagram gives the diagram's outcome law. -/
theorem runFor_eq_intendedOutcome_of_le (D : Diagram)
    (policy : (model D).Policy Agent.planner) {fuel : ℕ} (hfuel : 3 ≤ fuel) :
    (protocol D).runFor (chooserOf D policy) fuel (protocol D).init =
      intendedOutcome D (ruleOf D policy) := by
  rw [ExecutionProtocol.runFor_eq_of_stopsWithin_le (stopsWithin_three D policy) hfuel]
  exact runFor_eq_intendedOutcome D policy

/-- **The MAID's expected-utility semantics**, recovered from the run law. The
protocol carries no payoff of its own; the utility node's value is an
observable on states, and its expectation under the run law is the diagram's
expected utility. -/
theorem expect_payoffValue_runFor (D : Diagram)
    (policy : (model D).Policy Agent.planner) :
    ((protocol D).runFor (chooserOf D policy) 3 (protocol D).init).expect
        Stage.payoffValue =
      D.forecastLaw.expect fun forecast => D.payoff forecast (ruleOf D policy forecast) := by
  rw [runFor_eq_intendedOutcome, intendedOutcome, FinDist.expect_map]
  rfl

/-! ## A concrete diagram

The generic development above is instantiated so the probes have something to
be about. -/

/-- The chance node's alphabet. -/
inductive Sky
  | /-- Bad weather. -/
    rain
  | /-- Good weather. -/
    shine
  deriving DecidableEq

/-- The decision node's alphabet. -/
inductive Venue
  | /-- Hold it inside. -/
    indoors
  | /-- Hold it outside. -/
    outdoors
  deriving DecidableEq

/-- The chance node's law: rain with probability one third. -/
def skyLaw : FinDist Sky :=
  FinDist.mix (1 / 3) (by norm_num) (by norm_num) (FinDist.pure .rain) (FinDist.pure .shine)

/-- The utility node's table: the sponsor is scored one exactly when the venue
matches the weather. -/
def picnicPayoff : Sky → Venue → ℝ
  | .rain, .indoors => 1
  | .rain, .outdoors => 0
  | .shine, .indoors => 0
  | .shine, .outdoors => 1

/-- The concrete three-node diagram. `@[reducible]` for the same reason
`protocol` carries it: without it `picnic.Forecast` does not reduce to `Sky` at
`instances` transparency and `rw` fails on the concrete diagram. -/
@[reducible]
def picnic : Diagram where
  Forecast := Sky
  Plan := Venue
  forecastLaw := skyLaw
  payoff := picnicPayoff
  planNonempty := ⟨.indoors⟩

/-- The utility node's table, as a function. -/
theorem picnic_payoff : picnic.payoff = picnicPayoff := rfl

/-- A decision rule that ignores the forecast. -/
def constantRule (venue : Venue) : (model picnic).Policy Agent.planner := fun view =>
  if hpending : view.1 = some Node.plan then
    ⟨some venue, by simp only [menuAt, if_pos hpending, Set.mem_setOf_eq]
                    exact ⟨venue, rfl⟩⟩
  else
    ⟨none, by simp only [menuAt, if_neg hpending]; rfl⟩

/-- The venue a forecast-responsive rule picks. -/
def responsiveVenue : Option Sky → Venue
  | some .rain => .indoors
  | some .shine => .outdoors
  | none => .indoors

/-- A decision rule that reads the parent its decision node observes. -/
def responsiveRule : (model picnic).Policy Agent.planner := fun view =>
  if hpending : view.1 = some Node.plan then
    ⟨some (responsiveVenue view.2), by
      simp only [menuAt, if_pos hpending, Set.mem_setOf_eq]
      exact ⟨responsiveVenue view.2, rfl⟩⟩
  else
    ⟨none, by simp only [menuAt, if_neg hpending]; rfl⟩

theorem ruleOf_constantRule (venue : Venue) (sky : Sky) :
    ruleOf picnic (constantRule venue) sky = venue := rfl

theorem ruleOf_responsiveRule (sky : Sky) :
    ruleOf picnic responsiveRule sky = responsiveVenue (some sky) := rfl

/-- The expectation of any observable under the chance node's law. -/
theorem expect_skyLaw (score : Sky → ℝ) :
    skyLaw.expect score = 1 / 3 * score .rain + (1 - 1 / 3) * score .shine := by
  rw [skyLaw, FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure]

theorem expect_constant_indoors :
    ((protocol picnic).runFor (chooserOf picnic (constantRule .indoors)) 3
      (protocol picnic).init).expect Stage.payoffValue = 1 / 3 := by
  rw [expect_payoffValue_runFor, expect_skyLaw]
  norm_num [ruleOf_constantRule, picnic_payoff, picnicPayoff]

theorem expect_constant_outdoors :
    ((protocol picnic).runFor (chooserOf picnic (constantRule .outdoors)) 3
      (protocol picnic).init).expect Stage.payoffValue = 2 / 3 := by
  rw [expect_payoffValue_runFor, expect_skyLaw]
  norm_num [ruleOf_constantRule, picnic_payoff, picnicPayoff]

theorem expect_responsive :
    ((protocol picnic).runFor (chooserOf picnic responsiveRule) 3
      (protocol picnic).init).expect Stage.payoffValue = 1 := by
  rw [expect_payoffValue_runFor, expect_skyLaw]
  norm_num [ruleOf_responsiveRule, responsiveVenue, picnic_payoff, picnicPayoff]

/-! ## The discriminating probes

Everything above would still be provable by an encoding that resolved the
decision node itself and ignored the policy — the outcome law would then be the
same for every policy, and `runFor_eq_intendedOutcome` would hold vacuously
because `ruleOf` would also be reading a value nobody used. These probes rule
that out. -/

/-- **Probe 1.** The compiled run law depends on the decision node's value: two
policies give two different outcome laws. The decision has not been collapsed
away. -/
theorem outcome_law_depends_on_decision :
    (protocol picnic).runFor (chooserOf picnic (constantRule .indoors)) 3
        (protocol picnic).init ≠
      (protocol picnic).runFor (chooserOf picnic (constantRule .outdoors)) 3
        (protocol picnic).init := by
  intro hequal
  have hscore := congrArg (fun law => FinDist.expect law Stage.payoffValue) hequal
  rw [expect_constant_indoors, expect_constant_outdoors] at hscore
  norm_num at hscore

/-- **Probe 2.** The decision node's *observation* is load-bearing too: a rule
that reads the parent achieves an expected utility no constant rule achieves,
so the compiled information state is not decorative. -/
theorem outcome_law_depends_on_observation (venue : Venue) :
    (protocol picnic).runFor (chooserOf picnic responsiveRule) 3
        (protocol picnic).init ≠
      (protocol picnic).runFor (chooserOf picnic (constantRule venue)) 3
        (protocol picnic).init := by
  intro hequal
  have hscore := congrArg (fun law => FinDist.expect law Stage.payoffValue) hequal
  rw [expect_responsive] at hscore
  cases venue with
  | indoors => rw [expect_constant_indoors] at hscore; norm_num at hscore
  | outdoors => rw [expect_constant_outdoors] at hscore; norm_num at hscore

/-- **Probe 3.** The responsive rule is genuinely a function of its parent: it
returns different values at the two forecasts. -/
theorem responsiveRule_not_constant :
    ruleOf picnic responsiveRule .rain ≠ ruleOf picnic responsiveRule .shine := by
  rw [ruleOf_responsiveRule, ruleOf_responsiveRule]
  simp [responsiveVenue]

/-- **Probe 4.** The chance node is nondegenerate: both of its values carry
mass, so the diagram is not secretly deterministic. -/
theorem skyLaw_rain : skyLaw.prob .rain = 1 / 3 := by
  simp [skyLaw, FinDist.prob_pure_eq_ite]

theorem skyLaw_shine : skyLaw.prob .shine = 2 / 3 := by
  simp [skyLaw, FinDist.prob_pure_eq_ite]
  norm_num

/-- **Probe 5.** The planner's view is a view: it does not see the utility
node's value, so the information state is a genuine restriction and not the
execution state in disguise. -/
theorem planner_view_ignores_payoff (D : Diagram) (forecast : D.Forecast)
    (plan : D.Plan) (first second : ℝ) :
    viewOf D Agent.planner (Stage.resolved forecast plan first) =
      viewOf D Agent.planner (Stage.resolved forecast plan second) := rfl

/-! ## Workarounds

Every language-specific concession the encoding needed, with a theorem attached
wherever one is possible. The three failures worth ruling out are fake players,
fake actions beyond the canonical no-op, and escape fields; the first three
entries answer them, and the rest are the honest remainder.

**1. Fake players: none.** The protocol's index type is `Agent`, which is the
diagram's own agent set. Chance is carried by the transition law at an
ownerless node (`owner_forecast`, `chanceLaw_init`), so no `nature` index
exists. `no_extra_agent` records that `Agent` has no third constructor.

**2. Fake actions beyond the canonical no-op: none.** `actionOf` gives the
planner exactly its decision node's alphabet and gives the sponsor `Empty`
(`sponsor_action_is_empty`); an agent with no decision node needed no padding
action, and `sponsorPolicy` is still a policy. At both non-decision nodes the
only legal joint action is `E.noop` (`legal_eq_noop_of_pending_ne_plan`), and
`transition` has no branch that invents an outcome for an illegal joint action:
the decision branch reads the planner's action out of the legality certificate
via `decisionValue`, and the exhausted-diagram branch is discharged by the
certificate's non-terminality conjunct. This cost a dependent match on the
certificate. Writing a `none` branch at the decision node and a self-loop at the
terminal state would be shorter, but both would invent an outcome for a joint
action that legality already excludes.

**3. Language-specific escape fields: none.** `ExecutionProtocol`,
`InfoSignals`, and `InformationModel` were used as declared. No field of
`Diagram` exists to satisfy the compiler except `planNonempty` — see 4.

**4. One well-formedness obligation the syntax did not state.**
`Diagram.planNonempty` exists because `ExecutionProtocol.progress` demands a
legal joint action at every non-terminal state, and an active agent with an
empty alphabet has none. This is a true statement about MAIDs that native
syntax leaves implicit, not an encoding artifact — but the encoding is what
forced it to be written down.

**5. The DAG had to be linearized, and the state space is its prefixes.**
`Stage` has four constructors for three nodes: one per prefix of the
topological order, including the empty prefix, which is `init`. The extra state
is unavoidable — `ExecutionProtocol` has a single `init` and chance must be
stepped *into*. For this diagram the topological order is unique, so nothing
was chosen arbitrarily. A MAID with two incomparable decision nodes would need
an arbitrary interleaving, and the compiled protocol would then assert an order
the diagram does not have. **That case is not tested here, and it is the one
place this experiment does not license a general claim.**

**6. The utility node costs an execution step, and `IsChance` cannot see the
difference.** The utility node is resolved by a no-op step whose law is a point
mass (`chanceLaw_planChosen`), so `planChosen_isChance` holds even though the
diagram has no chance there. `ExecutionProtocol.IsChance` means "play continues
and nobody acts", which conflates a chance node with a deterministic
administrative step. Nothing breaks, but a MAID's node kinds are not
recoverable from the protocol; only the law tells them apart. The run therefore
needs one unit of fuel per node, not per decision.

**7. The protocol has no payoff, so utility is an observable.** `Stage.resolved`
stores a real number and `Stage.payoffValue` reads it, with a default of zero
off the support. This is the intended layering — utilities live in `Core` — but
it means the compiled state carries a value that no execution rule ever
inspects, and it costs the state space its decidable equality.

**8. `runFor` is state-indexed; policies are history-indexed.** `chooserOf`
bridges the gap by reconstructing the planner's view from the stage
(`viewOf`). That is sound here only because the stage records the value of
every resolved node, which is why this diagram also satisfies the *state*-level
menu adequacy `menuAt_adequate` that `InformationModel` does not ask for.
`chooserOf_eq_jointAt` proves the bridge gives back exactly the
information-local policies, so no hidden state reaches a decision rule. A MAID
whose decision node did not observe all of its ancestors would still compile,
but its chooser could not be reconstructed this way.

**9. `pushView` is memoryless, and that is diagram-specific.** The private
signal recomputes the observed parent's value from the target state at every
step, so the information state never has to accumulate. With two decision nodes
and a non-observing second one, `pushInfo` would have to remember, and
`infoOf_eq_viewOf` would fail — as it should, since the information state would
no longer be a function of the state.

**10. The public signal is an addition to the syntax.** `InformationModel.menu`
ranges over `Option (Action i)`, so an information state must determine
*whether* its agent acts. The encoding therefore broadcasts the pending node.
In a MAID the diagram's shape is common knowledge, so this leaks nothing; but
native MAID syntax has no notion of a public signal, and this one exists only
because the menu decides participation. This is the cost the information model
already recorded, arriving here from a second language.

**11. An agent with no decision node still needs information data.** `Whisper`,
`View`, `menuAt`, and `sponsorPolicy` all have a sponsor case, because the
information model is indexed by every agent. All four are trivial — `Unit`,
`Unit`, `{none}`, and the constant `none` — and none of them is a fake action
or a fake player, but the diagram does not contain them: an agent that owns
only a utility node observes nothing and chooses nothing. This is the closest
the encoding comes to padding, and it is padding of the *information* model,
not of the players or the actions.

**Verdict.** MAID shares `ExecutionProtocol` and `InformationModel` honestly on
this slice: entries 1-3 are clean, and none of entries 4-11 is a fake player, a
fake action, or an escape field. Entry 5 bounds the claim: a single-chain MAID
was compiled, and a MAID with incomparable decision nodes has not been. -/

/-- The agent set has no third constructor: nothing was added for chance. -/
theorem no_extra_agent (agent : Agent) :
    agent = Agent.planner ∨ agent = Agent.sponsor := by
  cases agent
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- An agent with no decision node needed no action alphabet at all. -/
theorem sponsor_action_is_empty (D : Diagram) :
    (protocol D).Action Agent.sponsor = Empty := rfl

/-- And the planner's alphabet is exactly its decision node's, with nothing
appended. -/
theorem planner_action_is_plan (D : Diagram) :
    (protocol D).Action Agent.planner = D.Plan := rfl

end GameTheory.Languages.MAID
