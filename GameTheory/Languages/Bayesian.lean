/-
# Bayesian games through execution and information

This module compiles the static data of `BayesianGame` through the accepted
execution/information boundary. Chance draws the type profile, every player is
then active simultaneously, and player `i` observes only `types i`.

The module deliberately imports no utility, preference, or equilibrium module.
It establishes syntax, information locality, and induced outcome laws; ordinary
static solution concepts apply above this compiler.
-/

import GameTheory.Core.Bayesian
import GameTheory.Protocol.Strategic

noncomputable section

namespace GameTheory.Languages.Bayesian

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open ExecutionProtocol

universe uι ut ua

variable {ι : Type uι}

/-- The two-step Harsanyi execution: chance chooses types, the players choose
actions simultaneously, and the realized pair is retained at the terminal
state. -/
inductive State (B : BayesianGame ι)
  | initial
  | typed (types : ∀ i, B.Ty i)
  | finished (types : ∀ i, B.Ty i) (actions : ∀ i, B.Act i)

namespace State

variable {B : BayesianGame ι}

/-- Recover an action from a joint contribution known to contain an available
action at every coordinate. -/
private def actionOfJoint (joint : ∀ i, Option (B.Act i))
    (hlegal : IsLegalJoint (fun _ => True) (fun _ => Set.univ) joint)
    (i : ι) : B.Act i :=
  match h : joint i with
  | some action => action
  | none => False.elim (by
      have hi := hlegal i
      rw [h] at hi
      exact hi trivial)

@[simp]
private theorem actionOfJoint_some (actions : ∀ i, B.Act i)
    (hlegal : IsLegalJoint (fun _ => True) (fun _ => Set.univ)
      (fun i => some (actions i))) (i : ι) :
    actionOfJoint (fun i => some (actions i)) hlegal i = actions i := rfl

end State

/-- The execution protocol underlying a Bayesian game. Nonempty action
carriers are needed only to witness progress at the simultaneous move, not by
the static game data. -/
@[reducible]
def execution (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)] :
    ExecutionProtocol ι where
  State := State B
  Action := B.Act
  init := .initial
  active state _ :=
    match state with
    | .typed _ => True
    | _ => False
  available _ _ := Set.univ
  terminal state :=
    match state with
    | .finished _ _ => True
    | _ => False
  step state joint :=
    match state with
    | .initial => B.prior.map State.typed
    | .typed types =>
        FinDist.pure (.finished types
          (State.actionOfJoint joint.1 joint.2.2))
    | .finished types actions => FinDist.pure (.finished types actions)
  progress := by
    intro state hterm
    cases state with
    | initial =>
        refine ⟨fun _ => none, fun i => ?_⟩
        simp
    | typed types =>
        refine ⟨fun i => some (Classical.choice (inferInstance : Nonempty (B.Act i))),
          fun i => ?_⟩
        exact ⟨trivial, Set.mem_univ _⟩
    | finished types actions =>
        exact False.elim (hterm trivial)

/-- The publicly visible phase contains no type information. -/
inductive Phase
  | waiting
  | acting
  | done
  deriving DecidableEq

/-- Player `i`'s local information state. Only the acting state carries a
type, and that type is `i`'s own coordinate. -/
inductive View (B : BayesianGame ι) (i : ι)
  | waiting
  | acting (ownType : B.Ty i)
  | done

/-- The phase visible at an execution state. -/
def phaseOfState {B : BayesianGame ι} : State B → Phase
  | .initial => .waiting
  | .typed _ => .acting
  | .finished _ _ => .done

/-- The local information state associated with a reached execution state. -/
def viewOfState {B : BayesianGame ι} (i : ι) : State B → View B i
  | .initial => .waiting
  | .typed types => .acting (types i)
  | .finished _ _ => .done

/-- A transition privately reveals only player `i`'s type coordinate. -/
def privateSignal {B : BayesianGame ι} [∀ i, Nonempty (B.Act i)] (i : ι)
    (event : StepEvent (execution B)) : Option (B.Ty i) :=
  match event.target with
  | .typed types => some (types i)
  | _ => none

/-- Public and private observations for the two-step protocol. -/
@[reducible]
def signals (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)] :
    InfoSignals (execution B) where
  PublicSignal := Phase
  PrivateSignal i := Option (B.Ty i)
  initialPublic := .waiting
  initialPrivate _ := none
  publicSignal event := phaseOfState event.target
  privateSignal := privateSignal
  InfoState := View B
  initInfo _ _ _ := .waiting
  pushInfo _ _ _ privateSignalValue publicSignalValue :=
    match publicSignalValue, privateSignalValue with
    | .acting, some ownType => .acting ownType
    | .done, _ => .done
    | _, _ => .waiting

/-- The signal update computes exactly the local view of the reached state. -/
theorem signals_push_event (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)]
    (i : ι) (prior : View B i)
    (event : StepEvent (execution B)) :
    (signals B).pushInfo i prior (event.joint i)
        ((signals B).privateSignal i event) ((signals B).publicSignal event) =
      viewOfState i event.target := by
  obtain ⟨source, joint, isLegal, target, realized⟩ := event
  cases target <;> rfl

/-- Every history leaves each player with exactly the intended local view of
its reached state. In particular, the acting view contains one type coordinate,
not the hidden full profile. -/
theorem infoOf_eq_viewOfState (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)]
    (i : ι) {state : (execution B).State}
    (trace : Trace (execution B) state) :
    (signals B).infoOf i trace = viewOfState i state := by
  cases trace with
  | start => rfl
  | extend prior joint isLegal realized =>
      rw [InfoSignals.infoOf_extend]
      exact signals_push_event B i _ ⟨_, joint, isLegal, _, realized⟩

/-- The local menu: no contribution off the move, and any action while acting.
Its argument is a `View`, never an execution state. -/
def menu (B : BayesianGame ι) (i : ι) : View B i → Set (Option (B.Act i))
  | .acting _ => { choice | ∃ action, choice = some action }
  | _ => {none}

/-- The local menu agrees with execution legality after every history. -/
theorem menu_adequate (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)]
    (i : ι) {state : (execution B).State}
    (trace : Trace (execution B) state)
    (choice : Option (B.Act i)) :
    choice ∈ menu B i ((signals B).infoOf i trace) ↔
      LegalOption (execution B) state i choice := by
  rw [infoOf_eq_viewOfState B i trace]
  cases state <;> cases choice <;> simp [menu, viewOfState, LegalOption, execution]

/-- The information model induced by a Bayesian game. -/
@[reducible]
def informationModel (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)] :
    InformationModel (execution B) where
  toInfoSignals := signals B
  menu := menu B
  menu_adequate := by
    intro i _ trace choice
    exact menu_adequate B i trace choice

namespace Policy

variable {B : BayesianGame ι} [∀ i, Nonempty (B.Act i)]

/-- Turn a type-contingent plan into a policy. Waiting and terminal choices are
forced; the only genuine choice is the action at an own-type view. -/
def ofPlan {i : ι} (plan : B.Ty i → B.Act i) :
    (informationModel B).Policy i :=
  fun info =>
    match show View B i from info with
    | .waiting => ⟨none, by simp [menu]⟩
    | .acting ownType =>
        ⟨some (plan ownType), by simp [menu]⟩
    | .done => ⟨none, by simp [menu]⟩

/-- At an acting view the menu certificate says the policy's option is
inhabited. -/
theorem act_isSome {i : ι} (policy : (informationModel B).Policy i)
    (ownType : B.Ty i) :
    (policy.act (View.acting ownType)).isSome := by
  have hmem := policy.act_mem_menu (View.acting ownType)
  obtain ⟨action, haction⟩ : ∃ action,
      policy.act (View.acting ownType) = some action := by
    simpa [menu] using hmem
  rw [haction]
  trivial

/-- Read the contingent plan implemented by an information-local policy. -/
def toPlan {i : ι} (policy : (informationModel B).Policy i) :
    B.Ty i → B.Act i :=
  fun ownType =>
    (policy.act (View.acting ownType)).get (act_isSome policy ownType)

@[simp]
theorem toPlan_ofPlan {i : ι} (plan : B.Ty i → B.Act i) :
    toPlan (ofPlan plan) = plan := by
  funext ownType
  rfl

theorem act_waiting {i : ι} (policy : (informationModel B).Policy i) :
    policy.act View.waiting = none := by
  simpa [menu] using policy.act_mem_menu View.waiting

theorem act_done {i : ι} (policy : (informationModel B).Policy i) :
    policy.act View.done = none := by
  simpa [menu] using policy.act_mem_menu View.done

private theorem ofPlan_toPlan_act {i : ι}
    (policy : (informationModel B).Policy i) (info : View B i) :
    (ofPlan (toPlan policy)).act info = policy.act info := by
  cases info with
  | waiting =>
      show none = policy.act View.waiting
      exact (act_waiting policy).symm
  | acting ownType =>
      show some (toPlan policy ownType) =
        policy.act (View.acting ownType)
      exact Option.some_get _
  | done =>
      show none = policy.act View.done
      exact (act_done policy).symm

@[simp]
theorem ofPlan_toPlan {i : ι} (policy : (informationModel B).Policy i) :
    ofPlan (toPlan policy) = policy := by
  funext info
  apply Subtype.ext
  exact ofPlan_toPlan_act policy info

/-- Information-local policies and type-contingent plans are exactly
equivalent, not merely equal on reachable states. -/
def equivPlan (i : ι) :
    (informationModel B).Policy i ≃ (B.Ty i → B.Act i) where
  toFun := toPlan
  invFun := ofPlan
  left_inv := ofPlan_toPlan
  right_inv := toPlan_ofPlan

end Policy

/-- Apply the policy/plan equivalence coordinatewise. -/
def policyProfileOfPlan (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)]
    (plan : Profile B.signature) :
    Profile (informationModel B).strategicSignature :=
  fun i => Policy.ofPlan (plan i)

/-- Recover a static contingent plan from a profile of local policies. -/
def planOfPolicyProfile (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)]
    (policies : Profile (informationModel B).strategicSignature) :
    Profile B.signature :=
  fun i => Policy.toPlan (policies i)

@[simp]
theorem planOfPolicyProfile_policyProfileOfPlan (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)] (plan : Profile B.signature) :
    planOfPolicyProfile B (policyProfileOfPlan B plan) = plan := by
  funext i ownType
  rfl

@[simp]
theorem policyProfileOfPlan_planOfPolicyProfile (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)]
    (policies : Profile (informationModel B).strategicSignature) :
    policyProfileOfPlan B (planOfPolicyProfile B policies) = policies := by
  funext i
  exact Policy.ofPlan_toPlan (policies i)

@[simp]
theorem planOfPolicyProfile_update (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)] [DecidableEq ι]
    (policies : Profile (informationModel B).strategicSignature) (who : ι)
    (replacement : (informationModel B).Policy who) :
    planOfPolicyProfile B (Profile.update policies who replacement) =
      Profile.update (planOfPolicyProfile B policies) who
        (Policy.toPlan replacement) := by
  funext i ownType
  by_cases hi : i = who
  · subst hi
    simp [planOfPolicyProfile]
  · simp [planOfPolicyProfile, Profile.update_of_ne _ _ hi]

/-- Read a static outcome from a completed execution state. -/
def outcomeOfState {B : BayesianGame ι} :
    State B → Option B.signature.Outcome
  | .finished types actions => some (types, actions)
  | _ => none

/-- The state-indexed chooser corresponding to a contingent plan. It is used
only to calculate the state shadow of the information-local history run. -/
def chooserOfPlan (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)]
    (plan : Profile B.signature) : (execution B).Chooser :=
  fun state hterm =>
    match state with
    | .initial =>
        ⟨fun _ => none, hterm, by
          intro i
          simp⟩
    | .typed types =>
        ⟨fun i => some (plan i (types i)), hterm, by
          intro i
          exact ⟨trivial, Set.mem_univ _⟩⟩
    | .finished _ _ => False.elim (hterm trivial)

/-- On plan-generated policies the history chooser is state based: at the
acting state it reads exactly the own-type coordinate already present in the
player's local view. -/
theorem historyChooser_policyProfileOfPlan (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)] (plan : Profile B.signature) :
    (informationModel B).historyChooser (policyProfileOfPlan B plan) =
      (chooserOfPlan B plan).toHistoryChooser := by
  apply funext
  rintro ⟨state, trace⟩
  apply funext
  intro hterm
  apply Subtype.ext
  funext i
  show (policyProfileOfPlan B plan i).act
      ((informationModel B).infoOf i trace) =
    (chooserOfPlan B plan state hterm).1 i
  have hinfo : (informationModel B).infoOf i trace =
      viewOfState i state :=
    infoOf_eq_viewOfState B i trace
  rw [hinfo]
  cases state with
  | initial => rfl
  | typed types => rfl
  | finished types actions =>
      exact False.elim (hterm trivial)

/-- Two steps under the chooser produce exactly the direct form's realized
type/action pair, now stored in a terminal execution state. -/
theorem runFor_chooserOfPlan_two (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)] (plan : Profile B.signature) :
    (execution B).runFor (chooserOfPlan B plan) 2 .initial =
      B.prior.map fun types => State.finished types (B.actionsOf plan types) := by
  simp [ExecutionProtocol.runFor, execution, chooserOfPlan,
    FinDist.map_eq_bind]
  refine FinDist.bind_congr fun types _ => ?_
  apply congrArg FinDist.pure
  congr

/-- The protocol-backed strategic form, retaining only its terminal Bayesian
outcome. Horizon two is sufficient by construction. -/
@[reducible]
def toProtocolForm (B : BayesianGame ι) [∀ i, Nonempty (B.Act i)] :
    GameForm ι :=
  ((informationModel B).toGameForm 2).mapOutcome
    (fun history => outcomeOfState history.state)

/-- The protocol compiler and the direct Bayesian form induce exactly the same
outcome law under the policy/plan equivalence. The optional codomain records
that arbitrary short histories need not be terminal; this two-step law is
supported entirely on `some`. -/
theorem toProtocolForm_play_policyProfileOfPlan (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)] (plan : Profile B.signature) :
    (toProtocolForm B).play (policyProfileOfPlan B plan) =
      (B.toForm.play plan).map some := by
  have hshadow := map_state_runHistoryFor (chooserOfPlan B plan) 2
    (execution B).initHistory
  rw [← historyChooser_policyProfileOfPlan B plan] at hshadow
  show
    (FinDist.map (fun history => outcomeOfState history.state)
      ((informationModel B).run (policyProfileOfPlan B plan) 2)) =
        (B.prior.map fun types => (types, B.actionsOf plan types)).map some
  rw [InformationModel.run, InformationModel.runFrom]
  calc
    FinDist.map (fun history => outcomeOfState history.state)
        ((execution B).runHistoryFor
          ((informationModel B).historyChooser (policyProfileOfPlan B plan)) 2
          (execution B).initHistory) =
      FinDist.map outcomeOfState
        (FinDist.map ExecutionProtocol.History.state
          ((execution B).runHistoryFor
            ((informationModel B).historyChooser (policyProfileOfPlan B plan)) 2
            (execution B).initHistory)) := by
              rw [FinDist.map_comp]
              rfl
    _ = FinDist.map outcomeOfState
        ((execution B).runFor (chooserOfPlan B plan) 2 .initial) := by
          simpa using congrArg (FinDist.map outcomeOfState) hshadow
    _ = (B.prior.map fun types => (types, B.actionsOf plan types)).map some := by
          rw [runFor_chooserOfPlan_two]
          rw [FinDist.map_comp, FinDist.map_comp]
          rfl

/-- The same play law for an arbitrary local-policy profile, after recovering
its exactly equivalent contingent plan. -/
theorem toProtocolForm_play (B : BayesianGame ι)
    [∀ i, Nonempty (B.Act i)]
    (policies : Profile (informationModel B).strategicSignature) :
    (toProtocolForm B).play policies =
      (B.toForm.play (planOfPolicyProfile B policies)).map some := by
  calc
    (toProtocolForm B).play policies =
        (toProtocolForm B).play
          (policyProfileOfPlan B (planOfPolicyProfile B policies)) := by
            rw [policyProfileOfPlan_planOfPolicyProfile]
    _ = (B.toForm.play (planOfPolicyProfile B policies)).map some :=
      toProtocolForm_play_policyProfileOfPlan B _

end GameTheory.Languages.Bayesian
