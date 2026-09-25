/-
Insufficient continuation fuel can make sequential rationality inconsistent.
One player first takes a forced step, then chooses a short payoff of one or a
long payoff of two. Two steps of fuel see different terminal opportunities at
the two decision sites. This is EXP-121's hostile finite EFG boundary.
-/

import GameTheory.Analysis.Protocol.EFG

noncomputable section

namespace GameTheory.Tests.SequentialExistenceBoundary

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

local syntax:max "finiteExpect" term:max term:max : term
local macro_rules
  | `(term| finiteExpect $law:term $payoff:term) =>
      `(expect $law $payoff (payoffIntegrable_of_finite $law $payoff))

set_option backward.isDefEq.respectTransparency false in
inductive State
  | root | choice | short | waiting | long
  deriving DecidableEq, Fintype

def State.running : State → Prop
  | .root | .choice | .waiting => True
  | _ => False

def State.allowed : State → Set Bool
  | .choice => Set.univ
  | _ => {false}

def next : State → Bool → State
  | .root, _ => .choice
  | .choice, false => .short
  | .choice, true => .waiting
  | .waiting, _ => .long
  | .short, _ => .short
  | .long, _ => .long

@[reducible] def execution : ExecutionProtocol Unit where
  State := State
  Action _ := Bool
  init := .root
  active state _ := state.running
  available state _ := state.allowed
  terminal state := ¬ state.running
  step state joint := PMF.pure (next state ((joint.1 ()).getD false))
  progress := by
    intro state running
    refine ⟨fun _ => some false, ?_⟩
    intro who
    cases state <;> simp_all [State.running, State.allowed]

theorem legal_joint {state : State} {joint : Unit → Option Bool}
    (legal : execution.Legal state joint) :
    ∃ action, joint = (fun _ => some action) ∧ action ∈ state.allowed := by
  have active : execution.active state () := by
    simpa using legal.1
  obtain ⟨action, haction⟩ := LegalOption.exists_eq_some_of_active
    (joint ()) (execution.legalOption_of_legal legal ()) active
  refine ⟨action, ?_, ?_⟩
  · funext who
    cases who
    exact haction
  · have h := execution.legalOption_of_legal legal ()
    rw [haction] at h
    exact h.2

theorem no_return (source : State) (joint : Unit → Option Bool)
    (legal : execution.Legal source joint) :
    State.root ∉ (execution.step source ⟨joint, legal⟩).support := by
  obtain ⟨action, rfl, _⟩ := legal_joint legal
  cases source <;> cases action <;> simp [execution, next]

theorem predecessor_unique {target first second : State}
    {firstJoint secondJoint : Unit → Option Bool}
    (firstLegal : execution.Legal first firstJoint)
    (secondLegal : execution.Legal second secondJoint)
    (firstReached : target ∈ (execution.step first ⟨firstJoint, firstLegal⟩).support)
    (secondReached : target ∈ (execution.step second ⟨secondJoint, secondLegal⟩).support) :
    first = second ∧ firstJoint = secondJoint := by
  obtain ⟨firstAction, rfl, hfirst⟩ := legal_joint firstLegal
  obtain ⟨secondAction, rfl, hsecond⟩ := legal_joint secondLegal
  have hfirstRun := firstLegal.1
  have hsecondRun := secondLegal.1
  simp only [execution, PMF.mem_support_iff, Option.getD_some] at firstReached secondReached
  cases first <;> cases second <;> cases firstAction <;> cases secondAction <;>
    simp_all [State.allowed, State.running, next]

theorem treeShaped : execution.IsTreeShaped :=
  isTreeShaped_of_predecessor_unique no_return predecessor_unique

theorem trace_length : ∀ {state : State} (trace : execution.Trace state),
    trace.length = match state with
      | .root => 0 | .choice => 1 | .short | .waiting => 2 | .long => 3
  | _, .start => rfl
  | _, .extend (source := source) (target := target) prior joint legal realized => by
      have ih := trace_length prior
      obtain ⟨action, rfl, allowed⟩ := legal_joint legal
      have running := legal.1
      simp only [execution, PMF.mem_support_iff, Option.getD_some] at realized
      have htarget : target = next source action := by
        simpa [PMF.pure_apply] using realized
      cases htarget
      cases source <;> cases action <;>
        simp_all [State.running, State.allowed, next, Trace.length]
termination_by _ trace => trace.length
decreasing_by simp [Trace.length]

/-- A uniform bound covers all legal histories, including off-path choices. -/
theorem bounded_three : execution.BoundedHorizon 3 := by
  intro state trace lengthBound
  rw [trace_length trace] at lengthBound
  cases state <;> simp_all [State.running]

@[reducible] def signals : InfoSignals execution where
  PublicSignal := Unit
  PrivateSignal _ := State
  initialPublic := ()
  initialPrivate _ := .root
  publicSignal _ := ()
  privateSignal _ event := event.target
  InfoState _ := State
  initInfo _ state _ := state
  pushInfo _ _ _ state _ := state

@[simp] theorem infoOf (who : Unit) :
    ∀ {state : State} (trace : execution.Trace state), signals.infoOf who trace = state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

@[reducible] def information : InformationModel execution where
  toInfoSignals := signals
  menu who state := {choice | LegalOption execution state who choice}
  menu_adequate := by
    intro who state trace action
    simp only [Set.mem_ofPred, infoOf]

local instance (who : Unit) (state : State) :
    Fintype (information.Choice who state) := by
  classical
  infer_instance

local instance (state : State) :
    Fintype {joint : Unit → Option Bool // execution.Legal state joint} := by
  classical
  infer_instance

theorem perfectRecall : information.PerfectRecall := by
  intro who first second firstTrace secondTrace equalInfo
  have equalState : first = second := by simpa using equalInfo
  subst second
  have equalTrace := (treeShaped first).elim firstTrace secondTrace
  subst secondTrace
  rfl

/-- The information actually distinguishes every complete history. -/
theorem history_eq_of_info_eq (first second : execution.History)
    (equalInfo : information.infoOf () first.trace = information.infoOf () second.trace) :
    first = second := by
  rcases first with ⟨firstState, firstTrace⟩
  rcases second with ⟨secondState, secondTrace⟩
  have equalState : firstState = secondState := by simpa using equalInfo
  subst secondState
  congr 1
  exact (treeShaped firstState).elim firstTrace secondTrace

theorem antichain : information.DecisionInformationAntichain :=
  information.decisionInformationAntichain_of_perfectRecall perfectRecall

@[reducible] def game : Languages.EFG.Game Unit where
  execution := execution
  information := information
  treeShaped := treeShaped
  singleMover := by intros; exact Subsingleton.elim _ _

local instance : Fintype execution.History := game.historyFintype

def forcedChoice (state : State) : information.Choice () state :=
  match state with
  | .root | .choice | .waiting => ⟨some false, by simp [LegalOption, State.running, State.allowed]⟩
  | .short | .long => ⟨none, by simp [LegalOption, State.running]⟩

/-- All raw information states, including terminal observations, have a menu. -/
theorem nonempty_menus (who : Unit) (state : State) : Nonempty (information.Choice who state) := by
  cases who
  exact ⟨forcedChoice state⟩

def policy (long : Bool) : information.BehavioralPolicy ()
  | .choice => PMF.pure ⟨some long, by simp [LegalOption, State.running, State.allowed]⟩
  | state => PMF.pure (forcedChoice state)

theorem root_legal : execution.Legal .root (fun _ => some false) := by
  constructor
  · simp [State.running]
  · intro who; simp [State.running, State.allowed]

@[reducible] def rootHistory : execution.History := execution.initHistory

@[reducible] def choiceHistory : execution.History :=
  rootHistory.extend (target := .choice) root_legal (by simp [execution, next])

theorem choice_long_legal : execution.Legal .choice (fun _ => some true) := by
  constructor
  · simp [State.running]
  · intro who; simp [State.running, State.allowed]

@[reducible] def waitingHistory : execution.History :=
  choiceHistory.extend (target := .waiting) choice_long_legal
    (by show State.waiting ∈ (PMF.pure State.waiting).support; simp)

/-- Two steps are insufficient because the long branch is still running. -/
theorem not_bounded_two : ¬ execution.BoundedHorizon 2 := by
  intro bounded
  have stopped := bounded .waiting waitingHistory.trace (by decide)
  exact stopped trivial

def rootSite : information.InformationSite () :=
  information.informationSite () rootHistory false (by simp [State.running])
    (by show True ∧ false ∈ ({false} : Set Bool); simp)

def choiceSite : information.InformationSite () :=
  information.informationSite () choiceHistory false (by show ¬ ¬ True; simp)
    (by show True ∧ false ∈ (Set.univ : Set Bool); simp)

def statePayoff : State → ℝ
  | .short => 1
  | .long => 2
  | _ => 0

def payoff (_ : Unit) (history : execution.History) : ℝ := statePayoff history.state

def localLaw (profile : (who : Unit) → information.BehavioralPolicy who) (state : State) :
    PMF (Option Bool) := (profile () state).map Subtype.val

set_option backward.isDefEq.respectTransparency false in
theorem step_value (profile : (who : Unit) → information.BehavioralPolicy who)
    (fuel : ℕ) (history : execution.History) (running : ¬ execution.terminal history.state)
    (value : State → ℝ)
    (continuation : ∀ nextHistory : execution.History,
      finiteExpect (information.runBehavioralFrom profile fuel nextHistory) (payoff ()) =
        value nextHistory.state) :
    finiteExpect (information.runBehavioralFrom profile (fuel + 1) history) (payoff ()) =
      finiteExpect (localLaw profile history.state)
        (fun choice => value (next history.state (choice.getD false))) := by
  rw [information.runBehavioralFrom_succ_of_not_terminal profile fuel running,
    information.behavioralJoint_eq_map_of_at_most_one_active profile history.trace running ()
      (fun who _ => Subsingleton.elim _ _)]
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)
    (fun _ => payoffIntegrable_of_finite _ _),
    expect_map _ _ _ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)]
  calc
    _ = finiteExpect (profile () (information.infoOf () history.trace))
        (fun choice => value (next history.state (choice.1.getD false))) := by
      apply expect_congr_on_support
      intro choice _
      simp only [execution, PMF.pure_bindOnSupport]
      simp only [Function.comp_apply]
      rw [continuation]
      simp [singletonJoint]
    _ = finiteExpect (localLaw profile (information.infoOf () history.trace))
        (fun choice => value (next history.state (choice.getD false))) := by
      rw [localLaw]
      exact (expect_map Subtype.val
        (profile () (information.infoOf () history.trace))
        (fun choice => value (next history.state (choice.getD false)))
        (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).symm
    _ = _ := by rw [show information.infoOf () history.trace = history.state from infoOf () _]

def shortWeight (profile : (who : Unit) → information.BehavioralPolicy who) : ℝ :=
  finiteExpect (localLaw profile State.choice)
    (fun choice => if choice = some false then 1 else 0)

theorem shortWeight_le_one (profile : (who : Unit) → information.BehavioralPolicy who) :
    shortWeight profile ≤ 1 := by
  unfold shortWeight
  apply expect_le_const
  intro choice _
  split <;> norm_num

theorem choice_cases (choice : information.Choice () State.choice) :
    choice.1 = some false ∨ choice.1 = some true := by
  rcases choice with ⟨choice, legal⟩
  cases choice with
  | none => exact False.elim (legal trivial)
  | some action => cases action <;> simp

set_option backward.isDefEq.respectTransparency false in
theorem value_one (profile : (who : Unit) → information.BehavioralPolicy who)
    (history : execution.History) :
    finiteExpect (information.runBehavioralFrom profile 1 history) (payoff ()) =
      match history.state with
      | .root => 0
      | .choice => shortWeight profile
      | .short => 1
      | .waiting | .long => 2 := by
  have continuation (nextHistory : execution.History) :
      finiteExpect (information.runBehavioralFrom profile 0 nextHistory) (payoff ()) =
        statePayoff nextHistory.state := by
    rw [InformationModel.runBehavioralFrom, ExecutionProtocol.runRandomizedFor,
      expect_pure]
    rfl
  cases stateEq : history.state with
  | root =>
      rw [step_value profile 0 history (by simp [stateEq, State.running]) statePayoff continuation]
      simp [stateEq, next, statePayoff, expect_constant]
  | choice =>
      rw [step_value profile 0 history (by simp [stateEq, State.running]) statePayoff continuation]
      simp only [stateEq, shortWeight]
      apply expect_congr_on_support
      intro choice supported
      rw [localLaw, PMF.support_map] at supported
      obtain ⟨actual, _, rfl⟩ := supported
      rcases choice_cases actual with h | h <;> simp [h, next, statePayoff]
  | short =>
      rw [information.runBehavioralFrom_of_terminal profile 1 (by simp [stateEq, State.running]),
        expect_pure]
      simp [payoff, stateEq, statePayoff]
  | waiting =>
      rw [step_value profile 0 history (by simp [stateEq, State.running]) statePayoff continuation]
      simp [stateEq, next, statePayoff, expect_constant]
  | long =>
      rw [information.runBehavioralFrom_of_terminal profile 1 (by simp [stateEq, State.running]),
        expect_pure]
      simp [payoff, stateEq, statePayoff]

theorem value_two_root (profile : (who : Unit) → information.BehavioralPolicy who)
    (history : execution.History) (stateEq : history.state = .root) :
    finiteExpect (information.runBehavioralFrom profile 2 history) (payoff ()) =
      shortWeight profile := by
  rw [step_value profile 1 history (by simp [stateEq, State.running])
    (fun state => match state with
      | .root => 0 | .choice => shortWeight profile | .short => 1 | .waiting | .long => 2)
    (value_one profile)]
  simp [stateEq, next, expect_constant]

set_option backward.isDefEq.respectTransparency false in
theorem value_two_choice (profile : (who : Unit) → information.BehavioralPolicy who)
    (history : execution.History) (stateEq : history.state = .choice) :
    finiteExpect (information.runBehavioralFrom profile 2 history) (payoff ()) =
      2 - shortWeight profile := by
  rw [step_value profile 1 history (by simp [stateEq, State.running])
    (fun state => match state with
      | .root => 0 | .choice => shortWeight profile | .short => 1 | .waiting | .long => 2)
    (value_one profile)]
  simp only [stateEq, shortWeight]
  rw [← expect_constant (localLaw profile State.choice) 2
    (payoffIntegrable_of_finite _ _), ← expect_sub]
  apply expect_congr_on_support
  intro choice supported
  rw [localLaw, PMF.support_map] at supported
  obtain ⟨actual, _, rfl⟩ := supported
  rcases choice_cases actual with h | h <;>
    norm_num [h, next, expect_constant]

theorem update_eq (assessment : information.BehavioralAssessment)
    (alternative : information.BehavioralPolicy ()) :
    Profile.update (sig := information.behavioralSignature)
      assessment.strategy () alternative = (fun _ => alternative) := by
  funext who
  cases who
  simp

private theorem continuationValue_eq_constant
    (assessment : information.BehavioralAssessment)
    (site : information.InformationSite ())
    (alternative : information.BehavioralPolicy ())
    (hbase : (assessment.continuationContext site (payoff ()) 2).IntegrableAt alternative)
    (value : ℝ)
    (hvalue : ∀ history : information.InformationHistory () site.1,
      expect
        (information.runBehavioralFrom (fun _ => alternative) 2 history.1)
        (payoff ()) (payoffIntegrable_of_finite _ _) = value) :
    (assessment.continuationContext site (payoff ()) 2).value alternative hbase = value := by
  let belief := assessment.belief () site
  let q := fun history : information.InformationHistory () site.1 =>
    information.runBehavioralFrom (fun _ => alternative) 2 history.1
  let actualLaw := belief.bind fun history =>
    information.runBehavioralFrom
      (Profile.update (sig := information.behavioralSignature)
        assessment.strategy () alternative) 2 history.1
  let canonicalLaw := belief.bind q
  have hlaw : actualLaw = canonicalLaw := by
    apply congrArg (fun kernel => belief.bind kernel)
    funext history
    exact congrArg (fun profile => information.runBehavioralFrom profile 2 history.1)
      (update_eq assessment alternative)
  have hcanonical : PayoffIntegrable canonicalLaw (payoff ()) :=
    payoffIntegrable_congr_law hlaw hbase
  have hconditional : ∀ history, PayoffIntegrable (q history) (payoff ()) :=
    fun _ => payoffIntegrable_of_finite _ _
  have hctx :=
    InformationModel.BehavioralAssessment.continuationContext_value
      assessment site (payoff ()) 2 alternative hbase
  calc
    _ = expect actualLaw (payoff ()) hbase := hctx
    _ = expect canonicalLaw (payoff ()) hcanonical :=
      expect_congr_law hlaw (payoff ()) hbase hcanonical
    _ = expect belief (fun history => expect (q history) (payoff ())
          (hconditional history))
          (payoffIntegrable_bind_conditionalExpectation belief q (payoff ())
            hcanonical hconditional) :=
      expect_bind_tower belief q (payoff ()) hcanonical hconditional
    _ = expect belief (fun _ => value) (payoffIntegrable_constant belief value) := by
      apply expect_congr_on_support
      intro history _
      exact hvalue history
    _ = value := expect_constant belief value (payoffIntegrable_constant belief value)

theorem context_value_root (assessment : information.BehavioralAssessment)
    (alternative : information.BehavioralPolicy ())
    (h : (assessment.continuationContext rootSite (payoff ()) 2).IntegrableAt alternative) :
  (assessment.continuationContext rootSite (payoff ()) 2).value alternative h =
      shortWeight (fun _ => alternative) := by
  apply continuationValue_eq_constant assessment rootSite alternative h
    (shortWeight (fun _ => alternative))
  intro history
  apply value_two_root
  have hstate : signals.infoOf () history.1.trace = State.root := history.2
  simpa only [infoOf] using hstate

theorem context_value_choice (assessment : information.BehavioralAssessment)
    (alternative : information.BehavioralPolicy ())
    (h : (assessment.continuationContext choiceSite (payoff ()) 2).IntegrableAt alternative) :
  (assessment.continuationContext choiceSite (payoff ()) 2).value alternative h =
      2 - shortWeight (fun _ => alternative) := by
  apply continuationValue_eq_constant assessment choiceSite alternative h
    (2 - shortWeight (fun _ => alternative))
  intro history
  apply value_two_choice
  have hstate : signals.infoOf () history.1.trace = State.choice := history.2
  simpa only [infoOf] using hstate

@[simp] theorem shortWeight_short : shortWeight (fun _ => policy false) = 1 := by
  simp [shortWeight, localLaw, policy, PMF.pure_map, expect_pure]

@[simp] theorem shortWeight_long : shortWeight (fun _ => policy true) = 0 := by
  simp [shortWeight, localLaw, policy, PMF.pure_map, expect_pure]

/-- The two decision sites impose incompatible whole-policy optimality
conditions when each is evaluated with only two steps of continuation fuel. -/
theorem no_sequentially_rational_assessment
    (assessment : information.BehavioralAssessment) :
    ¬ assessment.IsSequentiallyRationalWithin payoff 2 := by
  intro rational
  rcases rational () rootSite with ⟨hroot, hrootAllowed, hrootOptimal⟩
  rcases rational () choiceSite with ⟨hchoice, hchoiceAllowed, hchoiceOptimal⟩
  have hrootAlt := hrootAllowed (policy false) (Set.mem_univ _)
  have hchoiceAlt := hchoiceAllowed (policy true) (Set.mem_univ _)
  have atRoot := hrootOptimal (policy false) (Set.mem_univ _) hroot hrootAlt
  have atChoice := hchoiceOptimal (policy true) (Set.mem_univ _) hchoice hchoiceAlt
  rw [context_value_root assessment (policy false) hrootAlt,
    context_value_root assessment (assessment.strategy ()) hroot, shortWeight_short] at atRoot
  rw [context_value_choice assessment (policy true) hchoiceAlt,
    context_value_choice assessment (assessment.strategy ()) hchoice, shortWeight_long] at atChoice
  linarith

/-- Even finite, perfectly informed, perfect-recall EFGs with nonempty menus
need a sufficient-horizon hypothesis for sequential-equilibrium existence. -/
theorem no_sequential_equilibrium_with_insufficient_fuel :
    ¬ ∃ assessment : information.BehavioralAssessment,
      game.IsSequentialEquilibriumWithin antichain assessment payoff 2 := by
  rintro ⟨assessment, equilibrium⟩
  exact no_sequentially_rational_assessment assessment equilibrium.1

end GameTheory.Tests.SequentialExistenceBoundary
