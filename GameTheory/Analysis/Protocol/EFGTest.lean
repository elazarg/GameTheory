/-
# Hostile finite EFG assessment and equilibrium test

Nature privately selects a Boolean state, then the sole player acts without
observing it. The two decision histories are distinct but produce the same
information state. This tests the EFG specialization, finite history
enumeration, history-supported beliefs, and the analytic sequential-equilibrium
presentation together. A fully mixed Bayes assessment later proves that the
presentation carries an actual sequential-equilibrium witness.
-/

import GameTheory.Analysis.Protocol.EFG
import GameTheory.Math.Probability.Mixture
import GameTheory.Math.Probability.Product
import GameTheory.Math.Probability.Support
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.ExpectationMixture

noncomputable section

namespace GameTheory.Tests.EFG

open GameTheory GameTheory.Languages GameTheory.Protocol
open GameTheory.Math.Probability

set_option backward.isDefEq.respectTransparency false in
/-- One player is enough to make the hidden-information test discriminating. -/
inductive Player
  | player
  deriving DecidableEq, Fintype

/-- Nature's bit is retained through the terminal state, so the two decision
histories never merge as execution states. -/
inductive State
  | initial
  | decision (hidden : Bool) (arrival : Player → Option Bool)
  | terminal (hidden : Bool) (arrival action : Player → Option Bool)
  deriving DecidableEq, Fintype

/-- The nondegenerate chance law. -/
def fairCoin : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure true) (PMF.pure false)

theorem mem_support_fairCoin (side : Bool) :
    side ∈ fairCoin.support := by
  cases side with
  | true =>
      exact mem_support_mix_left (1 / 2) (by norm_num) (by norm_num)
        (by norm_num) (by simp)
  | false =>
      exact mem_support_mix_right (1 / 2) (by norm_num) (by norm_num)
        (by norm_num) (by simp)

/-- Chance, one hidden-information decision, then termination. -/
@[reducible]
def execution : ExecutionProtocol Player where
  State := State
  Action _ := Bool
  init := .initial
  active state _ :=
    match state with
    | .decision _ _ => True
    | _ => False
  available _ _ := Set.univ
  terminal state :=
    match state with
    | .terminal _ _ _ => True
    | _ => False
  step state joint :=
    match state with
    | .initial =>
        PMF.map (fun hidden => State.decision hidden joint.1) fairCoin
    | .decision hidden arrival =>
        PMF.pure (.terminal hidden arrival joint.1)
    | .terminal hidden arrival action =>
        PMF.pure (.terminal hidden arrival action)
  progress := by
    intro state hterm
    cases state with
    | initial =>
        exact ⟨fun _ => none, fun _ => by simp⟩
    | decision hidden arrival =>
        exact ⟨fun _ => some false, fun _ => ⟨trivial, Set.mem_univ _⟩⟩
    | terminal hidden arrival action =>
        exact False.elim (hterm trivial)

theorem initial_not_mem_step (source : State)
    (joint : Player → Option Bool) (hlegal : execution.Legal source joint) :
    State.initial ∉ (execution.step source ⟨joint, hlegal⟩).support := by
  cases source with
  | initial =>
      rw [PMF.support_map]
      rintro ⟨side, _hside, hstate⟩
      cases hstate
  | decision hidden arrival =>
      simp [execution]
  | terminal hidden arrival action =>
      exact False.elim (hlegal.1 trivial)

theorem step_predecessor_unique
    {target firstSource secondSource : State}
    {firstJoint secondJoint : Player → Option Bool}
    (firstLegal : execution.Legal firstSource firstJoint)
    (secondLegal : execution.Legal secondSource secondJoint)
    (firstRealized :
      target ∈ (execution.step firstSource ⟨firstJoint, firstLegal⟩).support)
    (secondRealized :
      target ∈ (execution.step secondSource ⟨secondJoint, secondLegal⟩).support) :
    firstSource = secondSource ∧ firstJoint = secondJoint := by
  cases firstSource with
  | initial =>
      rw [PMF.support_map] at firstRealized
      rcases firstRealized with ⟨firstSide, _hside, rfl⟩
      cases secondSource with
      | initial =>
          rw [PMF.support_map] at secondRealized
          rcases secondRealized with ⟨secondSide, _hsecond, hequal⟩
          injection hequal with _ hjoint
          have hjoint' : secondJoint = firstJoint := hjoint
          exact ⟨rfl, hjoint'.symm⟩
      | decision hidden arrival =>
          rw [PMF.mem_support_pure_iff] at secondRealized
          cases secondRealized
      | terminal hidden arrival action =>
          exact False.elim (secondLegal.1 trivial)
  | decision firstHidden firstArrival =>
      rw [PMF.mem_support_pure_iff] at firstRealized
      subst target
      cases secondSource with
      | initial =>
          rw [PMF.support_map] at secondRealized
          rcases secondRealized with ⟨secondSide, _hsecond, hequal⟩
          cases hequal
      | decision secondHidden secondArrival =>
          rw [PMF.mem_support_pure_iff] at secondRealized
          injection secondRealized with hhidden harrival hjoint
          have hjoint' : firstJoint = secondJoint := hjoint
          subst secondHidden
          subst secondArrival
          exact ⟨rfl, hjoint'⟩
      | terminal hidden arrival action =>
          exact False.elim (secondLegal.1 trivial)
  | terminal hidden arrival action =>
      exact False.elim (firstLegal.1 trivial)

theorem trace_unique :
    ∀ {state : State} (first second : execution.Trace state), first = second
  | _, .start, .start => rfl
  | _, .start, .extend prior joint isLegal realized =>
      False.elim (initial_not_mem_step _ joint isLegal realized)
  | _, .extend prior joint isLegal realized, .start =>
      False.elim (initial_not_mem_step _ joint isLegal realized)
  | _, .extend prior joint isLegal realized,
      .extend secondPrior secondJoint secondLegal secondRealized => by
      obtain ⟨rfl, hjoint⟩ :=
        step_predecessor_unique isLegal secondLegal realized secondRealized
      subst secondJoint
      have hprior := trace_unique prior secondPrior
      subst secondPrior
      rfl
termination_by _ first _ => first.length
decreasing_by simp [ExecutionProtocol.Trace.length]

theorem execution_treeShaped : execution.IsTreeShaped :=
  fun _ => ⟨trace_unique⟩

/-- Only one player can move because there is only one player. -/
theorem execution_singleMover (state : State) {first second : Player}
    (_hfirst : execution.active state first)
    (_hsecond : execution.active state second) :
    first = second := by
  cases first
  cases second
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- What the player observes. Both hidden decision states map to `acting`. -/
inductive View
  | waiting
  | acting
  | done
  deriving DecidableEq, Fintype

def viewOfState : State → View
  | .initial => .waiting
  | .decision _ _ => .acting
  | .terminal _ _ _ => .done

/-- The target state's view is emitted as the transition's private signal. -/
def privateView (event : execution.StepEvent) : View :=
  viewOfState event.target

/-- Signals deliberately forget nature's bit. -/
@[reducible]
def signals : InfoSignals execution where
  PublicSignal := Unit
  PrivateSignal := fun _ => View
  initialPublic := ()
  initialPrivate _ := .waiting
  publicSignal _ := ()
  privateSignal _ := privateView
  InfoState := fun _ => View
  initInfo := fun _ signal _ => signal
  pushInfo := fun _ _ _ signal _ => signal

theorem signals_infoOf (who : Player) :
  ∀ {state : State} (trace : execution.Trace state),
      signals.infoOf who trace = viewOfState state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

/-- The information model deliberately forgets nature's bit. -/
@[reducible]
def information : InformationModel execution where
  toInfoSignals := signals
  menu _ view :=
    match view with
    | .acting => Set.range some
    | _ => {none}
  menu_adequate := by
    intro who state trace choice
    rw [signals_infoOf]
    cases state <;> cases choice <;>
      simp [viewOfState, LegalOption]

/-- The stable EFG presentation adds laws, not another evaluator. -/
@[reducible]
def game : Languages.EFG.Game Player where
  execution := execution
  information := information
  treeShaped := execution_treeShaped
  singleMover := execution_singleMover

local instance finiteHistory : Fintype execution.History :=
  game.historyFintype

local instance finiteInformationHistory
    (who : Player) (site : information.InformationSite who) :
    Fintype (information.InformationHistory who site.1) := by
  classical
  infer_instance

/-- Finite test carriers give the actual law a canonical guarded expectation. -/
noncomputable def finiteExpect {α : Type*} [Fintype α]
    (law : PMF α) (payoff : α → ℝ) : ℝ :=
  expect law payoff (payoffIntegrable_of_finite law payoff)

private theorem finiteExpect_pure {α : Type*} [Fintype α]
    (a : α) (payoff : α → ℝ) :
    finiteExpect (PMF.pure a) payoff = payoff a := by
  unfold finiteExpect
  exact expect_pure a payoff _

private theorem finiteExpect_map {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (law : PMF α) (payoff : β → ℝ) :
    finiteExpect (PMF.map f law) payoff =
      finiteExpect law (payoff ∘ f) := by
  unfold finiteExpect
  exact expect_map f law payoff
    (payoffIntegrable_of_finite law (payoff ∘ f))
    (payoffIntegrable_of_finite (PMF.map f law) payoff)

private theorem finiteExpect_bind {α β : Type*} [Fintype α] [Fintype β]
    (law : PMF α) (kernel : α → PMF β) (payoff : β → ℝ) :
    finiteExpect (law.bind kernel) payoff =
      finiteExpect law (fun a => finiteExpect (kernel a) payoff) := by
  unfold finiteExpect
  let hbind := payoffIntegrable_of_finite (law.bind kernel) payoff
  let hcond := fun a => payoffIntegrable_of_finite (kernel a) payoff
  calc
    expect (law.bind kernel) payoff
        (payoffIntegrable_of_finite (law.bind kernel) payoff) =
      expect (law.bind kernel) payoff hbind := expect_proof_irrel ..
    _ = expect law (fun a => expect (kernel a) payoff (hcond a))
        (payoffIntegrable_bind_conditionalExpectation law kernel payoff hbind hcond) :=
      expect_bind_tower law kernel payoff hbind hcond
    _ = expect law (fun a => expect (kernel a) payoff
        (payoffIntegrable_of_finite (kernel a) payoff))
        (payoffIntegrable_of_finite law
          (fun a => expect (kernel a) payoff
            (payoffIntegrable_of_finite (kernel a) payoff))) := expect_proof_irrel ..

/-! ## Two histories, one decision information site -/

theorem initial_not_terminal : ¬ execution.terminal .initial := by
  simp

theorem initial_inactive (who : Player) :
    ¬ execution.active .initial who := by
  simp

theorem initialLegal : execution.Legal .initial execution.noop :=
  execution.noop_isLegal initial_not_terminal initial_inactive

theorem initial_legal_joint_eq_noop
    (joint : { joint : Player → Option Bool //
      execution.Legal .initial joint }) :
    joint.1 = execution.noop := by
  funext who
  cases who
  have hlegal := joint.2.2 .player
  cases hchoice : joint.1 .player with
  | none => rfl
  | some action =>
      rw [hchoice] at hlegal
      exact False.elim (initial_inactive .player hlegal.1)

theorem decision_mem_support (hidden : Bool) :
    State.decision hidden execution.noop ∈
      (execution.step .initial ⟨execution.noop, initialLegal⟩).support := by
  rw [PMF.support_map]
  exact ⟨hidden, mem_support_fairCoin hidden, rfl⟩

def decisionTrace (hidden : Bool) :
    execution.Trace (State.decision hidden execution.noop) :=
  .extend .start execution.noop initialLegal (decision_mem_support hidden)

@[reducible]
def decisionHistory (hidden : Bool) : execution.History :=
  ⟨.decision hidden execution.noop, decisionTrace hidden⟩

theorem infoOf_decisionHistory (hidden : Bool) :
    information.infoOf .player (decisionHistory hidden).trace = .acting :=
  signals_infoOf .player (decisionTrace hidden)

theorem acting_menu_contains_false :
    some false ∈ information.menu .player View.acting := by
  simp

theorem decision_not_terminal (hidden : Bool) :
    ¬ execution.terminal (decisionHistory hidden).state := by
  simp

@[reducible]
def actingSite : information.InformationSite .player :=
  information.informationSite .player (decisionHistory false) false (by
    exact decision_not_terminal false) (by
    rw [infoOf_decisionHistory]
    exact acting_menu_contains_false)

@[simp]
theorem actingSite_info : actingSite.1 = View.acting := by
  rfl

@[reducible]
def decisionInformationHistory (hidden : Bool) :
    information.InformationHistory .player actingSite.1 :=
  ⟨decisionHistory hidden, by
    simpa using infoOf_decisionHistory hidden⟩

/-- The belief carrier distinguishes nature's two histories even though the
player receives the same information state at both. -/
theorem decisionInformationHistory_ne :
    decisionInformationHistory false ≠ decisionInformationHistory true := by
  intro hequal
  have hstate :=
    congrArg
      (fun history : information.InformationHistory .player actingSite.1 =>
        history.1.state) hequal
  simp at hstate

/-- Every history at the acting information state is one of nature's two
decision histories. The proof uses reachability carried by the history rather
than enumerating proof terms in the history subtype. -/
theorem decision_trace_arrival_eq_noop
    : ∀ {state : State} (_trace : execution.Trace state)
        (hidden : Bool) (arrival : Player → Option Bool),
        state = .decision hidden arrival → arrival = execution.noop
  | _, .start, hidden, arrival, hstate => by cases hstate
  | _, .extend (source := source) prior joint isLegal realized,
      hidden, arrival, hstate => by
      cases hstate
      cases source with
      | initial =>
          rw [PMF.support_map] at realized
          rcases realized with ⟨side, _hside, hequal⟩
          injection hequal with _ hjoint
          exact hjoint.symm.trans
            (initial_legal_joint_eq_noop ⟨joint, isLegal⟩)
      | decision priorHidden priorArrival =>
          simp [execution] at realized
      | terminal priorHidden priorArrival priorAction =>
          exact False.elim (isLegal.1 trivial)

theorem history_eq_decisionHistory_of_info_acting
    (history : execution.History)
    (hinfo : information.infoOf .player history.trace = .acting) :
    ∃ hidden, history = decisionHistory hidden := by
  rcases history with ⟨state, trace⟩
  have hview : viewOfState state = .acting := by
    rw [← signals_infoOf .player trace]
    exact hinfo
  cases state with
  | initial => simp [viewOfState] at hview
  | terminal hidden arrival action => simp [viewOfState] at hview
  | decision hidden arrival =>
      have harrival :=
        decision_trace_arrival_eq_noop trace hidden arrival rfl
      subst arrival
      refine ⟨hidden, ?_⟩
      congr 1
      exact trace_unique trace (decisionTrace hidden)

/-- The acting information fiber is exactly the hidden Boolean chosen by
nature. -/
def actingHistoryEquivBool :
    information.InformationHistory .player actingSite.1 ≃ Bool where
  toFun history :=
    match history.1.state with
    | .decision hidden _ => hidden
    | _ => false
  invFun := decisionInformationHistory
  left_inv history := by
    rcases history with ⟨history, hinfo⟩
    obtain ⟨hidden, hhistory⟩ :=
      history_eq_decisionHistory_of_info_acting history hinfo
    subst history
    apply Subtype.ext
    rfl
  right_inv hidden := by
    simp

/-- The nondegenerate belief supported on the two hidden decision histories. -/
def decisionBelief :
    PMF (information.InformationHistory .player actingSite.1) :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure (decisionInformationHistory true))
    (PMF.pure (decisionInformationHistory false))

theorem decisionInformationHistory_mem_belief (hidden : Bool) :
    decisionInformationHistory hidden ∈ decisionBelief.support := by
  cases hidden
  · exact mem_support_mix_right (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by simp)
  · exact mem_support_mix_left (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by simp)

/-! ## The full analytic presentation typechecks on the hostile carrier -/

def behavioralPolicy : information.BehavioralPolicy .player
  | .waiting => PMF.pure ⟨none, by simp⟩
  | .acting => PMF.pure ⟨some false, by simp⟩
  | .done => PMF.pure ⟨none, by simp⟩

def behavioralProfile (who : Player) :
    information.BehavioralPolicy who := by
  cases who
  exact behavioralPolicy

/-- A genuinely mixed action law at the hidden decision information set. -/
def fullyMixedBehavioralPolicy : information.BehavioralPolicy .player
  | .waiting => PMF.pure ⟨none, by simp⟩
  | .acting =>
      PMF.map
        (fun action => ⟨some action, by simp⟩)
        fairCoin
  | .done => PMF.pure ⟨none, by simp⟩

theorem fullyMixedBehavioralPolicy_fullSupport (view : View) :
    ∀ choice, choice ∈ (fullyMixedBehavioralPolicy view).support := by
  intro choice
  cases view with
  | waiting =>
      rw [fullyMixedBehavioralPolicy, PMF.mem_support_pure_iff]
      rcases choice with ⟨choice, hchoice⟩
      cases choice with
      | none => rfl
      | some action => simp at hchoice
  | acting =>
      rw [fullyMixedBehavioralPolicy, PMF.support_map]
      rcases choice with ⟨choice, hchoice⟩
      cases choice with
      | none => simp at hchoice
      | some action =>
          exact ⟨action, mem_support_fairCoin action, rfl⟩
  | done =>
      rw [fullyMixedBehavioralPolicy, PMF.mem_support_pure_iff]
      rcases choice with ⟨choice, hchoice⟩
      cases choice with
      | none => rfl
      | some action => simp at hchoice

def fullyMixedBehavioralProfile (who : Player) :
    information.BehavioralPolicy who := by
  cases who
  exact fullyMixedBehavioralPolicy

private theorem initialLegal_at_initHistory :
    execution.Legal execution.initHistory.state execution.noop := by
  simpa [ExecutionProtocol.initHistory, execution] using initialLegal

/-- The unique legal initial draw in the hidden-information fixture. -/
def initialDraw :
    { joint : Player → Option Bool //
      execution.Legal execution.initHistory.state joint } :=
  ⟨execution.noop, initialLegal_at_initHistory⟩

theorem randomizedChooser_initial :
    information.randomizedChooser fullyMixedBehavioralProfile
      execution.initHistory initial_not_terminal =
        PMF.pure initialDraw := by
  let : Subsingleton
      { joint : Player → Option Bool //
        execution.Legal execution.initHistory.state joint } :=
    ⟨fun first second => Subtype.ext (by
      rw [initial_legal_joint_eq_noop first,
        initial_legal_joint_eq_noop second])⟩
  exact eq_pure_of_subsingleton _ _

def oneStepHistory : State → execution.History
  | .decision hidden _ => decisionHistory hidden
  | _ => decisionHistory false

theorem decisionHistory_injective : Function.Injective decisionHistory := by
  intro first second hequal
  have hstate := congrArg (fun history : execution.History => history.state) hequal
  simpa [decisionHistory] using hstate

theorem historyReachProbability_decision (hidden : Bool) :
    information.historyReachWeight fullyMixedBehavioralProfile
      (decisionInformationHistory hidden).1 =
        ENNReal.ofReal (1 / 2 : ℝ) := by
  classical
  unfold InformationModel.historyReachWeight
  rw [show (decisionInformationHistory hidden).1.trace.length = 1 by rfl,
    InformationModel.runBehavioral, InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 0 initial_not_terminal,
    randomizedChooser_initial, PMF.pure_bind]
  show (execution.step execution.initHistory.state initialDraw).bindOnSupport
      (fun state realized =>
        ExecutionProtocol.runRandomizedFor
          (information.randomizedChooser fullyMixedBehavioralProfile) 0
          (execution.initHistory.extend (joint := execution.noop)
            initialLegal_at_initHistory realized))
      (decisionHistory hidden) = ENNReal.ofReal (1 / 2 : ℝ)
  have hkernel : ∀ state
      (hstate : state ∈ (execution.step execution.initHistory.state
        initialDraw).support),
      ExecutionProtocol.runRandomizedFor
        (information.randomizedChooser fullyMixedBehavioralProfile) 0
        (execution.initHistory.extend (joint := execution.noop)
          initialLegal_at_initHistory (target := state) hstate) =
        PMF.pure (oneStepHistory state) := by
    intro state hstate
    rw [show execution.step execution.initHistory.state initialDraw =
      PMF.map (fun side => State.decision side execution.noop) fairCoin by rfl,
      PMF.support_map] at hstate
    rcases hstate with ⟨side, _hside, rfl⟩
    have htrace :
        (execution.initHistory.extend (joint := execution.noop)
          initialLegal_at_initHistory (target := State.decision side execution.noop)
          hstate).trace = decisionTrace side := by
      have hstate' :
          (execution.initHistory.extend (joint := execution.noop)
            initialLegal_at_initHistory
            (target := State.decision side execution.noop) hstate).state =
            State.decision side execution.noop := rfl
      cases hstate'
      exact @Subsingleton.elim _
        (execution_treeShaped (State.decision side execution.noop)) _ _
    apply congrArg PMF.pure
    exact congrArg
      (fun trace : execution.Trace (State.decision side execution.noop) =>
        (⟨State.decision side execution.noop, trace⟩ : execution.History)) htrace
  rw [bindOnSupport_eq_bind_of_eq_on_support
      (execution.step execution.initHistory.state initialDraw)
    (g := fun state => PMF.pure (oneStepHistory state)) hkernel]
  rw [show (execution.step execution.initHistory.state initialDraw).bind
      (fun state => PMF.pure (oneStepHistory state)) =
        PMF.map oneStepHistory
          (execution.step execution.initHistory.state initialDraw) by
            simpa only [Function.comp_def] using
              PMF.bind_pure_comp oneStepHistory
                (execution.step execution.initHistory.state initialDraw),
    show execution.step execution.initHistory.state initialDraw =
        PMF.map (fun side => State.decision side execution.noop) fairCoin by
          rfl,
    PMF.map_comp]
  rw [PMF.map_apply, tsum_eq_single hidden]
  · cases hidden <;>
      norm_num [fairCoin, mix_apply, PMF.pure_apply, oneStepHistory]
  · intro side hside
    by_cases hequal :
        decisionHistory hidden =
          oneStepHistory (State.decision side execution.noop)
    · have hhidden : hidden = side :=
        decisionHistory_injective (by simpa [oneStepHistory] using hequal)
      exact False.elim (hside hhidden.symm)
    · simp [hequal]

/-- The two equiprobable histories exhaust the acting information fiber. -/
theorem informationMass_fullyMixed_acting :
    information.informationMass fullyMixedBehavioralProfile
      .player actingSite = 1 := by
  rw [InformationModel.informationMass, tsum_fintype]
  calc
    (∑ history :
        information.InformationHistory .player actingSite.1,
        information.historyReachWeight
          fullyMixedBehavioralProfile history.1) =
      ∑ hidden : Bool,
        information.historyReachWeight fullyMixedBehavioralProfile
          (decisionInformationHistory hidden).1 := by
            exact Fintype.sum_equiv actingHistoryEquivBool
              (fun history =>
                information.historyReachWeight
                  fullyMixedBehavioralProfile history.1)
              (fun hidden =>
                information.historyReachWeight
                  fullyMixedBehavioralProfile
                    (decisionInformationHistory hidden).1)
              (fun history => by
                have hinverse :=
                  actingHistoryEquivBool.symm_apply_apply history
                exact congrArg
                  (fun current :
                      information.InformationHistory
                        .player actingSite.1 =>
                      information.historyReachWeight
                      fullyMixedBehavioralProfile current.1)
                  hinverse.symm)
    _ = ∑ _hidden : Bool, ENNReal.ofReal (1 / 2 : ℝ) := by
          apply Finset.sum_congr rfl
          intro hidden _hhidden
          exact historyReachProbability_decision hidden
    _ = 1 := by
          have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 : ENNReal) / 2 := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num)]
            norm_num
          have hsum :
              (∑ _hidden : Bool, ENNReal.ofReal (1 / 2 : ℝ)) =
                ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) := by
            rw [Fintype.sum_bool]
          calc
            _ = ENNReal.ofReal (1 / 2 : ℝ) +
                ENNReal.ofReal (1 / 2 : ℝ) := hsum
            _ = 1 := by
              rw [hhalf]
              exact ENNReal.add_halves 1

theorem informationSite_info_eq_acting
    (site : information.InformationSite .player) :
    site.1 = View.acting := by
  rcases site.2 with ⟨_history, _hnonterminal, action, haction⟩
  cases hinfo : site.1 <;> simp [information, hinfo] at haction ⊢

/-- There is exactly one decision information site in the hostile game. -/
theorem informationSite_eq_actingSite
    (site : information.InformationSite .player) :
    site = actingSite :=
  Subtype.ext (informationSite_info_eq_acting site)

/-- The two hidden decision histories are simultaneous alternatives, never a
history and its own continuation.  Hence normalized reach mass at the unique
decision site is genuine Bayes conditioning even though the terminal view does
not retain the player's action and the whole model need not satisfy perfect
recall. -/
theorem information_decisionInformationAntichain :
    information.DecisionInformationAntichain := by
  intro who site
  cases who
  intro first second joint isLegal reached realized fuel hreach
  have hfirstInfo :
      information.infoOf .player first.1.trace = View.acting := by
    simpa [informationSite_info_eq_acting site] using first.2
  have hsecondInfo :
      information.infoOf .player second.1.trace = View.acting := by
    simpa [informationSite_info_eq_acting site] using second.2
  obtain ⟨firstHidden, hfirst⟩ :=
    history_eq_decisionHistory_of_info_acting first.1 hfirstInfo
  obtain ⟨secondHidden, hsecond⟩ :=
    history_eq_decisionHistory_of_info_acting second.1 hsecondInfo
  have hfirstLength : first.1.trace.length = 1 := by
    rw [hfirst]
    rfl
  have hsecondLength : second.1.trace.length = 1 := by
    rw [hsecond]
    rfl
  have hlength := hreach.trace_length_le
  have hlength' : first.1.trace.length + 1 ≤ second.1.trace.length := hlength
  omega

theorem informationMass_fullyMixed_pos
    (site : information.InformationSite .player) :
    0 < information.informationMass
      fullyMixedBehavioralProfile .player site := by
  let witness : information.InformationHistory .player site.1 :=
    ⟨decisionHistory false,
      (infoOf_decisionHistory false).trans
        (informationSite_info_eq_acting site).symm⟩
  have hwitness :
      information.historyReachWeight fullyMixedBehavioralProfile witness.1 =
        ENNReal.ofReal (1 / 2 : ℝ) := by
    simpa [witness] using historyReachProbability_decision false
  have hnonneg :
      ∀ history : information.InformationHistory .player site.1,
        0 ≤ information.historyReachWeight
          fullyMixedBehavioralProfile history.1 := by
    intro history
    exact bot_le
  rw [InformationModel.informationMass, tsum_fintype]
  exact lt_of_lt_of_le (by rw [hwitness]; norm_num)
    (Finset.single_le_sum (fun history _ => hnonneg history)
      (Finset.mem_univ witness))

def assessmentBelief
    (who : Player) (site : information.InformationSite who) :
    PMF (information.InformationHistory who site.1) := by
  cases who
  rw [informationSite_info_eq_acting site]
  exact decisionBelief

def assessment : information.BehavioralAssessment where
  strategy := behavioralProfile
  belief := assessmentBelief

theorem assessment_belief_acting :
    assessment.belief .player actingSite = decisionBelief := by
  rfl

def payoff (_ : Player) (_ : execution.History) : ℝ := 0

/-- The player earns one exactly when its terminal action matches nature's
hidden bit. This payoff is nonconstant, but the fair hidden bit and the single
information set make both actions worth `1 / 2`. -/
def matchingPayoff (_ : Player) (history : execution.History) : ℝ :=
  match history.state with
  | .terminal hidden _ action =>
      if action .player = some hidden then 1 else 0
  | _ => 0

set_option backward.isDefEq.respectTransparency false in
theorem runBehavioralFrom_decision_matchingPayoff
    (hidden : Bool)
    (alternative : information.BehavioralPolicy Player.player) :
    finiteExpect (information.runBehavioralFrom
      (Profile.update (sig := information.behavioralSignature)
        fullyMixedBehavioralProfile Player.player alternative) 2
      (decisionHistory hidden)) (matchingPayoff .player) =
        finiteExpect (alternative .acting) fun choice =>
          if choice.1 = some hidden then 1 else 0 := by
  classical
  let drawLaw :
      PMF ((i : Player) →
        information.Choice i
          (information.infoOf i (decisionHistory hidden).trace)) :=
      independentProduct fun i =>
      Profile.update (sig := information.behavioralSignature)
        fullyMixedBehavioralProfile Player.player alternative i
        (information.infoOf i (decisionHistory hidden).trace)
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ 1
      (decision_not_terminal hidden),
    finiteExpect_bind, InformationModel.randomizedChooser,
    InformationModel.behavioralJoint, finiteExpect_map]
  have hmarginal :
      PMF.map (fun draws => (draws Player.player).1) drawLaw =
        PMF.map (fun choice => choice.1) (alternative .acting) := by
    have hchoice :
        PMF.map (fun draws => draws Player.player) drawLaw =
          alternative
            (information.infoOf Player.player
              (decisionHistory hidden).trace) := by
      unfold drawLaw
      rw [independentProduct_map_eval, Profile.update_same]
    have hprojected :
        PMF.map (fun draws => (draws Player.player).1) drawLaw =
          PMF.map (fun choice => choice.1)
            (alternative
              (information.infoOf Player.player
                (decisionHistory hidden).trace)) := by
      have hcongr := congrArg
        (fun law : PMF
            (information.Choice Player.player
              (information.infoOf Player.player
                (decisionHistory hidden).trace)) =>
          PMF.map (fun choice => choice.1) law)
        hchoice
      simpa only [PMF.map_comp, Function.comp_def] using hcongr
    exact hprojected.trans (by
      rw [infoOf_decisionHistory])
  calc
    _ =
      finiteExpect drawLaw (fun draws =>
        if (draws Player.player).1 = some hidden then 1 else 0) := by
          unfold finiteExpect
          apply expect_congr_on_support
          · intro draws _hdraws
            have hlegal := (draws Player.player).2
            cases hdraw : (draws Player.player).1 with
            | none =>
                simp [information, signals_infoOf, viewOfState, hdraw] at hlegal
            | some action =>
                cases action <;> cases hidden <;>
                  simp [hdraw, expect_pure, execution, decisionHistory, matchingPayoff,
                    PMF.pure_bindOnSupport,
                    ExecutionProtocol.History.extend_state,
                    ExecutionProtocol.runRandomizedFor_of_terminal]
    _ = finiteExpect
          (PMF.map (fun draws => (draws Player.player).1) drawLaw)
          (fun choice : Option Bool =>
            if choice = some hidden then 1 else 0) := by
          simpa only [Function.comp_def] using
            (finiteExpect_map (fun draws => (draws Player.player).1)
              drawLaw (fun choice : Option Bool =>
                if choice = some hidden then 1 else 0)).symm
    _ = finiteExpect
          (PMF.map (fun choice => choice.1) (alternative .acting))
          (fun choice : Option Bool =>
            if choice = some hidden then 1 else 0) := by
          rw [hmarginal]
    _ = finiteExpect (alternative .acting) fun choice =>
          if choice.1 = some hidden then 1 else 0 := by
          simpa only [Function.comp_def] using
            finiteExpect_map (fun choice => choice.1) (alternative .acting)
              (fun action : Option Bool =>
                if action = some hidden then 1 else 0)

/-- The Bayes assessment used by the concrete equilibrium theorem. Unlike the
presentation-only assessment above, its decision law has full support and its
belief is constructed by normalizing the existing history reach masses. -/
def fullyMixedAssessment : information.BehavioralAssessment where
  strategy := fullyMixedBehavioralProfile
  belief := fun who site => by
    cases who
    exact information.bayesBelief fullyMixedBehavioralProfile .player site
      (information_decisionInformationAntichain .player site)
      (informationMass_fullyMixed_pos site)

theorem fullyMixedAssessment_isFullyMixed :
    fullyMixedAssessment.IsFullyMixed := by
  intro who site
  cases who
  rw [informationSite_info_eq_acting site]
  exact fullyMixedBehavioralPolicy_fullSupport .acting

theorem fullyMixedAssessment_isBayesConsistent :
    InformationModel.BehavioralAssessment.IsBayesConsistent information
      fullyMixedAssessment
      information_decisionInformationAntichain := by
  intro who site _hmass history
  cases who
  exact information.bayesBelief_apply fullyMixedBehavioralProfile .player site
    (information_decisionInformationAntichain .player site)
    (informationMass_fullyMixed_pos site) history

set_option backward.isDefEq.respectTransparency false in
/-- At the unique acting site, the canonical normalized Bayes belief is the
explicit fair mixture over nature's two hidden histories. -/
theorem fullyMixedAssessment_belief_acting :
    fullyMixedAssessment.belief .player actingSite = decisionBelief := by
  classical
  apply PMF.ext
  intro history
  obtain ⟨hidden, hcarrier⟩ :=
    history_eq_decisionHistory_of_info_acting history.1 history.2
  have hhistory : history = decisionInformationHistory hidden :=
    Subtype.ext hcarrier
  subst history
  rw [fullyMixedAssessment, InformationModel.bayesBelief_apply,
    informationMass_fullyMixed_acting,
    historyReachProbability_decision]
  have hstate :
      State.decision false execution.noop ≠
        State.decision true execution.noop := by simp
  cases hidden <;>
    norm_num [decisionBelief, decisionInformationHistory_ne,
      PMF.pure_apply, ENNReal.ofReal, hstate, hstate.symm]

/-- Every whole continuation policy has value `1 / 2`: after projecting legal
choices to their Boolean action, the two hidden states contribute
complementary indicators. -/
theorem continuationContext_matchingPayoff_value
    (alternative : information.BehavioralPolicy .player)
    (hvalue : (fullyMixedAssessment.continuationContext actingSite
      (matchingPayoff .player) 2).IntegrableAt alternative) :
    (fullyMixedAssessment.continuationContext actingSite
      (matchingPayoff .player) 2).value alternative hvalue = 1 / 2 := by
  let kernel : information.InformationHistory .player actingSite.1 →
      PMF execution.History := fun history =>
    information.runBehavioralFrom
      (Profile.update (sig := information.behavioralSignature)
        fullyMixedAssessment.strategy .player alternative) 2 history.1
  let belief : PMF (information.InformationHistory .player actingSite.1) :=
    fullyMixedAssessment.belief .player actingSite
  have hbelief : belief = decisionBelief := by
    dsimp [belief]
    exact fullyMixedAssessment_belief_acting
  have hbind : PayoffIntegrable (belief.bind kernel) (matchingPayoff .player) := by
    show (fullyMixedAssessment.continuationContext actingSite
      (matchingPayoff .player) 2).IntegrableAt alternative
    exact hvalue
  have hcond (history : information.InformationHistory .player actingSite.1) :
      PayoffIntegrable (kernel history) (matchingPayoff .player) :=
    payoffIntegrable_of_finite (kernel history) (matchingPayoff .player)
  let branchValue := fun history =>
    expect (kernel history) (matchingPayoff .player) (hcond history)
  have houter := payoffIntegrable_bind_conditionalExpectation
    belief kernel (matchingPayoff .player) hbind hcond
  have hbranch (hidden : Bool) :
      branchValue (decisionInformationHistory hidden) =
        finiteExpect (alternative .acting) (fun choice =>
          if choice.1 = some hidden then 1 else 0) := by
    unfold branchValue kernel
    have hlaw :
        information.runBehavioralFrom
            (Profile.update (sig := information.behavioralSignature)
              fullyMixedAssessment.strategy Player.player alternative)
            2 (decisionHistory hidden) =
          information.runBehavioralFrom
            (Profile.update (sig := information.behavioralSignature)
              fullyMixedBehavioralProfile Player.player alternative)
            2 (decisionHistory hidden) := by
      simp only [fullyMixedAssessment]
    have hsame := expect_proof_irrel _ _
      (hcond (decisionInformationHistory hidden))
      (payoffIntegrable_of_finite _ _)
    have hvalue' := runBehavioralFrom_decision_matchingPayoff hidden alternative
    calc
      expect
          (information.runBehavioralFrom
            (Profile.update (sig := information.behavioralSignature)
              fullyMixedAssessment.strategy Player.player alternative)
            2 (decisionHistory hidden))
          (matchingPayoff .player) (hcond (decisionInformationHistory hidden)) =
        expect
          (information.runBehavioralFrom
            (Profile.update (sig := information.behavioralSignature)
              fullyMixedBehavioralProfile Player.player alternative)
            2 (decisionHistory hidden))
          (matchingPayoff .player) _ :=
            expect_congr_law hlaw _ _ _
      _ = finiteExpect (alternative .acting) (fun choice =>
          if choice.1 = some hidden then 1 else 0) := hsame.trans hvalue'
  have htrue : PayoffIntegrable
      (PMF.pure (decisionInformationHistory true)) branchValue :=
    payoffIntegrable_of_finite _ _
  have hfalse : PayoffIntegrable
      (PMF.pure (decisionInformationHistory false)) branchValue :=
    payoffIntegrable_of_finite _ _
  have hmix := expect_mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure (decisionInformationHistory true))
    (PMF.pure (decisionInformationHistory false)) branchValue htrue hfalse
  have hcomplement :
      finiteExpect (alternative .acting) (fun choice =>
        if choice.1 = some true then 1 else 0) +
      finiteExpect (alternative .acting) (fun choice =>
        if choice.1 = some false then 1 else 0) = 1 := by
    let ftrue := fun choice : information.Choice .player View.acting =>
      if choice.1 = some true then (1 : ℝ) else 0
    let ffalse := fun choice : information.Choice .player View.acting =>
      if choice.1 = some false then (1 : ℝ) else 0
    have hf : PayoffIntegrable (alternative .acting) ftrue :=
      payoffIntegrable_of_finite _ _
    have hg : PayoffIntegrable (alternative .acting) ffalse :=
      payoffIntegrable_of_finite _ _
    have hconst : PayoffIntegrable (alternative .acting) (fun _ => (1 : ℝ)) :=
      payoffIntegrable_of_finite _ _
    have hpoint (choice : information.Choice .player View.acting)
        (_hchoice : choice ∈ (alternative .acting).support) :
        ftrue choice + ffalse choice = 1 := by
      rcases choice with ⟨choice, hchoice⟩
      rcases hchoice with ⟨action, rfl⟩
      cases action <;> simp [ftrue, ffalse]
    have hcongr := expect_congr_on_support hpoint
      (payoffIntegrable_add hf hg) hconst
    have hadd := expect_add hf hg
    unfold finiteExpect
    calc
      _ = expect (alternative .acting) (fun choice =>
            ftrue choice + ffalse choice) (payoffIntegrable_add hf hg) := hadd.symm
      _ = expect (alternative .acting) (fun _ => (1 : ℝ)) hconst := hcongr
      _ = 1 := expect_constant (alternative .acting) 1 hconst
  calc
    expect (belief.bind kernel) (matchingPayoff .player) hbind =
      expect belief branchValue houter :=
        expect_bind_tower belief kernel (matchingPayoff .player) hbind hcond
    _ = expect decisionBelief branchValue
          (payoffIntegrable_congr_law hbelief houter) :=
      expect_congr_law hbelief branchValue houter
        (payoffIntegrable_congr_law hbelief houter)
    _ = (1 / 2) * branchValue (decisionInformationHistory true) +
          (1 - 1 / 2) * branchValue (decisionInformationHistory false) := by
      rw [expect_pure, expect_pure] at hmix
      exact hmix
    _ = 1 / 2 := by
      rw [hbranch true, hbranch false]
      rw [show 1 - 1 / 2 = (1 / 2 : ℝ) by norm_num]
      nlinarith [hcomplement]

/-- The fair hidden state makes every whole continuation policy optimal, even
though the terminal payoff itself is nonconstant. -/
theorem fullyMixedAssessment_isSequentiallyRationalWithin_matchingPayoff :
    fullyMixedAssessment.IsSequentiallyRationalWithin matchingPayoff 2 := by
  intro who site
  cases who
  have hsite := informationSite_eq_actingSite site
  subst site
  let context := fullyMixedAssessment.continuationContext actingSite
    (matchingPayoff .player) 2
  have hfinite (alternative : information.BehavioralPolicy .player) :
      context.IntegrableAt alternative :=
    payoffIntegrable_of_finite (context.outcome alternative)
      context.continuation
  show context.IsLocallyOptimal Set.univ
    (fullyMixedAssessment.strategy .player)
  refine ⟨hfinite _, fun alternative _ => hfinite alternative, ?_⟩
  intro alternative _ hincumbent halternative
  rw [continuationContext_matchingPayoff_value alternative halternative,
    continuationContext_matchingPayoff_value
      (fullyMixedAssessment.strategy .player) hincumbent]

theorem fullyMixedAssessment_isSequentiallyConsistent :
    game.IsSequentiallyConsistent information_decisionInformationAntichain
      fullyMixedAssessment := by
  simpa only [GameTheory.Languages.EFG.Game.IsSequentiallyConsistent] using
    InformationModel.BehavioralAssessment.IsSequentiallyConsistent.of_fullyMixed_bayes
      information_decisionInformationAntichain
      fullyMixedAssessment_isFullyMixed
      fullyMixedAssessment_isBayesConsistent

/-- The hostile hidden-information EFG has an actual sequential equilibrium.
Zero continuation payoff makes every whole continuation policy optimal; full
mixing and finite Bayes consistency make the assessment its own valid
approximating sequence. -/
theorem fullyMixedAssessment_isSequentialEquilibrium :
    game.IsSequentialEquilibriumWithin information_decisionInformationAntichain
      fullyMixedAssessment payoff 2 := by
  rw [game.isSequentialEquilibriumWithin_iff
    information_decisionInformationAntichain]
  exact
    ⟨fullyMixedAssessment.isSequentiallyRationalWithin_zero 2,
      fullyMixedAssessment_isSequentiallyConsistent⟩

/-- The same fully mixed Bayes assessment is a sequential equilibrium for the
nonconstant matching payoff. Rationality quantifies over arbitrary replacement
policies, so this is not a fixed-strategy payoff calculation. -/
theorem fullyMixedAssessment_isSequentialEquilibrium_matchingPayoff :
    game.IsSequentialEquilibriumWithin
      information_decisionInformationAntichain fullyMixedAssessment
        matchingPayoff 2 := by
  rw [game.isSequentialEquilibriumWithin_iff
    information_decisionInformationAntichain]
  exact
    ⟨fullyMixedAssessment_isSequentiallyRationalWithin_matchingPayoff,
      fullyMixedAssessment_isSequentiallyConsistent⟩

/-! A falsifying assessment reuses the same continuation runner. Its belief
puts all mass on hidden `true`, while its strategy chooses `false`. -/

def trueBelief
    (who : Player) (site : information.InformationSite who) :
    PMF (information.InformationHistory who site.1) := by
  cases who
  rw [informationSite_info_eq_acting site]
  exact PMF.pure (decisionInformationHistory true)

def wrongAssessment : information.BehavioralAssessment where
  strategy := behavioralProfile
  belief := trueBelief

@[simp]
theorem wrongAssessment_belief_acting :
    wrongAssessment.belief .player actingSite =
      PMF.pure (decisionInformationHistory true) := by
  rfl

def alwaysTruePolicy : information.BehavioralPolicy .player
  | .waiting => PMF.pure ⟨none, by simp⟩
  | .acting => PMF.pure ⟨some true, by simp⟩
  | .done => PMF.pure ⟨none, by simp⟩

/-- Under the dogmatic belief, continuation value is exactly the probability
of choosing `true` at the acting information state. -/
theorem wrongAssessment_continuationContext_value
    (alternative : information.BehavioralPolicy .player)
    (hvalue : (wrongAssessment.continuationContext actingSite
      (matchingPayoff .player) 2).IntegrableAt alternative) :
    (wrongAssessment.continuationContext actingSite
      (matchingPayoff .player) 2).value alternative hvalue =
      finiteExpect (alternative .acting) fun choice =>
          if choice.1 = some true then 1 else 0 := by
  let kernel : information.InformationHistory .player actingSite.1 →
      PMF execution.History := fun history =>
    information.runBehavioralFrom
      (Profile.update (sig := information.behavioralSignature)
        wrongAssessment.strategy .player alternative) 2 history.1
  let belief : PMF (information.InformationHistory .player actingSite.1) :=
    wrongAssessment.belief .player actingSite
  have hbind : PayoffIntegrable (belief.bind kernel) (matchingPayoff .player) := by
    show (wrongAssessment.continuationContext actingSite
      (matchingPayoff .player) 2).IntegrableAt alternative
    exact hvalue
  have hcond (history : information.InformationHistory .player actingSite.1) :
      PayoffIntegrable (kernel history) (matchingPayoff .player) :=
    payoffIntegrable_of_finite (kernel history) (matchingPayoff .player)
  let branchValue := fun history =>
    expect (kernel history) (matchingPayoff .player) (hcond history)
  have houter := payoffIntegrable_bind_conditionalExpectation
    belief kernel (matchingPayoff .player) hbind hcond
  have hupdated :
      Profile.update (sig := information.behavioralSignature)
          wrongAssessment.strategy .player alternative =
        Profile.update (sig := information.behavioralSignature)
          fullyMixedBehavioralProfile .player alternative := by
    funext who
    cases who
    exact Profile.update_same _ _ _
  have hbelief : belief = PMF.pure (decisionInformationHistory true) := by
    dsimp [belief]
    exact wrongAssessment_belief_acting
  have hpure : PayoffIntegrable
      (PMF.pure (decisionInformationHistory true)) branchValue :=
    payoffIntegrable_of_finite _ _
  calc
    expect (belief.bind kernel) (matchingPayoff .player) hbind =
        expect belief branchValue houter :=
      expect_bind_tower belief kernel (matchingPayoff .player) hbind hcond
    _ = expect (PMF.pure (decisionInformationHistory true)) branchValue hpure :=
      expect_congr_law hbelief branchValue houter hpure
    _ = finiteExpect (alternative .acting) fun choice =>
          if choice.1 = some true then 1 else 0 := by
      rw [expect_pure]
      unfold branchValue kernel
      have hrun :
          information.runBehavioralFrom
              (Profile.update (sig := information.behavioralSignature)
                wrongAssessment.strategy .player alternative)
              2 (decisionHistory true) =
            information.runBehavioralFrom
              (Profile.update (sig := information.behavioralSignature)
                fullyMixedBehavioralProfile .player alternative)
              2 (decisionHistory true) :=
        congrArg (fun profile =>
          information.runBehavioralFrom profile 2 (decisionHistory true)) hupdated
      have hfull : PayoffIntegrable
          (information.runBehavioralFrom
            (Profile.update (sig := information.behavioralSignature)
              fullyMixedBehavioralProfile .player alternative)
            2 (decisionHistory true)) (matchingPayoff .player) :=
        payoffIntegrable_congr_law hrun.symm
          (hcond (decisionInformationHistory true))
      calc
        expect (information.runBehavioralFrom
            (Profile.update (sig := information.behavioralSignature)
              wrongAssessment.strategy .player alternative)
            2 (decisionHistory true))
            (matchingPayoff .player) (hcond (decisionInformationHistory true)) =
          expect (information.runBehavioralFrom
            (Profile.update (sig := information.behavioralSignature)
              fullyMixedBehavioralProfile .player alternative)
            2 (decisionHistory true))
            (matchingPayoff .player) hfull :=
              expect_congr_law hrun _ _ _
        _ = finiteExpect (alternative .acting) (fun choice =>
            if choice.1 = some true then 1 else 0) := by
          have hsame := expect_proof_irrel _ _
            hfull (payoffIntegrable_of_finite _ _)
          have hvalue' := runBehavioralFrom_decision_matchingPayoff true alternative
          exact hsame.trans hvalue'

/-- The prescribed `false` policy has value zero, while the whole-policy
alternative choosing `true` has value one. -/
theorem wrongAssessment_not_isSequentiallyRationalWithin_matchingPayoff :
    ¬ wrongAssessment.IsSequentiallyRationalWithin matchingPayoff 2 := by
  intro hrational
  let context := wrongAssessment.continuationContext actingSite
    (matchingPayoff .player) 2
  have hlocal : context.IsLocallyOptimal Set.univ
      (wrongAssessment.strategy .player) := hrational .player actingSite
  rcases hlocal with ⟨hincumbent, hall, hoptimal⟩
  have hdeviation := hoptimal alwaysTruePolicy (Set.mem_univ _)
    hincumbent (hall alwaysTruePolicy (Set.mem_univ _))
  have hdeviation' :
      context.value alwaysTruePolicy (hall alwaysTruePolicy (Set.mem_univ _)) ≤
        context.value (wrongAssessment.strategy .player) hincumbent := by
    simpa only [context] using hdeviation
  have htrue := wrongAssessment_continuationContext_value alwaysTruePolicy
    (hall alwaysTruePolicy (Set.mem_univ _))
  have hincumbent' := wrongAssessment_continuationContext_value
    (wrongAssessment.strategy .player) hincumbent
  have hvalues :
      finiteExpect (alwaysTruePolicy .acting) (fun choice =>
        if choice.1 = some true then 1 else 0) ≤
      finiteExpect (wrongAssessment.strategy .player .acting) (fun choice =>
        if choice.1 = some true then 1 else 0) := by
    calc
      _ = context.value alwaysTruePolicy (hall alwaysTruePolicy (Set.mem_univ _)) :=
        htrue.symm
      _ ≤ context.value (wrongAssessment.strategy .player) hincumbent := hdeviation'
      _ = _ := hincumbent'
  have hincumbentValue :
      finiteExpect (wrongAssessment.strategy Player.player .acting) (fun choice =>
        if choice.1 = some true then 1 else 0) = 0 := by
    simp [wrongAssessment, behavioralProfile, behavioralPolicy,
      finiteExpect_pure]
  have halwaysValue :
      finiteExpect (alwaysTruePolicy .acting) (fun choice =>
        if choice.1 = some true then 1 else 0) = 1 := by
    simp [alwaysTruePolicy, finiteExpect_pure]
  rw [halwaysValue, hincumbentValue] at hvalues
  norm_num at hvalues

/-- Failed sequential rationality is already enough to refute sequential
equilibrium, independently of the assessment's consistency status. -/
theorem wrongAssessment_not_isSequentialEquilibrium_matchingPayoff :
    ¬ game.IsSequentialEquilibriumWithin information_decisionInformationAntichain
      wrongAssessment matchingPayoff 2 := by
  intro hequilibrium
  apply wrongAssessment_not_isSequentiallyRationalWithin_matchingPayoff
  exact (game.isSequentialEquilibriumWithin_iff
    information_decisionInformationAntichain wrongAssessment matchingPayoff 2).mp
      hequilibrium |>.1

/-- The fixture supplies finite history fibers; the language adapter
specializes canonical full-policy contexts and consistency predicates. -/
def sequentialEquilibriumTarget : Prop :=
  game.IsSequentialEquilibriumWithin information_decisionInformationAntichain
    assessment payoff 2

theorem sequentialEquilibriumTarget_iff :
    sequentialEquilibriumTarget ↔
      assessment.IsSequentiallyRationalWithin payoff 2 ∧
        game.IsSequentiallyConsistent information_decisionInformationAntichain
          assessment := by
  exact game.isSequentialEquilibriumWithin_iff
    information_decisionInformationAntichain assessment payoff 2

end GameTheory.Tests.EFG
