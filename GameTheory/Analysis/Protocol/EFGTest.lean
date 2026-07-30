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

noncomputable section

namespace GameTheory.Tests.EFG

open GameTheory GameTheory.Languages GameTheory.Protocol
open GameTheory.Probability

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
def fairCoin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure true) (FinDist.pure false)

theorem mem_support_fairCoin (side : Bool) :
    side ∈ fairCoin.support := by
  rw [← FinDist.prob_pos_iff]
  cases side <;> norm_num [fairCoin, FinDist.prob_pure_eq_ite]

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
        FinDist.map (fun hidden => State.decision hidden joint.1) fairCoin
    | .decision hidden arrival =>
        FinDist.pure (.terminal hidden arrival joint.1)
    | .terminal hidden arrival action =>
        FinDist.pure (.terminal hidden arrival action)
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
      rw [FinDist.support_map]
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
      rw [FinDist.support_map] at firstRealized
      rcases firstRealized with ⟨firstSide, _hside, rfl⟩
      cases secondSource with
      | initial =>
          rw [FinDist.support_map] at secondRealized
          rcases secondRealized with ⟨secondSide, _hsecond, hequal⟩
          injection hequal with _ hjoint
          have hjoint' : secondJoint = firstJoint := hjoint
          exact ⟨rfl, hjoint'.symm⟩
      | decision hidden arrival =>
          rw [FinDist.mem_support_pure] at secondRealized
          cases secondRealized
      | terminal hidden arrival action =>
          exact False.elim (secondLegal.1 trivial)
  | decision firstHidden firstArrival =>
      rw [FinDist.mem_support_pure] at firstRealized
      subst target
      cases secondSource with
      | initial =>
          rw [FinDist.support_map] at secondRealized
          rcases secondRealized with ⟨secondSide, _hsecond, hequal⟩
          cases hequal
      | decision secondHidden secondArrival =>
          rw [FinDist.mem_support_pure] at secondRealized
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
  rw [FinDist.support_map]
  exact ⟨hidden, mem_support_fairCoin hidden, rfl⟩

def decisionTrace (hidden : Bool) :
    execution.Trace (State.decision hidden execution.noop) :=
  .extend .start execution.noop initialLegal (decision_mem_support hidden)

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
  simp [decisionHistory]

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
  simp [decisionHistory] at hstate

/-- The nondegenerate belief supported on the two hidden decision histories. -/
def decisionBelief :
    FinDist (information.InformationHistory .player actingSite.1) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (decisionInformationHistory true))
    (FinDist.pure (decisionInformationHistory false))

theorem decisionInformationHistory_mem_belief (hidden : Bool) :
    decisionInformationHistory hidden ∈ decisionBelief.support := by
  cases hidden
  · exact FinDist.mem_support_mix_right (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (FinDist.mem_support_pure.mpr rfl)
  · exact FinDist.mem_support_mix_left (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (FinDist.mem_support_pure.mpr rfl)

/-! ## The full analytic presentation typechecks on the hostile carrier -/

def behavioralPolicy : information.BehavioralPolicy .player
  | .waiting => FinDist.pure ⟨none, by simp⟩
  | .acting => FinDist.pure ⟨some false, by simp⟩
  | .done => FinDist.pure ⟨none, by simp⟩

def behavioralProfile (who : Player) :
    information.BehavioralPolicy who := by
  cases who
  exact behavioralPolicy

/-- A genuinely mixed action law at the hidden decision information set. -/
def fullyMixedBehavioralPolicy : information.BehavioralPolicy .player
  | .waiting => FinDist.pure ⟨none, by simp⟩
  | .acting =>
      FinDist.map
        (fun action => ⟨some action, by simp⟩)
        fairCoin
  | .done => FinDist.pure ⟨none, by simp⟩

theorem fullyMixedBehavioralPolicy_fullSupport (view : View) :
    (fullyMixedBehavioralPolicy view).FullSupport := by
  intro choice
  cases view with
  | waiting =>
      rw [fullyMixedBehavioralPolicy, FinDist.mem_support_pure]
      rcases choice with ⟨choice, hchoice⟩
      cases choice with
      | none => rfl
      | some action => simp at hchoice
  | acting =>
      rw [fullyMixedBehavioralPolicy, FinDist.support_map]
      rcases choice with ⟨choice, hchoice⟩
      cases choice with
      | none => simp at hchoice
      | some action =>
          exact ⟨action, mem_support_fairCoin action, rfl⟩
  | done =>
      rw [fullyMixedBehavioralPolicy, FinDist.mem_support_pure]
      rcases choice with ⟨choice, hchoice⟩
      cases choice with
      | none => rfl
      | some action => simp at hchoice

def fullyMixedBehavioralProfile (who : Player) :
    information.BehavioralPolicy who := by
  cases who
  exact fullyMixedBehavioralPolicy

theorem randomizedChooser_initial :
    information.randomizedChooser fullyMixedBehavioralProfile
      execution.initHistory initial_not_terminal =
        FinDist.pure ⟨execution.noop, initialLegal⟩ := by
  letI : Subsingleton
      { joint : Player → Option Bool //
        execution.Legal execution.initHistory.state joint } :=
    ⟨fun first second => Subtype.ext (by
      rw [initial_legal_joint_eq_noop first,
        initial_legal_joint_eq_noop second])⟩
  exact FinDist.eq_pure_of_subsingleton _ _

def oneStepHistory : State → execution.History
  | .decision hidden _ => decisionHistory hidden
  | _ => decisionHistory false

theorem decisionHistory_injective : Function.Injective decisionHistory := by
  intro first second hequal
  have hstate := congrArg (fun history : execution.History => history.state) hequal
  simpa [decisionHistory] using hstate

theorem historyReachProbability_decision (hidden : Bool) :
    information.historyReachProbability fullyMixedBehavioralProfile
      (decisionInformationHistory hidden) = 1 / 2 := by
  classical
  show
    (information.runBehavioral fullyMixedBehavioralProfile 1).prob
      (decisionHistory hidden) = 1 / 2
  rw [InformationModel.runBehavioral, InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 0 initial_not_terminal,
    randomizedChooser_initial, FinDist.pure_bind]
  show
    ((execution.step .initial ⟨execution.noop, initialLegal⟩).bindOnSupport
      (fun _ realized =>
        FinDist.pure (execution.initHistory.extend initialLegal realized))).prob
        (decisionHistory hidden) = 1 / 2
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun state => FinDist.pure (oneStepHistory state))]
  · rw [← FinDist.map_eq_bind, FinDist.map_comp]
    show
      (FinDist.map decisionHistory fairCoin).prob
        (decisionHistory hidden) = 1 / 2
    rw [FinDist.prob_map_of_injective decisionHistory
      decisionHistory_injective fairCoin hidden]
    cases hidden <;> norm_num [fairCoin, FinDist.prob_pure_eq_ite]
  · intro state hstate
    rw [FinDist.support_map] at hstate
    rcases hstate with ⟨side, _hside, rfl⟩
    congr 1

theorem informationSite_info_eq_acting
    (site : information.InformationSite .player) :
    site.1 = View.acting := by
  rcases site.2 with ⟨_history, _hnonterminal, action, haction⟩
  cases hinfo : site.1 <;> simp [information, hinfo] at haction ⊢

theorem informationMass_fullyMixed_pos
    (site : information.InformationSite .player) :
    0 < information.informationMass
      fullyMixedBehavioralProfile .player site := by
  let witness : information.InformationHistory .player site.1 :=
    ⟨decisionHistory false,
      (infoOf_decisionHistory false).trans
        (informationSite_info_eq_acting site).symm⟩
  have hwitness :
      information.historyReachProbability fullyMixedBehavioralProfile witness =
        1 / 2 := by
    simpa [witness] using historyReachProbability_decision false
  have hnonneg :
      ∀ history : information.InformationHistory .player site.1,
        0 ≤ information.historyReachProbability
          fullyMixedBehavioralProfile history := by
    intro history
    exact FinDist.prob_nonneg _ _
  rw [InformationModel.informationMass]
  exact lt_of_lt_of_le (by rw [hwitness]; norm_num)
    (Finset.single_le_sum (fun history _ => hnonneg history)
      (Finset.mem_univ witness))

def assessmentBelief
    (who : Player) (site : information.InformationSite who) :
    FinDist (information.InformationHistory who site.1) := by
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

/-- The Bayes assessment used by the concrete equilibrium theorem. Unlike the
presentation-only assessment above, its decision law has full support and its
belief is constructed by normalizing the existing history reach masses. -/
def fullyMixedAssessment : information.BehavioralAssessment where
  strategy := fullyMixedBehavioralProfile
  belief := fun who site => by
    cases who
    exact information.bayesBelief fullyMixedBehavioralProfile .player site
      (informationMass_fullyMixed_pos site)

theorem fullyMixedAssessment_isFullyMixed :
    fullyMixedAssessment.IsFullyMixed := by
  intro who site
  cases who
  rw [informationSite_info_eq_acting site]
  exact fullyMixedBehavioralPolicy_fullSupport .acting

theorem fullyMixedAssessment_isBayesConsistent :
    fullyMixedAssessment.IsBayesConsistent := by
  intro who site history
  cases who
  exact information.bayesBelief_prob fullyMixedBehavioralProfile .player site
    (informationMass_fullyMixed_pos site) history

theorem fullyMixedAssessment_isSequentiallyConsistent :
    game.IsSequentiallyConsistent fullyMixedAssessment := by
  exact
    InformationModel.BehavioralAssessment.IsSequentiallyConsistent.of_fullyMixed_bayes
      fullyMixedAssessment_isFullyMixed
      fullyMixedAssessment_isBayesConsistent

/-- The hostile hidden-information EFG has an actual sequential equilibrium.
Zero continuation payoff makes every whole continuation policy optimal; full
mixing and finite Bayes consistency make the assessment its own valid
approximating sequence. -/
theorem fullyMixedAssessment_isSequentialEquilibrium :
    game.IsSequentialEquilibriumWithin fullyMixedAssessment payoff 2 := by
  rw [game.isSequentialEquilibriumWithin_iff]
  exact
    ⟨fullyMixedAssessment.isSequentiallyRationalWithin_zero 2,
      fullyMixedAssessment_isSequentiallyConsistent⟩

/-- The language adapter supplies finite history fibers and the canonical
full-policy continuation contexts. This is a genuine proposition, not a stub
or a language-specific equilibrium definition. -/
def sequentialEquilibriumTarget : Prop :=
  game.IsSequentialEquilibriumWithin assessment payoff 2

theorem sequentialEquilibriumTarget_iff :
    sequentialEquilibriumTarget ↔
      assessment.IsSequentiallyRationalWithin payoff 2 ∧
        game.IsSequentiallyConsistent assessment := by
  exact game.isSequentialEquilibriumWithin_iff assessment payoff 2

end GameTheory.Tests.EFG
