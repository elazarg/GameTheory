/-
# Multi-site Bayesian Protocol regret learning

A common fair type creates two positive-probability information sites for each
of two players. Four coupled local regret matchers are assembled into one law
over complete contingent policies, and their shared trace is intended to feed
the static zero-sum regret-to-Nash theorem.
-/

import GameTheory.Analysis.Protocol.CounterfactualRootRegret
import GameTheory.Analysis.ZeroSumLearning
import GameTheory.Languages.Bayesian.Strategic
import Mathlib.Tactic.FinCases

noncomputable section

namespace GameTheory.Analysis.Protocol.BayesianZeroSumLearningTest

open Filter GameTheory GameTheory.Math.Probability Protocol
open GameTheory.Languages.Bayesian
open GameTheory.Protocol.InformationModel
open GameTheory.Analysis.Approachability
open GameTheory.Math.Approachability GameTheory.Math.OrthantProjection

def fairBit : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure false) (PMF.pure true)

def typeProfile (ty : Bool) : Fin 2 → Bool := fun _ => ty

def commonPrior : PMF (Fin 2 → Bool) :=
  fairBit.map typeProfile

def stagePayoff (row col : Bool) : ℝ :=
  if row = col then 1 else -1

/-- The Bayesian carrier is already zero-sum; types affect information but
both positive-probability branches play matching pennies. -/
abbrev game : BayesianGame (Fin 2) where
  Ty _ := Bool
  Act _ := Bool
  prior := commonPrior
  payoff _types actions who :=
    if who = 0 then stagePayoff (actions 0) (actions 1)
    else -stagePayoff (actions 0) (actions 1)

local instance actionNonempty (who : Fin 2) : Nonempty (game.Act who) :=
  ⟨false⟩

local instance typeProfileDecidableEq :
    DecidableEq ((who : Fin 2) → game.Ty who) := Classical.decEq _

local instance stateDecidableEq :
    DecidableEq (Languages.Bayesian.State game) := Classical.decEq _

abbrev execution := Languages.Bayesian.execution game
abbrev information := Languages.Bayesian.informationModel game

local instance infoDecidableEq (who : Fin 2) :
    DecidableEq (information.InfoState who) := Classical.decEq _

local instance allChoiceDecidableEq (who : Fin 2)
    (view : information.InfoState who) :
    DecidableEq (information.Choice who view) := Classical.decEq _

def viewEquiv (who : Fin 2) :
    Languages.Bayesian.View game who ≃ Option (Option Bool) where
  toFun
    | .waiting => none
    | .acting ty => some (some ty)
    | .done => some none
  invFun
    | none => .waiting
    | some (some ty) => .acting ty
    | some none => .done
  left_inv view := by cases view <;> rfl
  right_inv code := by
    rcases code with _ | (_ | _) <;> rfl

local instance infoFintype (who : Fin 2) :
    Fintype (information.InfoState who) :=
  Fintype.ofEquiv (Option (Option Bool)) (viewEquiv who).symm

theorem mem_support_fairBit (ty : Bool) : ty ∈ fairBit.support := by
  rw [PMF.mem_support_iff]
  cases ty <;> norm_num [fairBit, mix_apply, PMF.pure_apply]

theorem mem_support_commonPrior (ty : Bool) :
    typeProfile ty ∈ commonPrior.support := by
  rw [commonPrior, PMF.support_map]
  exact ⟨ty, mem_support_fairBit ty, rfl⟩

theorem initial_not_terminal : ¬execution.terminal (.initial) := by simp

theorem initial_inactive (who : Fin 2) :
    ¬execution.active (.initial) who := by simp

theorem initial_noop_legal :
    execution.Legal (.initial) execution.noop :=
  execution.noop_isLegal initial_not_terminal initial_inactive

theorem typed_mem_support (ty : Bool) :
    Languages.Bayesian.State.typed (B := game) (typeProfile ty) ∈
      (execution.step (.initial)
        ⟨execution.noop, initial_noop_legal⟩).support := by
  show Languages.Bayesian.State.typed (B := game) (typeProfile ty) ∈
    (commonPrior.map (Languages.Bayesian.State.typed (B := game))).support
  rw [PMF.support_map]
  exact ⟨typeProfile ty, mem_support_commonPrior ty, rfl⟩

def typedHistory (ty : Bool) : execution.History :=
  ⟨.typed (typeProfile ty),
    .extend .start execution.noop initial_noop_legal
      (typed_mem_support ty)⟩

@[simp]
theorem typedHistory_state (ty : Bool) :
    (typedHistory ty).state = .typed (typeProfile ty) := rfl

@[reducible]
def site (who : Fin 2) (ty : Bool) : information.InformationSite who :=
  ⟨.acting ty,
    ⟨⟨typedHistory ty, rfl⟩,
      by simp [typedHistory],
      ⟨false, ⟨false, rfl⟩⟩⟩⟩

@[simp]
theorem site_info (who : Fin 2) (ty : Bool) :
    (site who ty).1 =
      (show information.InfoState who from .acting ty) := rfl

abbrev LocalChoice (who : Fin 2) (ty : Bool) :=
  information.Choice who
    (show information.InfoState who from .acting ty)

def choiceOfAction (who : Fin 2) (ty action : Bool) :
    LocalChoice who ty :=
  ⟨some action, by
    show ∃ current : Bool, some action = some current
    exact ⟨action, rfl⟩⟩

private theorem exists_action_eq (who : Fin 2) (ty : Bool)
    (choice : LocalChoice who ty) :
    ∃ action : Bool, choice.1 = some action := by
  rcases choice with ⟨value, hchoice⟩
  cases value with
  | none =>
      simp [Languages.Bayesian.menu] at hchoice
  | some action => exact ⟨action, rfl⟩

def actionOfChoice (who : Fin 2) (ty : Bool)
    (choice : LocalChoice who ty) : Bool :=
  Classical.choose (exists_action_eq who ty choice)

theorem choice_eq_some_actionOfChoice (who : Fin 2) (ty : Bool)
    (choice : LocalChoice who ty) :
    choice.1 = some (actionOfChoice who ty choice) :=
  Classical.choose_spec (exists_action_eq who ty choice)

/-- The simultaneous legal move represented by a complete tuple of local
choices at the realized type. -/
def typedJointOfDraws (ty : Bool)
    (draws : (who : Fin 2) → LocalChoice who ty) :
    { choices : ∀ who, Option (game.Act who) //
      execution.Legal (.typed (typeProfile ty)) choices } :=
  ⟨fun who => (draws who).1,
    execution.legal_of_legalOption (by simp) (fun who => by
      rw [choice_eq_some_actionOfChoice who ty (draws who)]
      exact ⟨trivial, Set.mem_univ _⟩)⟩

theorem typedJointOfDraws_apply (ty : Bool)
    (draws : (who : Fin 2) → LocalChoice who ty) (who : Fin 2) :
    (typedJointOfDraws ty draws).1 who =
      some (actionOfChoice who ty (draws who)) :=
  choice_eq_some_actionOfChoice who ty (draws who)

def choiceEquiv (who : Fin 2) (ty : Bool) :
    LocalChoice who ty ≃ Bool where
  toFun := actionOfChoice who ty
  invFun := choiceOfAction who ty
  left_inv choice := by
    apply Subtype.ext
    exact (choice_eq_some_actionOfChoice who ty choice).symm
  right_inv action := by
    have h := choice_eq_some_actionOfChoice who ty
      (choiceOfAction who ty action)
    exact Option.some.inj h.symm

@[simp]
theorem actionOfChoice_choiceOfAction (who : Fin 2) (ty action : Bool) :
    actionOfChoice who ty (choiceOfAction who ty action) = action :=
  (choiceEquiv who ty).apply_symm_apply action

local instance choiceFintype (who : Fin 2) (ty : Bool) :
    Fintype (LocalChoice who ty) :=
  Fintype.ofEquiv Bool (choiceEquiv who ty).symm

local instance choiceNonempty (who : Fin 2) (ty : Bool) :
    Nonempty (LocalChoice who ty) :=
  ⟨choiceOfAction who ty false⟩

theorem legal_initial_joint_eq_noop {joint : ∀ who, Option (game.Act who)}
    (hlegal : execution.Legal (.initial) joint) : joint = execution.noop := by
  funext who
  have hinactive : ¬execution.active (.initial) who := by simp
  exact LegalOption.eq_none_of_inactive (joint who)
    (execution.legalOption_of_legal hlegal who) hinactive

theorem initial_not_mem_step
    (state : Languages.Bayesian.State game)
    (joint : ∀ who, Option (game.Act who))
    (hlegal : execution.Legal state joint) :
    Languages.Bayesian.State.initial ∉
      (execution.step state ⟨joint, hlegal⟩).support := by
  cases state with
  | initial =>
      rw [PMF.support_map]
      rintro ⟨types, _, heq⟩
      cases heq
  | typed types => simp
  | finished types actions => exact False.elim (hlegal.1 trivial)

theorem trace_initial_eq_start :
    ∀ trace : execution.Trace Languages.Bayesian.State.initial,
      trace = .start
  | .start => rfl
  | .extend _ joint hlegal realized =>
      False.elim (initial_not_mem_step _ joint hlegal realized)

theorem typed_predecessor
    {types : Fin 2 → Bool} {state : Languages.Bayesian.State game}
    {joint : ∀ who, Option (game.Act who)}
    (hlegal : execution.Legal state joint)
    (realized : Languages.Bayesian.State.typed types ∈
      (execution.step state ⟨joint, hlegal⟩).support) :
    state = .initial ∧ joint = execution.noop ∧ types ∈ commonPrior.support := by
  cases state with
  | initial =>
      have hjoint := legal_initial_joint_eq_noop hlegal
      subst joint
      have hrealized : Languages.Bayesian.State.typed types ∈
          (commonPrior.map
            (Languages.Bayesian.State.typed (B := game))).support := realized
      rw [PMF.support_map] at hrealized
      obtain ⟨sourceTypes, hsource, heq⟩ := hrealized
      cases heq
      exact ⟨rfl, rfl, hsource⟩
  | typed priorTypes =>
      rw [PMF.mem_support_pure_iff] at realized
      cases realized
  | finished priorTypes priorActions =>
      exact False.elim (hlegal.1 trivial)

theorem mem_support_commonPrior_eq_typeProfile {types : Fin 2 → Bool}
    (hmem : types ∈ commonPrior.support) :
    ∃ ty, types = typeProfile ty := by
  rw [commonPrior, PMF.support_map] at hmem
  obtain ⟨ty, _, heq⟩ := hmem
  exact ⟨ty, heq.symm⟩

theorem trace_typed_mem_support {types : Fin 2 → Bool} :
    ∀ _trace : execution.Trace (.typed types), types ∈ commonPrior.support
  | .extend _ _joint hlegal realized =>
      (typed_predecessor hlegal realized).2.2

theorem trace_typed_eq (ty : Bool) :
    ∀ trace : execution.Trace (.typed (typeProfile ty)),
      trace = (typedHistory ty).trace
  | .extend prior joint hlegal realized => by
      obtain ⟨hstate, hjoint, _⟩ := typed_predecessor hlegal realized
      subst_vars
      rw [trace_initial_eq_start prior]
      rfl

theorem informationHistory_eq_typedHistory (who : Fin 2) (ty : Bool)
    (history : information.InformationHistory who (site who ty).1) :
    history.1 = typedHistory ty := by
  rcases history with ⟨⟨state, trace⟩, hinfo⟩
  show (⟨state, trace⟩ : execution.History) = typedHistory ty
  rw [Languages.Bayesian.infoOf_eq_viewOfState] at hinfo
  cases state with
  | initial => simp [Languages.Bayesian.viewOfState] at hinfo
  | finished types actions =>
      simp [Languages.Bayesian.viewOfState] at hinfo
  | typed types =>
      have hown : types who = ty := by
        simpa [Languages.Bayesian.viewOfState] using hinfo
      obtain ⟨sourceType, htypes⟩ :=
        mem_support_commonPrior_eq_typeProfile
          (trace_typed_mem_support trace)
      subst types
      have htype : sourceType = ty := hown
      subst sourceType
      rw [trace_typed_eq ty trace]
      rfl

def informationHistoryEquivUnit (who : Fin 2) (ty : Bool) :
    information.InformationHistory who (site who ty).1 ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => ⟨typedHistory ty, rfl⟩
  left_inv history := by
    apply Subtype.ext
    exact (informationHistory_eq_typedHistory who ty history).symm
  right_inv value := by cases value; rfl

local instance informationHistoryFintype (who : Fin 2) (ty : Bool) :
    Fintype (information.InformationHistory who (site who ty).1) :=
  Fintype.ofEquiv Unit (informationHistoryEquivUnit who ty).symm

local instance informationHistoryUnique (who : Fin 2) (ty : Bool) :
    Unique (information.InformationHistory who (site who ty).1) where
  default := ⟨typedHistory ty, rfl⟩
  uniq history := by
    apply Subtype.ext
    exact informationHistory_eq_typedHistory who ty history

theorem site_allNonterminal (who : Fin 2) (ty : Bool) :
    InformationSite.AllNonterminal information (site who ty) := by
  intro history
  rw [informationHistory_eq_typedHistory who ty history]
  simp [typedHistory]

theorem site_commonDepth (who : Fin 2) (ty : Bool) :
    InformationSite.CommonDepth information (site who ty) 1 := by
  intro history
  rw [informationHistory_eq_typedHistory who ty history]
  rfl

theorem actedAt_trace_typed_eq_nil (who : Fin 2)
    {types : Fin 2 → Bool} (trace : execution.Trace (.typed types)) :
    information.actedAt who trace = [] := by
  obtain ⟨ty, htypes⟩ := mem_support_commonPrior_eq_typeProfile
    (trace_typed_mem_support trace)
  subst types
  rw [trace_typed_eq ty trace]
  rfl

theorem information_actsOnce : information.ActsOnceWhereItMatters := by
  intro who state trace
  induction trace with
  | start => simp [InfoSignals.actedAt]
  | @extend source target prior joint hlegal realized ih =>
      rw [InfoSignals.actedAt]
      cases hchoice : joint who with
      | none => exact ih
      | some action =>
          cases source with
          | initial =>
              have hinactive : ¬execution.active (.initial) who := by simp
              have hnone := LegalOption.eq_none_of_inactive (joint who)
                (execution.legalOption_of_legal hlegal who) hinactive
              rw [hchoice] at hnone
              contradiction
          | typed types =>
              rw [actedAt_trace_typed_eq_nil]
              simp
          | finished types actions =>
              exact False.elim (hlegal.1 trivial)

def terminalPayoff (history : execution.History) (who : Fin 2) : ℝ :=
  match history.state with
  | .finished types actions => game.payoff types actions who
  | _ => 0

def statePayoff (state : Languages.Bayesian.State game) (who : Fin 2) : ℝ :=
  match state with
  | .finished types actions => game.payoff types actions who
  | _ => 0

theorem terminalPayoff_eq_statePayoff (history : execution.History)
    (who : Fin 2) :
    terminalPayoff history who = statePayoff history.state who := rfl

theorem statePayoff_bound (who : Fin 2)
    (state : Languages.Bayesian.State game) :
    |statePayoff state who| ≤ 1 := by
  cases state with
  | initial => norm_num [statePayoff]
  | typed types => norm_num [statePayoff]
  | finished types actions =>
      fin_cases who <;>
        cases hrow : actions 0 <;>
        cases hcol : actions 1 <;>
        norm_num [statePayoff, game, stagePayoff, hrow, hcol]

theorem terminalPayoff_zeroSum (history : execution.History) :
    terminalPayoff history 1 = -terminalPayoff history 0 := by
  rcases history with ⟨state, trace⟩
  cases state <;> simp [terminalPayoff]

theorem terminalPayoff_bound (who : Fin 2) (history : execution.History) :
    |terminalPayoff history who| ≤ 1 := by
  rcases history with ⟨state, trace⟩
  cases state with
  | initial => norm_num [terminalPayoff]
  | typed types => norm_num [terminalPayoff]
  | finished types actions =>
      fin_cases who <;>
        cases hrow : actions 0 <;>
        cases hcol : actions 1 <;>
        norm_num [terminalPayoff, game, stagePayoff, hrow, hcol]

theorem terminalPayoff_integrable (who : Fin 2)
    (law : PMF execution.History) :
    PayoffIntegrable law (fun history => terminalPayoff history who) :=
  payoffIntegrable_of_bounded law _ (terminalPayoff_bound who)

/-- A realized all-some move from a typed history has the specified terminal
payoff, independently of the trace's proof fields. -/
theorem terminalPayoff_typed_step (ty : Bool)
    (joint : { choices : ∀ i, Option (game.Act i) //
      execution.Legal (.typed (typeProfile ty)) choices })
    (actions : ∀ i, game.Act i)
    (hjoint : ∀ i, joint.1 i = some (actions i))
    {target : Languages.Bayesian.State game}
    (realized : target ∈
      (execution.step (.typed (typeProfile ty)) joint).support)
    (who : Fin 2) :
    terminalPayoff ((typedHistory ty).extend joint.2 realized) who =
      game.payoff (typeProfile ty) actions who := by
  have hstep := Languages.Bayesian.execution_step_typed_of_actions
    game (typeProfile ty) joint actions hjoint
  rw [hstep, PMF.mem_support_pure_iff] at realized
  subst target
  rfl

def typedStepLaw
    (strategy : (who : Fin 2) → information.BehavioralPolicy who)
    (ty : Bool) : PMF execution.History :=
  (information.behavioralJoint strategy (typedHistory ty).trace
    (by simp [typedHistory])).bind fun draw =>
      (execution.step (typedHistory ty).state draw).bindOnSupport
        fun _ realized => information.runBehavioralFrom strategy 0
          ((typedHistory ty).extend draw.2 realized)

theorem runBehavioralFrom_typed_one
    (strategy : (who : Fin 2) → information.BehavioralPolicy who)
    (ty : Bool) :
    information.runBehavioralFrom strategy 1 (typedHistory ty) =
      typedStepLaw strategy ty := by
  exact information.runBehavioralFrom_succ_of_not_terminal strategy 0
    (by simp [typedHistory])

/-- Forgetting the trace after one typed step leaves the ordinary joint-step
state law. This normalization does not inspect a dependent history trace. -/
theorem typedStepLaw_map_state
    (strategy : (who : Fin 2) → information.BehavioralPolicy who)
    (ty : Bool) :
    (typedStepLaw strategy ty).map ExecutionProtocol.History.state =
      (information.behavioralJoint strategy (typedHistory ty).trace
        (by simp [typedHistory])).bind
        (execution.step (typedHistory ty).state) := by
  unfold typedStepLaw
  rw [PMF.map_bind]
  apply bind_congr_on_support
  intro joint _
  rw [map_bindOnSupport]
  calc
    _ = (execution.step (typedHistory ty).state joint).bind PMF.pure := by
      apply bindOnSupport_eq_bind_of_eq_on_support
      intro target realized
      simp only [InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero, PMF.pure_map,
        ExecutionProtocol.History.extend_state]
    _ = _ := PMF.bind_pure _

/-- The one-step continuation payoff factors through the trace-free state
law, with integrability certified against each actual law. -/
theorem terminalPayoff_expect_typedStepLaw
    (strategy : (who : Fin 2) → information.BehavioralPolicy who)
    (ty : Bool) (who : Fin 2) :
    expect (typedStepLaw strategy ty)
        (fun history => terminalPayoff history who)
        (terminalPayoff_integrable who _) =
      expect ((information.behavioralJoint strategy (typedHistory ty).trace
          (by simp [typedHistory])).bind
          (execution.step (typedHistory ty).state))
        (fun state => statePayoff state who)
        (payoffIntegrable_of_bounded _ _ (statePayoff_bound who)) := by
  calc
    _ = expect ((typedStepLaw strategy ty).map ExecutionProtocol.History.state)
          (fun state => statePayoff state who)
          (payoffIntegrable_of_bounded _ _ (statePayoff_bound who)) := by
        symm
        simpa only [Function.comp_def, terminalPayoff_eq_statePayoff] using
          (expect_map ExecutionProtocol.History.state (typedStepLaw strategy ty)
            (fun state => statePayoff state who)
            (terminalPayoff_integrable who _)
            (payoffIntegrable_of_bounded _ _ (statePayoff_bound who)))
    _ = _ := expect_congr_law (typedStepLaw_map_state strategy ty)
      (fun state => statePayoff state who)
      (payoffIntegrable_of_bounded _ _ (statePayoff_bound who))
      (payoffIntegrable_of_bounded _ _ (statePayoff_bound who))

/-- Each complete typed draw has the exact deterministic stage payoff. -/
theorem typedJoint_statePayoff_value (ty : Bool)
    (draws : (player : Fin 2) → LocalChoice player ty)
    (who : Fin 2) :
    expect (execution.step (.typed (typeProfile ty))
        (typedJointOfDraws ty draws))
      (fun state => statePayoff state who)
      (payoffIntegrable_of_bounded _ _ (statePayoff_bound who)) =
    game.payoff (typeProfile ty)
      (fun player => actionOfChoice player ty (draws player)) who := by
  rw [Languages.Bayesian.execution_step_typed_of_actions game
    (typeProfile ty) (typedJointOfDraws ty draws)
      (fun player => actionOfChoice player ty (draws player))
      (typedJointOfDraws_apply ty draws)]
  exact expect_pure _ _ _

/-- At a typed history, the behavioral joint is the independent product of
the two local choice laws, mapped to their legal simultaneous move. -/
theorem behavioralJoint_typed
    (strategy : (player : Fin 2) → information.BehavioralPolicy player)
    (ty : Bool) :
    information.behavioralJoint strategy (typedHistory ty).trace
        (by simp [typedHistory]) =
      PMF.map (typedJointOfDraws ty)
        (independentProduct fun player => strategy player (.acting ty)) := by
  unfold InformationModel.behavioralJoint
  have hlaws :
      (fun player => strategy player
        (information.infoOf player (typedHistory ty).trace)) =
        (fun player => strategy player (.acting ty)) := by
    funext player
    rfl
  rw [hlaws]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- At either realized type, the one-step continuation value is the exact
stage payoff integrated over the two independent local choice laws. -/
theorem typedStepLaw_value_product
    (strategy : (player : Fin 2) → information.BehavioralPolicy player)
    (ty : Bool) (who : Fin 2) :
    expect (typedStepLaw strategy ty)
        (fun history => terminalPayoff history who)
        (terminalPayoff_integrable who _) =
      expect (independentProduct fun player => strategy player (.acting ty))
        (fun draws => game.payoff (typeProfile ty)
          (fun player => actionOfChoice player ty (draws player)) who)
        (payoffIntegrable_of_finite _ _) := by
  let drawLaw := independentProduct fun player => strategy player (.acting ty)
  let stepLaw := PMF.map (typedJointOfDraws ty) drawLaw
  let payoffOnState := fun state => statePayoff state who
  have hlaw :
      (information.behavioralJoint strategy (typedHistory ty).trace
        (by simp [typedHistory])).bind
          (execution.step (typedHistory ty).state) =
        stepLaw.bind (execution.step (typedHistory ty).state) :=
    congrArg (fun law => law.bind (execution.step (typedHistory ty).state))
      (behavioralJoint_typed strategy ty)
  calc
    _ = expect ((information.behavioralJoint strategy (typedHistory ty).trace
          (by simp [typedHistory])).bind
          (execution.step (typedHistory ty).state)) payoffOnState
        (payoffIntegrable_of_bounded _ _ (statePayoff_bound who)) :=
      terminalPayoff_expect_typedStepLaw strategy ty who
    _ = expect (stepLaw.bind (execution.step (typedHistory ty).state))
        payoffOnState
        (payoffIntegrable_of_bounded _ _ (statePayoff_bound who)) :=
      expect_congr_law hlaw payoffOnState
        (payoffIntegrable_of_bounded _ _ (statePayoff_bound who))
        (payoffIntegrable_of_bounded _ _ (statePayoff_bound who))
    _ = expect drawLaw
        (fun draws => game.payoff (typeProfile ty)
          (fun player => actionOfChoice player ty (draws player)) who)
        (payoffIntegrable_of_finite _ _) := by
      dsimp only [stepLaw, payoffOnState]
      rw [expect_bind_tower_bounded _ _ _ (by norm_num)
        (statePayoff_bound who)]
      rw [expect_map _ _ _ (payoffIntegrable_of_finite _ _) _]
      apply expect_congr_on_support
      intro draws _
      simpa only [Function.comp_def, payoffOnState, typedHistory_state] using
        (typedJoint_statePayoff_value ty draws who)

theorem localRegretsIntegrable
    (strategy : (who : Fin 2) → information.BehavioralPolicy who)
    (who : Fin 2) (ty : Bool) :
    information.LocalCounterfactualRegretsIntegrable strategy who
      (site who ty) (fun history => terminalPayoff history who) 1 := by
  constructor
  · intro choice history _
    exact terminalPayoff_integrable who _
  · intro history _
    exact terminalPayoff_integrable who _

/-- This finite fixture integrates every strategic payoff against its actual law. -/
def finiteExpect {α : Type*} [Fintype α] (law : PMF α)
    (payoff : α → ℝ) : ℝ :=
  expect law payoff (payoffIntegrable_of_finite law payoff)

structure LearningState where
  rowFalse : EuclideanSpace ℝ (LocalChoice 0 false)
  rowTrue : EuclideanSpace ℝ (LocalChoice 0 true)
  colFalse : EuclideanSpace ℝ (LocalChoice 1 false)
  colTrue : EuclideanSpace ℝ (LocalChoice 1 true)

def averageOfState (state : LearningState) :
    (who : Fin 2) → (ty : Bool) →
      EuclideanSpace ℝ (LocalChoice who ty)
  | 0, false => state.rowFalse
  | 0, true => state.rowTrue
  | 1, false => state.colFalse
  | 1, true => state.colTrue

def policyOfState (state : LearningState) (who : Fin 2) :
    information.BehavioralPolicy who := fun view =>
  match view with
  | .waiting => PMF.pure ⟨none, by simp [Languages.Bayesian.menu]⟩
  | .acting ty => regretMatch (averageOfState state who ty)
  | .done => PMF.pure ⟨none, by simp [Languages.Bayesian.menu]⟩

def strategyOfState (state : LearningState) :
    (who : Fin 2) → information.BehavioralPolicy who :=
  policyOfState state

@[simp]
theorem strategyOfState_at_site (state : LearningState) (who : Fin 2)
    (ty : Bool) :
    strategyOfState state who (site who ty).1 =
      regretMatch (averageOfState state who ty) := rfl

def instantaneous (state : LearningState) (who : Fin 2) (ty : Bool) :
    EuclideanSpace ℝ (LocalChoice who ty) :=
  localCounterfactualRegretVector information (strategyOfState state) who
    (site who ty) (fun history => terminalPayoff history who) 1
      (localRegretsIntegrable (strategyOfState state) who ty)

/-- All four local sites update simultaneously by the same Cesaro recurrence
used in the canonical D46 average. -/
def learningState : ℕ → LearningState
  | 0 => ⟨0, 0, 0, 0⟩
  | n + 1 =>
      let current := learningState n
      ⟨((n : ℝ) / ((n : ℝ) + 1)) • current.rowFalse +
          (1 / ((n : ℝ) + 1)) • instantaneous current 0 false,
        ((n : ℝ) / ((n : ℝ) + 1)) • current.rowTrue +
          (1 / ((n : ℝ) + 1)) • instantaneous current 0 true,
        ((n : ℝ) / ((n : ℝ) + 1)) • current.colFalse +
          (1 / ((n : ℝ) + 1)) • instantaneous current 1 false,
        ((n : ℝ) / ((n : ℝ) + 1)) • current.colTrue +
          (1 / ((n : ℝ) + 1)) • instantaneous current 1 true⟩

def localStrategyOf (who : Fin 2) (ty : Bool)
    (law : PMF (LocalChoice who ty))
    (state : LearningState) :
    (player : Fin 2) → information.BehavioralPolicy player :=
  strategyWithLocalLaw information (strategyOfState state) who
    (site who ty) law

def localPayoffOf (who : Fin 2) (_ty : Bool) (_state : LearningState) :
    execution.History → ℝ := fun history => terminalPayoff history who

def scheduleEnvironment (_who : Fin 2) (_ty : Bool) (round : ℕ) :
    LearningState := learningState round

theorem localStrategyOf_current_eq (state : LearningState) (who : Fin 2)
    (ty : Bool) :
    localStrategyOf who ty
        (regretMatch (averageOfState state who ty)) state =
      strategyOfState state := by
  unfold localStrategyOf
  rw [← strategyOfState_at_site state who ty]
  unfold strategyWithLocalLaw
  have hpolicy := BehavioralPolicy.withLaw_eq_self
    (M := information) (strategyOfState state who) (site who ty).1
  rw [hpolicy]
  exact Profile.update_eq_self _ who

def localUtility (who : Fin 2) (ty : Bool)
    (choice : LocalChoice who ty) (state : LearningState) : ℝ :=
  information.counterfactualActionUtility (strategyOfState state) who
    (site who ty) (fun history => terminalPayoff history who) 1 choice
      ((localRegretsIntegrable (strategyOfState state) who ty).1 choice)

theorem local_realization (who : Fin 2) (ty : Bool)
    (law : PMF (LocalChoice who ty)) (state : LearningState) :
    localCounterfactualRegretVector information
        (localStrategyOf who ty law state) who (site who ty)
          (localPayoffOf who ty state) 1
          (localRegretsIntegrable (localStrategyOf who ty law state) who ty) =
      regretPayoff (localUtility who ty) law state
        (payoffIntegrable_of_finite _ _) := by
  have h := information.localCounterfactualRegretVector_strategyWithLocalLaw
    information_actsOnce (strategyOfState state) who (site who ty)
      (site_allNonterminal who ty) law
      (fun history => terminalPayoff history who) 0 state
      (localRegretsIntegrable (localStrategyOf who ty law state) who ty)
      (localRegretsIntegrable (strategyOfState state) who ty).1
  calc
    _ = localCounterfactualRegretVector information
        (strategyWithLocalLaw information (strategyOfState state) who
          (site who ty) law)
        who (site who ty) (fun history => terminalPayoff history who) 1
        (localRegretsIntegrable _ who ty) := rfl
    _ = regretPayoff
        (fun choice (_current : LearningState) =>
          information.counterfactualActionUtility (strategyOfState state) who
            (site who ty) (fun history => terminalPayoff history who) 1 choice
            ((localRegretsIntegrable (strategyOfState state) who ty).1 choice))
        law state (payoffIntegrable_of_finite _ _) := h
    _ = regretPayoff (localUtility who ty) law state
          (payoffIntegrable_of_finite _ _) := by
      ext choice
      rfl

def localAverage (who : Fin 2) (ty : Bool) (round : ℕ) :
    EuclideanSpace ℝ (LocalChoice who ty) :=
  counterfactualRegretMatchAverage information who (site who ty)
    (localStrategyOf who ty) (localPayoffOf who ty) 1
      (fun law state => localRegretsIntegrable
        (localStrategyOf who ty law state) who ty)
      (scheduleEnvironment who ty) round

theorem localAverage_succ (who : Fin 2) (ty : Bool) (round : ℕ) :
    localAverage who ty (round + 1) =
      ((round : ℝ) / ((round : ℝ) + 1)) • localAverage who ty round +
        (1 / ((round : ℝ) + 1)) •
          localCounterfactualRegretVector information
            (localStrategyOf who ty
              (regretMatch (localAverage who ty round)) (learningState round))
            who (site who ty) (fun history => terminalPayoff history who) 1
              (localRegretsIntegrable _ who ty) :=
  rfl

/-- The explicit four-coordinate recurrence is exactly the family of D46
averages. This is the scheduling invariant the one-site experiment lacked. -/
theorem localAverage_eq_state (who : Fin 2) (ty : Bool) (round : ℕ) :
    localAverage who ty round = averageOfState (learningState round) who ty := by
  induction round with
  | zero =>
      fin_cases who <;> cases ty <;>
        rfl
  | succ round ih =>
      rw [localAverage_succ, ih, localStrategyOf_current_eq]
      fin_cases who <;> cases ty <;> rfl

theorem typeProfile_injective : Function.Injective typeProfile := by
  intro first second heq
  exact congrFun heq 0

theorem commonPrior_prob_typeProfile (ty : Bool) :
    commonPrior (typeProfile ty) = 1 / 2 := by
  rw [commonPrior,
    pmf_map_apply_of_injective fairBit typeProfile_injective]
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)]
    norm_num
  cases ty <;> norm_num [fairBit, mix_apply, PMF.pure_apply, hhalf]

theorem initial_step_prob_typed (ty : Bool) :
    (execution.step (.initial) ⟨execution.noop, initial_noop_legal⟩)
        (.typed (typeProfile ty)) = 1 / 2 := by
  show (commonPrior.map (Languages.Bayesian.State.typed (B := game)))
      (.typed (typeProfile ty)) = 1 / 2
  rw [pmf_map_apply_of_injective]
  · exact commonPrior_prob_typeProfile ty
  · intro first second heq
    exact Languages.Bayesian.State.typed.inj heq

theorem initial_noop_choice_prob (state : LearningState) (other : Fin 2) :
    ((strategyOfState state other)
        (information.infoOf other ExecutionProtocol.Trace.start))
      (choicesOfLegal information ExecutionProtocol.Trace.start
        ⟨execution.noop, initial_noop_legal⟩ other) = 1 := by
  dsimp only [strategyOfState, policyOfState, choicesOfLegal,
    InfoSignals.infoOf, Languages.Bayesian.signals]
  exact PMF.pure_apply_self _

theorem opponentsStepProb_initial_noop (state : LearningState) (who : Fin 2) :
    opponentsStepProb information (strategyOfState state) who
        ExecutionProtocol.Trace.start
        ⟨execution.noop, initial_noop_legal⟩ = 1 := by
  classical
  unfold opponentsStepProb
  apply Finset.prod_eq_one
  intro other hother
  exact congrArg ENNReal.toReal (initial_noop_choice_prob state other)

theorem counterfactualReach_typedHistory (state : LearningState)
    (who : Fin 2) (ty : Bool) :
    information.counterfactualReachProbability (strategyOfState state) who
        (typedHistory ty).trace = 1 / 2 := by
  unfold typedHistory
  simp only [counterfactualReachProbability, one_mul]
  unfold counterfactualStepProb
  rw [opponentsStepProb_initial_noop, initial_step_prob_typed]
  norm_num

theorem terminalPayoff_mem_Icc (history : execution.History) (who : Fin 2) :
    terminalPayoff history who ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases history with ⟨state, trace⟩
  cases state with
  | initial => simp [terminalPayoff]
  | typed types => simp [terminalPayoff]
  | finished types actions =>
      fin_cases who <;> simp [terminalPayoff, stagePayoff]
      <;> split <;> norm_num

theorem behavioralContinuationValue_mem_Icc
    (strategy : (player : Fin 2) → information.BehavioralPolicy player)
    (who : Fin 2) (alternative : information.BehavioralPolicy who)
    (fuel : ℕ) (history : execution.History) :
    information.behavioralContinuationValue strategy who alternative
        (fun final => terminalPayoff final who) fuel history
        (terminalPayoff_integrable who _) ∈
      Set.Icc (-1 : ℝ) 1 := by
  unfold InformationModel.behavioralContinuationValue
  exact abs_le.mp (expect_abs_le_of_bounded (by norm_num)
    (terminalPayoff_bound who) (terminalPayoff_integrable who _))

theorem localUtility_mem_Icc (who : Fin 2) (ty : Bool)
    (choice : LocalChoice who ty) (state : LearningState) :
    localUtility who ty choice state ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
  unfold localUtility counterfactualActionUtility
    counterfactualContinuationValue
  rw [Fintype.sum_unique]
  dsimp only [default, informationHistoryUnique]
  simp only [counterfactualReach_typedHistory, dite_eq_left
    (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  have hcontinuation := behavioralContinuationValue_mem_Icc
    (strategyOfState state) who
      ((strategyOfState state who).commit (site who ty).1 choice) 1
      (typedHistory ty)
  constructor <;> nlinarith [hcontinuation.1, hcontinuation.2]

theorem local_regretPayoff_norm_le (who : Fin 2) (ty : Bool)
    (law : PMF (LocalChoice who ty)) (state : LearningState) :
    ‖regretPayoff (localUtility who ty) law state
      (payoffIntegrable_of_finite _ _)‖ ≤
      (Fintype.card (LocalChoice who ty) : ℝ) := by
  have h := regretPayoff_norm_le_card_mul_width (localUtility who ty)
    (lo := -(1 / 2)) (hi := 1 / 2) (localUtility_mem_Icc who ty) law state
  norm_num at h
  simpa only [Set.fintypeCard_eq_ncard] using h

theorem local_approaches (who : Fin 2) (ty : Bool) :
    Tendsto
      (fun t => Metric.infDist (localAverage who ty t) nonposOrthant)
      atTop (nhds 0) := by
  simpa only [localAverage, counterfactualRegretMatchAverage] using
    counterfactualRegretMatch_approaches information who (site who ty)
      (localUtility who ty) (localStrategyOf who ty) (localPayoffOf who ty) 1
      (fun law state => localRegretsIntegrable
        (localStrategyOf who ty law state) who ty)
      (local_realization who ty) (bound := Fintype.card (LocalChoice who ty))
      (by positivity) (local_regretPayoff_norm_le who ty)
      (scheduleEnvironment who ty)

def learnedLaw (who : Fin 2) (ty : Bool) (round : ℕ) :
    PMF (LocalChoice who ty) :=
  regretMatch (localAverage who ty round)

def currentLaw (state : LearningState) (who : Fin 2) (ty : Bool) :
    PMF (LocalChoice who ty) :=
  regretMatch (averageOfState state who ty)

def rowCommitted (state : LearningState) (ty : Bool)
    (choice : LocalChoice 0 ty) :
    (player : Fin 2) → information.BehavioralPolicy player :=
  Profile.update (sig := information.behavioralSignature)
    (strategyOfState state) 0
    ((strategyOfState state 0).commit (.acting ty) choice)

theorem rowCommitted_first (state : LearningState) (ty : Bool)
    (choice : LocalChoice 0 ty) :
    rowCommitted state ty choice 0 (.acting ty) = PMF.pure choice := by
  simp only [rowCommitted, Profile.update_same, BehavioralPolicy.commit_self]

theorem rowCommitted_second (state : LearningState) (ty : Bool)
    (choice : LocalChoice 0 ty) :
    rowCommitted state ty choice 1 (.acting ty) = currentLaw state 1 ty := by
  simp [rowCommitted, strategyOfState, policyOfState, currentLaw]

theorem rowCommitted_product_value (state : LearningState) (ty : Bool)
    (choice : LocalChoice 0 ty) :
    expect (independentProduct fun player =>
        rowCommitted state ty choice player (.acting ty))
      (fun draws => game.payoff (typeProfile ty)
        (fun player => actionOfChoice player ty (draws player)) 0)
      (payoffIntegrable_of_finite _ _) =
    finiteExpect (currentLaw state 1 ty) (fun other =>
      stagePayoff (actionOfChoice 0 ty choice)
        (actionOfChoice 1 ty other)) := by
  let p := independentProduct fun player =>
    rowCommitted state ty choice player (.acting ty)
  have hrow (draws : (player : Fin 2) → LocalChoice player ty)
      (hd : draws ∈ p.support) : draws 0 = choice := by
    have hcoord := (independentProduct_support_iff _ draws).mp hd 0
    rw [rowCommitted_first, PMF.mem_support_pure_iff] at hcoord
    exact hcoord
  calc
    _ = expect p (fun draws =>
        stagePayoff (actionOfChoice 0 ty choice)
          (actionOfChoice 1 ty (draws 1)))
        (payoffIntegrable_of_finite _ _) := by
      apply expect_congr_on_support
      intro draws hd
      simp [hrow draws hd]
    _ = expect (p.map fun draws => draws 1)
        (fun other => stagePayoff (actionOfChoice 0 ty choice)
          (actionOfChoice 1 ty other))
        (payoffIntegrable_of_finite _ _) := by
      symm
      simpa only [Function.comp_def] using
        (expect_map (fun draws => draws 1) p
          (fun other => stagePayoff (actionOfChoice 0 ty choice)
            (actionOfChoice 1 ty other))
          (payoffIntegrable_of_finite _ _)
          (payoffIntegrable_of_finite _ _))
    _ = _ := by
      dsimp only [p, finiteExpect]
      rw [independentProduct_map_eval, rowCommitted_second]

theorem rowContinuation_value (state : LearningState) (ty : Bool)
    (choice : LocalChoice 0 ty) :
    expect (information.runBehavioralFrom
        (rowCommitted state ty choice) 1 (typedHistory ty))
      (fun history => terminalPayoff history 0)
      (terminalPayoff_integrable 0 _) =
    finiteExpect (currentLaw state 1 ty) (fun other =>
      stagePayoff (actionOfChoice 0 ty choice)
        (actionOfChoice 1 ty other)) := by
  calc
    _ = expect (typedStepLaw (rowCommitted state ty choice) ty)
          (fun history => terminalPayoff history 0)
          (terminalPayoff_integrable 0 _) :=
      expect_congr_law
        (runBehavioralFrom_typed_one (rowCommitted state ty choice) ty)
        (fun history => terminalPayoff history 0)
        (terminalPayoff_integrable 0 _) (terminalPayoff_integrable 0 _)
    _ = expect (independentProduct fun player =>
          rowCommitted state ty choice player (.acting ty))
        (fun draws => game.payoff (typeProfile ty)
          (fun player => actionOfChoice player ty (draws player)) 0)
        (payoffIntegrable_of_finite _ _) :=
      typedStepLaw_value_product (rowCommitted state ty choice) ty 0
    _ = _ := rowCommitted_product_value state ty choice

def columnCommitted (state : LearningState) (ty : Bool)
    (choice : LocalChoice 1 ty) :
    (player : Fin 2) → information.BehavioralPolicy player :=
  Profile.update (sig := information.behavioralSignature)
    (strategyOfState state) 1
    ((strategyOfState state 1).commit (.acting ty) choice)

theorem columnCommitted_first (state : LearningState) (ty : Bool)
    (choice : LocalChoice 1 ty) :
    columnCommitted state ty choice 0 (.acting ty) = currentLaw state 0 ty := by
  simp [columnCommitted, strategyOfState, policyOfState, currentLaw]

theorem columnCommitted_second (state : LearningState) (ty : Bool)
    (choice : LocalChoice 1 ty) :
    columnCommitted state ty choice 1 (.acting ty) = PMF.pure choice := by
  simp only [columnCommitted, Profile.update_same, BehavioralPolicy.commit_self]

theorem columnCommitted_product_value (state : LearningState) (ty : Bool)
    (choice : LocalChoice 1 ty) :
    expect (independentProduct fun player =>
        columnCommitted state ty choice player (.acting ty))
      (fun draws => game.payoff (typeProfile ty)
        (fun player => actionOfChoice player ty (draws player)) 1)
      (payoffIntegrable_of_finite _ _) =
    -finiteExpect (currentLaw state 0 ty) (fun other =>
      stagePayoff (actionOfChoice 0 ty other)
        (actionOfChoice 1 ty choice)) := by
  let p := independentProduct fun player =>
    columnCommitted state ty choice player (.acting ty)
  have hcolumn (draws : (player : Fin 2) → LocalChoice player ty)
      (hd : draws ∈ p.support) : draws 1 = choice := by
    have hcoord := (independentProduct_support_iff _ draws).mp hd 1
    rw [columnCommitted_second, PMF.mem_support_pure_iff] at hcoord
    exact hcoord
  calc
    _ = expect p (fun draws =>
        -stagePayoff (actionOfChoice 0 ty (draws 0))
          (actionOfChoice 1 ty choice))
        (payoffIntegrable_of_finite _ _) := by
      apply expect_congr_on_support
      intro draws hd
      simp [hcolumn draws hd]
    _ = expect (p.map fun draws => draws 0)
        (fun other => -stagePayoff (actionOfChoice 0 ty other)
          (actionOfChoice 1 ty choice))
        (payoffIntegrable_of_finite _ _) := by
      symm
      simpa only [Function.comp_def] using
        (expect_map (fun draws => draws 0) p
          (fun other => -stagePayoff (actionOfChoice 0 ty other)
            (actionOfChoice 1 ty choice))
          (payoffIntegrable_of_finite _ _)
          (payoffIntegrable_of_finite _ _))
    _ = expect (currentLaw state 0 ty)
        (fun other => -stagePayoff (actionOfChoice 0 ty other)
          (actionOfChoice 1 ty choice))
        (payoffIntegrable_of_finite _ _) := by
      dsimp only [p]
      rw [independentProduct_map_eval, columnCommitted_first]
    _ = _ := by
      simpa only [finiteExpect] using
        (expect_neg (payoffIntegrable_of_finite (currentLaw state 0 ty)
          (fun other => stagePayoff (actionOfChoice 0 ty other)
            (actionOfChoice 1 ty choice))))

theorem columnContinuation_value (state : LearningState) (ty : Bool)
    (choice : LocalChoice 1 ty) :
    expect (information.runBehavioralFrom
        (columnCommitted state ty choice) 1 (typedHistory ty))
      (fun history => terminalPayoff history 1)
      (terminalPayoff_integrable 1 _) =
    -finiteExpect (currentLaw state 0 ty) (fun other =>
      stagePayoff (actionOfChoice 0 ty other)
        (actionOfChoice 1 ty choice)) := by
  calc
    _ = expect (typedStepLaw (columnCommitted state ty choice) ty)
          (fun history => terminalPayoff history 1)
          (terminalPayoff_integrable 1 _) :=
      expect_congr_law
        (runBehavioralFrom_typed_one (columnCommitted state ty choice) ty)
        (fun history => terminalPayoff history 1)
        (terminalPayoff_integrable 1 _) (terminalPayoff_integrable 1 _)
    _ = expect (independentProduct fun player =>
          columnCommitted state ty choice player (.acting ty))
        (fun draws => game.payoff (typeProfile ty)
          (fun player => actionOfChoice player ty (draws player)) 1)
        (payoffIntegrable_of_finite _ _) :=
      typedStepLaw_value_product (columnCommitted state ty choice) ty 1
    _ = _ := columnCommitted_product_value state ty choice

theorem localUtility_row_eq (ty : Bool) (choice : LocalChoice 0 ty)
    (state : LearningState) :
    localUtility 0 ty choice state =
      (1 / 2) * finiteExpect (currentLaw state 1 ty) (fun other =>
        stagePayoff (actionOfChoice 0 ty choice)
          (actionOfChoice 1 ty other)) := by
  unfold localUtility counterfactualActionUtility
    counterfactualContinuationValue
  rw [Fintype.sum_unique]
  dsimp only [default, informationHistoryUnique]
  simp only [counterfactualReach_typedHistory, dite_eq_left
    (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  unfold behavioralContinuationValue
  simpa only [rowCommitted] using
    congrArg (fun value : ℝ => (1 / 2 : ℝ) * value)
      (rowContinuation_value state ty choice)
theorem localUtility_column_eq (ty : Bool) (choice : LocalChoice 1 ty)
    (state : LearningState) :
    localUtility 1 ty choice state =
      -(1 / 2) * finiteExpect (currentLaw state 0 ty) (fun other =>
        stagePayoff (actionOfChoice 0 ty other)
          (actionOfChoice 1 ty choice)) := by
  unfold localUtility counterfactualActionUtility
    counterfactualContinuationValue
  rw [Fintype.sum_unique]
  dsimp only [default, informationHistoryUnique]
  simp only [counterfactualReach_typedHistory, dite_eq_left
    (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  unfold behavioralContinuationValue
  have hvalue := columnContinuation_value state ty choice
  simpa only [columnCommitted, mul_neg, neg_mul] using
    congrArg (fun value : ℝ => (1 / 2 : ℝ) * value) hvalue
theorem learnedLaw_eq_current (who : Fin 2) (ty : Bool) (round : ℕ) :
    learnedLaw who ty round =
      currentLaw (learningState round) who ty := by
  rw [learnedLaw, localAverage_eq_state]
  rfl

/-- A pure strategic deviation specifies one legal action at each of the
player's two positive-probability type sites. -/
abbrev ContingentChoice (who : Fin 2) :=
  (ty : Bool) → LocalChoice who ty

local instance contingentChoiceFintype (who : Fin 2) :
    Fintype (ContingentChoice who) := by
  unfold ContingentChoice
  infer_instance

local instance matrixStrategyFintype (who : Fin 2) :
    Fintype ((MatrixGame.form
      (ContingentChoice 0) (ContingentChoice 1)).sig.Strategy who) := by
  induction who using Fin.cases with
  | zero => exact contingentChoiceFintype 0
  | succ next =>
      induction next using Fin.cases with
      | zero => exact contingentChoiceFintype 1
      | succ impossible => exact impossible.elim0

def contingentLaw (who : Fin 2) (round : ℕ) :
    PMF (ContingentChoice who) :=
  independentProduct fun ty => learnedLaw who ty round

def actionPlan (who : Fin 2) (choices : ContingentChoice who) : Bool → Bool :=
  fun ty => actionOfChoice who ty (choices ty)

def planProfile (row : ContingentChoice 0) (col : ContingentChoice 1) :
    Profile game.signature
  | 0 => actionPlan 0 row
  | 1 => actionPlan 1 col

def matrixPayoff (row : ContingentChoice 0) (col : ContingentChoice 1) : ℝ :=
  (1 / 2) * stagePayoff (actionPlan 0 row false) (actionPlan 1 col false) +
    (1 / 2) * stagePayoff (actionPlan 0 row true) (actionPlan 1 col true)

set_option backward.isDefEq.respectTransparency false in
/-- The matrix carrier is not a surrogate game: on every pair of complete
contingent choices, its payoff is the direct Bayesian game's ex-ante payoff. -/
theorem matrixPayoff_eq_direct_expectedUtility
    (row : ContingentChoice 0) (col : ContingentChoice 1) :
    matrixPayoff row col =
      expectedUtility game.utility 0
        (game.toForm.play (planProfile row col))
        (payoffIntegrable_of_finite _ _) := by
  rw [BayesianGame.toForm_play]
  unfold expectedUtility
  rw [expect_map _ _ _ (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)]
  unfold matrixPayoff
  simp only [game, BayesianGame.utility]
  unfold commonPrior fairBit
  rw [expect_map _ _ _ (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)]
  rw [expect_mix _ _ _ _ _ _
    (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _), expect_pure, expect_pure]
  simp [planProfile, BayesianGame.actionsOf, typeProfile, stagePayoff]
  ring_nf

def localGain (who : Fin 2) (ty : Bool) (deviation : LocalChoice who ty)
    (round : ℕ) : ℝ :=
  localUtility who ty deviation (learningState round) -
    finiteExpect (learnedLaw who ty round) (fun current =>
      localUtility who ty current (learningState round))

theorem localVector_coordinate_eq_gain (who : Fin 2) (ty : Bool)
    (deviation : LocalChoice who ty) (round : ℕ) :
    (localCounterfactualRegretVector information
      (localStrategyOf who ty (learnedLaw who ty round)
        (learningState round))
      who (site who ty) (localPayoffOf who ty (learningState round)) 1
      (localRegretsIntegrable
        (localStrategyOf who ty (learnedLaw who ty round)
          (learningState round)) who ty)).ofLp
        deviation = localGain who ty deviation round := by
  rw [local_realization, regretPayoff_ofLp]
  rfl

def contingentGain (who : Fin 2) (deviation : ContingentChoice who)
    (round : ℕ) : ℝ :=
  ∑ ty : Bool, localGain who ty (deviation ty) round

/-- Both positive-probability sites of one player feed one D50 bound for every
complete contingent deviation; no sitewise convergence premise is smuggled in
at the strategic layer. -/
theorem contingentGain_positiveAverage_tendsto_zero (who : Fin 2) :
    ∀ deviation : ContingentChoice who,
      Tendsto
        (fun t => max
          ((∑ round ∈ Finset.range t, contingentGain who deviation round) /
            (t : ℝ)) 0)
        atTop (nhds 0) := by
  apply counterfactualRegretMatches_positiveRootGains_tendsto_zero
    information (fun _ : Bool => LearningState) who (site who)
    (fun ty => localStrategyOf who ty) (fun ty => localPayoffOf who ty)
    (fun _ => 1) (fun _ round => learningState round)
    (fun ty law current => localRegretsIntegrable
      (localStrategyOf who ty law current) who ty) (contingentGain who)
    (fun _ _ => 1) (fun _ _ => by exact ⟨by norm_num, by norm_num⟩)
    (fun deviation ty => deviation ty)
  · intro deviation round
    unfold contingentGain
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro ty _
    rw [one_mul]
    symm
    rw [show (fun currentRound => learningState currentRound) =
      scheduleEnvironment who ty from rfl]
    exact localVector_coordinate_eq_gain who ty (deviation ty) round
  · intro ty
    exact local_approaches who ty

theorem contingentLaw_marginal (who : Fin 2) (ty : Bool) (round : ℕ) :
    (contingentLaw who round).map (fun choices => choices ty) =
      learnedLaw who ty round := by
  unfold contingentLaw
  exact independentProduct_map_eval _ ty

theorem expectedPayoff_pureRow_eq_sum_localUtility
    (row : ContingentChoice 0) (round : ℕ) :
    MatrixGame.expectedPayoffOfFinite matrixPayoff (PMF.pure row)
        (contingentLaw 1 round) =
      ∑ ty : Bool, localUtility 0 ty (row ty) (learningState round) := by
  unfold MatrixGame.expectedPayoffOfFinite
  rw [MatrixGame.expectedPayoff_pure_row matrixPayoff row
    (contingentLaw 1 round) (payoffIntegrable_of_finite _ _)]
  unfold matrixPayoff
  rw [expect_add (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _),
    expect_const_mul (payoffIntegrable_of_finite _ _),
    expect_const_mul (payoffIntegrable_of_finite _ _),
    Fintype.sum_bool, localUtility_row_eq, localUtility_row_eq,
    ← learnedLaw_eq_current, ← learnedLaw_eq_current]
  unfold finiteExpect
  rw [← contingentLaw_marginal 1 false round,
    ← contingentLaw_marginal 1 true round,
    expect_map _ _ _ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _),
    expect_map _ _ _ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)]
  dsimp only [Function.comp_def, actionPlan]
  ring

theorem expectedPayoff_pureColumn_eq_neg_sum_localUtility
    (col : ContingentChoice 1) (round : ℕ) :
    MatrixGame.expectedPayoffOfFinite matrixPayoff (contingentLaw 0 round)
        (PMF.pure col) =
      -(∑ ty : Bool, localUtility 1 ty (col ty) (learningState round)) := by
  unfold MatrixGame.expectedPayoffOfFinite
  rw [MatrixGame.expectedPayoff_pure_column matrixPayoff
    (contingentLaw 0 round) col (payoffIntegrable_of_finite _ _)]
  unfold matrixPayoff
  rw [expect_add (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _),
    expect_const_mul (payoffIntegrable_of_finite _ _),
    expect_const_mul (payoffIntegrable_of_finite _ _),
    Fintype.sum_bool, localUtility_column_eq, localUtility_column_eq,
    ← learnedLaw_eq_current, ← learnedLaw_eq_current]
  unfold finiteExpect
  rw [← contingentLaw_marginal 0 false round,
    ← contingentLaw_marginal 0 true round,
    expect_map _ _ _ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _),
    expect_map _ _ _ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)]
  dsimp only [Function.comp_def, actionPlan]
  ring_nf

theorem expectedPayoff_current_eq_sum_expectedLocalUtility (round : ℕ) :
    MatrixGame.expectedPayoffOfFinite matrixPayoff
        (contingentLaw 0 round) (contingentLaw 1 round) =
      ∑ ty : Bool, finiteExpect (learnedLaw 0 ty round) (fun current =>
        localUtility 0 ty current (learningState round)) := by
  unfold MatrixGame.expectedPayoffOfFinite
  obtain ⟨houter, hrows⟩ := MatrixGame.expectedPayoff_eq_expect_rows
    matrixPayoff (contingentLaw 0 round) (contingentLaw 1 round)
      (payoffIntegrable_of_finite _ _)
      (fun _ => payoffIntegrable_of_finite _ _)
  rw [hrows]
  have hpure (current : ContingentChoice 0) :
      expect (contingentLaw 1 round) (matrixPayoff current)
          (payoffIntegrable_of_finite _ _) =
        ∑ ty : Bool, localUtility 0 ty (current ty)
          (learningState round) := by
    have h := expectedPayoff_pureRow_eq_sum_localUtility current round
    unfold MatrixGame.expectedPayoffOfFinite at h
    rw [MatrixGame.expectedPayoff_pure_row matrixPayoff current
      (contingentLaw 1 round) (payoffIntegrable_of_finite _ _)] at h
    exact h
  simp_rw [hpure]
  simp_rw [Fintype.sum_bool]
  rw [expect_add (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)]
  unfold finiteExpect
  rw [← contingentLaw_marginal 0 false round,
    ← contingentLaw_marginal 0 true round,
    expect_map _ _ _ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _),
    expect_map _ _ _ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)]
  dsimp only [Function.comp_def]

def mixedRoundProfile (round : ℕ) :
    Profile (MatrixGame.form (ContingentChoice 0) (ContingentChoice 1)).sig.mixed :=
  MatrixGame.mixedProfile (contingentLaw 0 round) (contingentLaw 1 round)

def roundLaw (round : ℕ) :
    PMF (Profile
      (MatrixGame.form (ContingentChoice 0) (ContingentChoice 1)).sig) :=
  independentProduct (mixedRoundProfile round)

/-- The contingent matrix has finite carriers, so both actual regret laws
admit the required payoff integrations. -/
noncomputable def matrixRegret
    (law : PMF (Profile (MatrixGame.utilityGame matrixPayoff).form.sig))
    (who : Fin 2)
    (replacement :
      (MatrixGame.utilityGame matrixPayoff).form.sig.Strategy who) : ℝ :=
  (MatrixGame.utilityGame matrixPayoff).externalRegret law who replacement
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)

theorem matrixRegret_pi
    (mixed : Profile (MatrixGame.utilityGame matrixPayoff).form.sig.mixed)
    (who : Fin 2)
    (replacement :
      (MatrixGame.utilityGame matrixPayoff).form.sig.Strategy who) :
    matrixRegret (independentProduct mixed) who replacement =
      expectedUtility (MatrixGame.utilityGame matrixPayoff).utility who
          ((MatrixGame.utilityGame matrixPayoff).form.mixed.play
            (Profile.update mixed who (PMF.pure replacement)))
          (payoffIntegrable_of_finite _ _) -
        expectedUtility (MatrixGame.utilityGame matrixPayoff).utility who
          ((MatrixGame.utilityGame matrixPayoff).form.mixed.play mixed)
          (payoffIntegrable_of_finite _ _) := by
  simpa only [matrixRegret] using
    (MatrixGame.utilityGame matrixPayoff).externalRegret_pi
      mixed who replacement
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)

theorem rowExternalRegret_roundLaw_eq_contingentGain
    (row : ContingentChoice 0) (round : ℕ) :
    matrixRegret
        (roundLaw round) 0 row = contingentGain 0 row round := by
  rw [roundLaw, matrixRegret_pi]
  unfold mixedRoundProfile
  rw [MatrixGame.mixedProfile_update_zero,
    MatrixGame.expectedUtility_zero_mixedProfile,
    MatrixGame.expectedUtility_zero_mixedProfile]
  calc
    _ = (∑ ty : Bool,
          localUtility 0 ty (row ty) (learningState round)) -
        (∑ ty : Bool, finiteExpect (learnedLaw 0 ty round) (fun current =>
          localUtility 0 ty current (learningState round))) :=
      congrArg₂ (fun first second : ℝ => first - second)
        (expectedPayoff_pureRow_eq_sum_localUtility row round)
        (expectedPayoff_current_eq_sum_expectedLocalUtility round)
    _ = _ := by
      unfold contingentGain localGain
      rw [Finset.sum_sub_distrib]

theorem columnExternalRegret_roundLaw_eq_contingentGain
    (col : ContingentChoice 1) (round : ℕ) :
    matrixRegret
        (roundLaw round) 1 col = contingentGain 1 col round := by
  rw [roundLaw, matrixRegret_pi]
  unfold mixedRoundProfile
  rw [MatrixGame.mixedProfile_update_one,
    MatrixGame.expectedUtility_one_mixedProfile matrixPayoff
      (contingentLaw 0 round) (PMF.pure col)
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    MatrixGame.expectedUtility_one_mixedProfile matrixPayoff
      (contingentLaw 0 round) (contingentLaw 1 round)
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
  calc
    _ = -(-(∑ ty : Bool,
          localUtility 1 ty (col ty) (learningState round))) -
        -(MatrixGame.expectedPayoffOfFinite matrixPayoff
          (contingentLaw 0 round) (contingentLaw 1 round)) :=
      congrArg₂ (fun first second : ℝ => -first - -second)
        (expectedPayoff_pureColumn_eq_neg_sum_localUtility col round) rfl
    _ = (∑ ty : Bool,
          localUtility 1 ty (col ty) (learningState round)) -
        (∑ ty : Bool, finiteExpect (learnedLaw 1 ty round) (fun current =>
          localUtility 1 ty current (learningState round))) := by
      have hzeroSumCurrent :
          MatrixGame.expectedPayoffOfFinite matrixPayoff
              (contingentLaw 0 round) (contingentLaw 1 round) =
            -(∑ ty : Bool, finiteExpect (learnedLaw 1 ty round) (fun current =>
              localUtility 1 ty current (learningState round))) := by
        unfold MatrixGame.expectedPayoffOfFinite
        obtain ⟨houter, hcols⟩ := MatrixGame.expectedPayoff_eq_expect_columns
          matrixPayoff (contingentLaw 0 round) (contingentLaw 1 round)
            (payoffIntegrable_of_finite _ _)
            (fun _ => payoffIntegrable_of_finite _ _)
        rw [hcols]
        have hpure (current : ContingentChoice 1) :
            expect (contingentLaw 0 round)
                (fun currentRow => matrixPayoff currentRow current)
                (payoffIntegrable_of_finite _ _) =
              -(∑ ty : Bool, localUtility 1 ty (current ty)
                (learningState round)) := by
          have h := expectedPayoff_pureColumn_eq_neg_sum_localUtility
            current round
          unfold MatrixGame.expectedPayoffOfFinite at h
          rw [MatrixGame.expectedPayoff_pure_column matrixPayoff
            (contingentLaw 0 round) current
            (payoffIntegrable_of_finite _ _)] at h
          exact h
        simp_rw [hpure, Fintype.sum_bool]
        rw [expect_neg (payoffIntegrable_of_finite _ _),
          expect_add (payoffIntegrable_of_finite _ _)
            (payoffIntegrable_of_finite _ _)]
        unfold finiteExpect
        rw [← contingentLaw_marginal 1 false round,
          ← contingentLaw_marginal 1 true round,
          expect_map _ _ _ (payoffIntegrable_of_finite _ _)
            (payoffIntegrable_of_finite _ _),
          expect_map _ _ _ (payoffIntegrable_of_finite _ _)
            (payoffIntegrable_of_finite _ _)]
        dsimp only [Function.comp_def]
      rw [hzeroSumCurrent]
      ring
    _ = _ := by
      unfold contingentGain localGain
      rw [Finset.sum_sub_distrib]

def finRoundLaw {T : ℕ} (round : Fin T) :
    PMF (Profile
      (MatrixGame.form (ContingentChoice 0) (ContingentChoice 1)).sig) :=
  roundLaw round

def averageLaw (t : ℕ) :
    PMF (Profile
      (MatrixGame.form (ContingentChoice 0) (ContingentChoice 1)).sig) :=
  (MatrixGame.form (ContingentChoice 0) (ContingentChoice 1)).timeAverage
    (finRoundLaw (T := t + 1))

theorem matrixRegret_timeAverage (t : ℕ) (who : Fin 2)
    (replacement :
      (MatrixGame.utilityGame matrixPayoff).form.sig.Strategy who) :
    matrixRegret (averageLaw t) who replacement =
      (∑ round : Fin (t + 1),
        matrixRegret (roundLaw round) who replacement) / (t + 1) := by
  unfold matrixRegret averageLaw
  simpa only [finRoundLaw, Nat.cast_add, Nat.cast_one] using
    (MatrixGame.utilityGame matrixPayoff).externalRegret_timeAverage
      (finRoundLaw (T := t + 1)) who replacement
      (fun _ => payoffIntegrable_of_finite _ _)
      (fun _ => payoffIntegrable_of_finite _ _)

theorem rowExternalRegret_average_tendsto_zero (row : ContingentChoice 0) :
    Tendsto
      (fun t => max
        (matrixRegret
          (averageLaw t) 0 row) 0)
      atTop (nhds 0) := by
  have hshift := (contingentGain_positiveAverage_tendsto_zero 0 row).comp
    (tendsto_add_atTop_nat 1)
  apply hshift.congr
  intro t
  apply congrArg (fun value : ℝ => max value 0)
  rw [matrixRegret_timeAverage]
  have hsum :
      (∑ round : Fin (t + 1),
        matrixRegret
          (roundLaw round) 0 row) =
        ∑ round : Fin (t + 1), contingentGain 0 row round := by
    apply Finset.sum_congr rfl
    intro round _
    exact rowExternalRegret_roundLaw_eq_contingentGain row round
  rw [hsum]
  rw [Fin.sum_univ_eq_sum_range
    (fun round => contingentGain 0 row round) (t + 1)]
  simp only [Nat.cast_add, Nat.cast_one]

theorem columnExternalRegret_average_tendsto_zero (col : ContingentChoice 1) :
    Tendsto
      (fun t => max
        (matrixRegret
          (averageLaw t) 1 col) 0)
      atTop (nhds 0) := by
  have hshift := (contingentGain_positiveAverage_tendsto_zero 1 col).comp
    (tendsto_add_atTop_nat 1)
  apply hshift.congr
  intro t
  apply congrArg (fun value : ℝ => max value 0)
  rw [matrixRegret_timeAverage]
  have hsum :
      (∑ round : Fin (t + 1),
        matrixRegret
          (roundLaw round) 1 col) =
        ∑ round : Fin (t + 1), contingentGain 1 col round := by
    apply Finset.sum_congr rfl
    intro round _
    exact columnExternalRegret_roundLaw_eq_contingentGain col round
  rw [hsum]
  rw [Fin.sum_univ_eq_sum_range
    (fun round => contingentGain 1 col round) (t + 1)]
  simp only [Nat.cast_add, Nat.cast_one]

def rowRegretBound (t : ℕ) : ℝ :=
  ∑ row : ContingentChoice 0,
    max (matrixRegret
      (averageLaw t) 0 row) 0

def columnRegretBound (t : ℕ) : ℝ :=
  ∑ col : ContingentChoice 1,
    max (matrixRegret
      (averageLaw t) 1 col) 0

theorem rowRegretBound_tendsto_zero :
    Tendsto rowRegretBound atTop (nhds 0) := by
  unfold rowRegretBound
  simpa using tendsto_finsetSum Finset.univ (fun row _ =>
    rowExternalRegret_average_tendsto_zero row)

theorem columnRegretBound_tendsto_zero :
    Tendsto columnRegretBound atTop (nhds 0) := by
  unfold columnRegretBound
  simpa using tendsto_finsetSum Finset.univ (fun col _ =>
    columnExternalRegret_average_tendsto_zero col)

theorem externalRegret_le_rowRegretBound (t : ℕ)
    (row : ContingentChoice 0) :
    matrixRegret
        (averageLaw t) 0 row ≤ rowRegretBound t := by
  apply le_trans (le_max_left _ 0)
  exact Finset.single_le_sum
    (fun current _ => le_max_right _ _) (Finset.mem_univ row)

theorem externalRegret_le_columnRegretBound (t : ℕ)
    (col : ContingentChoice 1) :
    matrixRegret
        (averageLaw t) 1 col ≤ columnRegretBound t := by
  apply le_trans (le_max_left _ 0)
  exact Finset.single_le_sum
    (fun current _ => le_max_right _ _) (Finset.mem_univ col)

/-- The same four Protocol learners induce one empirical law over complete
Bayesian plans. D50 controls both players' strategic deviations, and D51 turns
those bounds into the canonical approximate mixed Nash certificate. -/
theorem empiricalMarginals_isεNash (t : ℕ) :
    IsεNash
      (MatrixGame.form (ContingentChoice 0) (ContingentChoice 1)).mixed
      (MatrixGame.utility matrixPayoff)
      (rowRegretBound t + columnRegretBound t)
      (MatrixGame.mixedProfile
        (MatrixGame.rowMarginal (averageLaw t))
        (MatrixGame.columnMarginal (averageLaw t))) :=
  MatrixGame.marginalProfile_isεNash_of_externalRegret_le
    matrixPayoff (averageLaw t)
      (payoffIntegrable_of_finite _ _)
      (fun _ => payoffIntegrable_of_finite _ _)
      (fun _ => payoffIntegrable_of_finite _ _)
      (externalRegret_le_rowRegretBound t)
      (externalRegret_le_columnRegretBound t)
      (fun _ => payoffIntegrable_of_finite _ _)
      (fun _ => payoffIntegrable_of_finite _ _)

theorem empiricalNashTolerance_tendsto_zero :
    Tendsto (fun t => rowRegretBound t + columnRegretBound t)
      atTop (nhds 0) := by
  simpa using rowRegretBound_tendsto_zero.add
    columnRegretBound_tendsto_zero

def fallbackChoice (who : Fin 2) (ty : Bool) : LocalChoice who ty :=
  Classical.choice (choiceNonempty who ty)

def fallbackAction (who : Fin 2) (ty : Bool) : Bool :=
  actionOfChoice who ty (fallbackChoice who ty)

def improvingRowChoice (ty : Bool) : LocalChoice 0 ty :=
  choiceOfAction 0 ty (fallbackAction 1 ty)

def improvingColumnChoice (ty : Bool) : LocalChoice 1 ty :=
  choiceOfAction 1 ty (!(fallbackAction 0 ty))

theorem fallbackChoice_eq_choiceOfAction (who : Fin 2) (ty : Bool) :
    fallbackChoice who ty = choiceOfAction who ty (fallbackAction who ty) := by
  apply Subtype.ext
  exact choice_eq_some_actionOfChoice who ty (fallbackChoice who ty)

theorem learnedLaw_zero (who : Fin 2) (ty : Bool) :
    learnedLaw who ty 0 = PMF.pure (fallbackChoice who ty) := by
  simp [learnedLaw, localAverage, counterfactualRegretMatchAverage,
    avgVec, regretMatch, fallbackChoice]

theorem initial_type_saddleGain_eq_one (ty : Bool) :
    localGain 0 ty (improvingRowChoice ty) 0 +
      localGain 1 ty (improvingColumnChoice ty) 0 = 1 := by
  unfold localGain
  rw [learnedLaw_zero, learnedLaw_zero]
  simp only [finiteExpect, expect_pure]
  rw [localUtility_row_eq, localUtility_row_eq,
    localUtility_column_eq, localUtility_column_eq]
  rw [← learnedLaw_eq_current, ← learnedLaw_eq_current,
    learnedLaw_zero, learnedLaw_zero]
  simp only [finiteExpect, expect_pure]
  rw [fallbackChoice_eq_choiceOfAction, fallbackChoice_eq_choiceOfAction]
  simp [improvingRowChoice, improvingColumnChoice, fallbackAction,
    stagePayoff]
  rw [show actionOfChoice 0 ty (fallbackChoice 0 ty) =
      fallbackAction 0 ty from rfl,
    show actionOfChoice 1 ty (fallbackChoice 1 ty) =
      fallbackAction 1 ty from rfl]
  cases hrow : fallbackAction 0 ty <;>
    cases hcol : fallbackAction 1 ty <;>
      norm_num [stagePayoff, hrow, hcol]

def improvingRowPlan : ContingentChoice 0 := improvingRowChoice

def improvingColumnPlan : ContingentChoice 1 := improvingColumnChoice

/-- Both type branches matter at round zero: their exact strategic saddle
gaps add to two. The four local laws therefore cannot all remain at their
arbitrary fallback point masses. -/
theorem initial_saddleGap_eq_two :
    MatrixGame.expectedPayoffOfFinite matrixPayoff
          (PMF.pure improvingRowPlan)
          (MatrixGame.columnMarginal (roundLaw 0)) -
        MatrixGame.expectedPayoffOfFinite matrixPayoff
          (MatrixGame.rowMarginal (roundLaw 0))
          (PMF.pure improvingColumnPlan) = 2 := by
  have hgap := MatrixGame.saddleGap_eq_externalRegret_add
    matrixPayoff (roundLaw 0) improvingRowPlan improvingColumnPlan
      (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
  rw [hgap]
  show matrixRegret (roundLaw 0) 0 improvingRowPlan +
    matrixRegret (roundLaw 0) 1 improvingColumnPlan = 2
  rw [rowExternalRegret_roundLaw_eq_contingentGain,
    columnExternalRegret_roundLaw_eq_contingentGain]
  unfold contingentGain improvingRowPlan improvingColumnPlan
  rw [Fintype.sum_bool, Fintype.sum_bool]
  rw [add_add_add_comm]
  rw [initial_type_saddleGain_eq_one, initial_type_saddleGain_eq_one]
  norm_num

theorem localAverage_one_coordinate_eq_gain (who : Fin 2) (ty : Bool)
    (deviation : LocalChoice who ty) :
    (localAverage who ty 1).ofLp deviation =
      localGain who ty deviation 0 := by
  unfold localAverage counterfactualRegretMatchAverage
  simp only [avgVec]
  norm_num
  simpa [learnedLaw, localAverage, counterfactualRegretMatchAverage,
    avgVec, scheduleEnvironment] using
      localVector_coordinate_eq_gain who ty deviation 0

theorem learnedLaw_one_prob_pos_of_gain_pos (who : Fin 2) (ty : Bool)
    (deviation : LocalChoice who ty)
    (hgain : 0 < localGain who ty deviation 0) :
    0 < learnedLaw who ty 1 deviation := by
  have hcoordinate : 0 < (localAverage who ty 1).ofLp deviation := by
    rw [localAverage_one_coordinate_eq_gain]
    exact hgain
  have hsum : 0 < ∑ choice,
      max ((localAverage who ty 1).ofLp choice) 0 := by
    have hle : max ((localAverage who ty 1).ofLp deviation) 0 ≤
        ∑ choice, max ((localAverage who ty 1).ofLp choice) 0 :=
      Finset.single_le_sum (fun current _ => le_max_right _ 0)
        (Finset.mem_univ deviation)
    rw [max_eq_left hcoordinate.le] at hle
    exact lt_of_lt_of_le hcoordinate hle
  rw [learnedLaw, regretMatch, dite_eq_left hsum, PMF.ofFintype_apply]
  apply ENNReal.ofReal_pos.mpr
  exact div_pos (by rw [max_eq_left hcoordinate.le]; exact hcoordinate) hsum

theorem localGain_fallback_zero (who : Fin 2) (ty : Bool) :
    localGain who ty (fallbackChoice who ty) 0 = 0 := by
  unfold localGain
  rw [learnedLaw_zero]
  simp only [finiteExpect, expect_pure]
  ring

theorem learnedLaw_one_ne_zero_of_gain_pos (who : Fin 2) (ty : Bool)
    (deviation : LocalChoice who ty)
    (hgain : 0 < localGain who ty deviation 0) :
    learnedLaw who ty 1 ≠ learnedLaw who ty 0 := by
  have hne : deviation ≠ fallbackChoice who ty := by
    intro heq
    subst deviation
    rw [localGain_fallback_zero] at hgain
    exact (lt_irrefl 0) hgain
  intro hlaw
  have hprob := learnedLaw_one_prob_pos_of_gain_pos who ty deviation hgain
  rw [hlaw, learnedLaw_zero] at hprob
  simp [PMF.pure_apply, hne] at hprob

/-- At each positive-probability type, at least one player's next local law
leaves its arbitrary fallback. This is the hostile nonconstant-dynamics
control; it does not overclaim that matching pennies improves both players
against every possible pair of fallbacks. -/
theorem some_learnedLaw_moves_at_each_type (ty : Bool) :
    learnedLaw 0 ty 1 ≠ learnedLaw 0 ty 0 ∨
      learnedLaw 1 ty 1 ≠ learnedLaw 1 ty 0 := by
  have hsum := initial_type_saddleGain_eq_one ty
  have hpositive :
      0 < localGain 0 ty (improvingRowChoice ty) 0 ∨
        0 < localGain 1 ty (improvingColumnChoice ty) 0 := by
    by_contra hnot
    push Not at hnot
    linarith
  rcases hpositive with hrow | hcol
  · exact Or.inl (learnedLaw_one_ne_zero_of_gain_pos 0 ty _ hrow)
  · exact Or.inr (learnedLaw_one_ne_zero_of_gain_pos 1 ty _ hcol)

end GameTheory.Analysis.Protocol.BayesianZeroSumLearningTest
