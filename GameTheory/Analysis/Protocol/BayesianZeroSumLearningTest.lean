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

def fairBit : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

def typeProfile (ty : Bool) : Fin 2 → Bool := fun _ => ty

def commonPrior : FinDist (Fin 2 → Bool) :=
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
  apply FinDist.prob_pos_iff.mp
  cases ty <;> norm_num [fairBit, FinDist.prob_pure_eq_ite]

theorem mem_support_commonPrior (ty : Bool) :
    typeProfile ty ∈ commonPrior.support := by
  rw [commonPrior, FinDist.support_map]
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
  rw [FinDist.support_map]
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
      rw [FinDist.support_map]
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
      rw [FinDist.support_map] at hrealized
      obtain ⟨sourceTypes, hsource, heq⟩ := hrealized
      cases heq
      exact ⟨rfl, rfl, hsource⟩
  | typed priorTypes =>
      rw [FinDist.mem_support_pure] at realized
      cases realized
  | finished priorTypes priorActions =>
      exact False.elim (hlegal.1 trivial)

theorem mem_support_commonPrior_eq_typeProfile {types : Fin 2 → Bool}
    (hmem : types ∈ commonPrior.support) :
    ∃ ty, types = typeProfile ty := by
  rw [commonPrior, FinDist.support_map] at hmem
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

theorem terminalPayoff_zeroSum (history : execution.History) :
    terminalPayoff history 1 = -terminalPayoff history 0 := by
  rcases history with ⟨state, trace⟩
  cases state <;> simp [terminalPayoff]

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
  | .waiting => FinDist.pure ⟨none, by simp [Languages.Bayesian.menu]⟩
  | .acting ty => regretMatch (averageOfState state who ty)
  | .done => FinDist.pure ⟨none, by simp [Languages.Bayesian.menu]⟩

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
    (law : FinDist (LocalChoice who ty))
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

theorem local_realization (who : Fin 2) (ty : Bool)
    (law : FinDist (LocalChoice who ty)) (state : LearningState) :
    localCounterfactualRegretVector information
        (localStrategyOf who ty law state) who (site who ty)
          (localPayoffOf who ty state) 1 =
      regretPayoff (localUtility who ty) law state := by
  have h := information.localCounterfactualRegretVector_strategyWithLocalLaw
    information_actsOnce (strategyOfState state) who (site who ty)
      (site_allNonterminal who ty) law
      (fun history => terminalPayoff history who) 0 state
  calc
    _ = localCounterfactualRegretVector information
        (strategyWithLocalLaw information (strategyOfState state) who
          (site who ty) law)
        who (site who ty) (fun history => terminalPayoff history who) 1 := rfl
    _ = regretPayoff
        (fun choice (_current : LearningState) =>
          information.counterfactualActionUtility (strategyOfState state) who
            (site who ty) (fun history => terminalPayoff history who) 1 choice)
        law state := h
    _ = regretPayoff (localUtility who ty) law state := by
      ext choice
      rfl

def localAverage (who : Fin 2) (ty : Bool) (round : ℕ) :
    EuclideanSpace ℝ (LocalChoice who ty) :=
  counterfactualRegretMatchAverage information who (site who ty)
    (localStrategyOf who ty) (localPayoffOf who ty) 1
      (scheduleEnvironment who ty) round

theorem localAverage_succ (who : Fin 2) (ty : Bool) (round : ℕ) :
    localAverage who ty (round + 1) =
      ((round : ℝ) / ((round : ℝ) + 1)) • localAverage who ty round +
        (1 / ((round : ℝ) + 1)) •
          localCounterfactualRegretVector information
            (localStrategyOf who ty
              (regretMatch (localAverage who ty round)) (learningState round))
            who (site who ty) (fun history => terminalPayoff history who) 1 :=
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
    commonPrior.prob (typeProfile ty) = 1 / 2 := by
  rw [commonPrior,
    FinDist.prob_map_of_injective typeProfile typeProfile_injective]
  cases ty <;> norm_num [fairBit, FinDist.prob_pure_eq_ite]

theorem initial_step_prob_typed (ty : Bool) :
    (execution.step (.initial) ⟨execution.noop, initial_noop_legal⟩).prob
        (.typed (typeProfile ty)) = 1 / 2 := by
  show (commonPrior.map (Languages.Bayesian.State.typed (B := game))).prob
      (.typed (typeProfile ty)) = 1 / 2
  rw [FinDist.prob_map_of_injective]
  · exact commonPrior_prob_typeProfile ty
  · intro first second heq
    exact Languages.Bayesian.State.typed.inj heq

theorem initial_noop_choice_prob (state : LearningState) (other : Fin 2) :
    ((strategyOfState state other)
        (information.infoOf other ExecutionProtocol.Trace.start)).prob
      (choicesOfLegal information ExecutionProtocol.Trace.start
        ⟨execution.noop, initial_noop_legal⟩ other) = 1 := by
  simp [strategyOfState, policyOfState, choicesOfLegal,
    InfoSignals.infoOf, Languages.Bayesian.signals]
  rw [FinDist.prob_pure_eq_ite]
  split
  · rfl
  · rename_i hne
    exfalso
    apply hne
    apply Subtype.ext
    rfl

theorem opponentsStepProb_initial_noop (state : LearningState) (who : Fin 2) :
    opponentsStepProb information (strategyOfState state) who
        ExecutionProtocol.Trace.start
        ⟨execution.noop, initial_noop_legal⟩ = 1 := by
  classical
  unfold opponentsStepProb
  apply Finset.prod_eq_one
  intro other hother
  exact initial_noop_choice_prob state other

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
        (fun final => terminalPayoff final who) fuel history ∈
      Set.Icc (-1 : ℝ) 1 := by
  unfold InformationModel.behavioralContinuationValue
  constructor
  · have h := FinDist.expect_mono
      (μ := information.runBehavioralFrom
        (Profile.update (sig := information.behavioralSignature)
          strategy who alternative) fuel history)
      (u := fun _history : execution.History => (-1 : ℝ))
      (v := fun final => terminalPayoff final who)
      (fun final _ => (terminalPayoff_mem_Icc final who).1)
    simpa using h
  · exact FinDist.expect_le_of_forall
      (information.runBehavioralFrom
        (Profile.update (sig := information.behavioralSignature)
          strategy who alternative) fuel history)
      (fun final => terminalPayoff final who) 1
      (fun final _ => (terminalPayoff_mem_Icc final who).2)

theorem localUtility_mem_Icc (who : Fin 2) (ty : Bool)
    (choice : LocalChoice who ty) (state : LearningState) :
    localUtility who ty choice state ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
  unfold localUtility counterfactualActionUtility
    counterfactualContinuationValue
  rw [Fintype.sum_unique]
  rw [informationHistory_eq_typedHistory who ty
    (default : information.InformationHistory who (site who ty).1)]
  rw [counterfactualReach_typedHistory]
  have hcontinuation := behavioralContinuationValue_mem_Icc
    (strategyOfState state) who
      ((strategyOfState state who).commit (site who ty).1 choice) 1
      (typedHistory ty)
  constructor <;> nlinarith [hcontinuation.1, hcontinuation.2]

theorem local_regretPayoff_norm_le (who : Fin 2) (ty : Bool)
    (law : FinDist (LocalChoice who ty)) (state : LearningState) :
    ‖regretPayoff (localUtility who ty) law state‖ ≤
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
      (local_realization who ty) (bound := Fintype.card (LocalChoice who ty))
      (by positivity) (local_regretPayoff_norm_le who ty)
      (scheduleEnvironment who ty)

def learnedLaw (who : Fin 2) (ty : Bool) (round : ℕ) :
    FinDist (LocalChoice who ty) :=
  regretMatch (localAverage who ty round)

def currentLaw (state : LearningState) (who : Fin 2) (ty : Bool) :
    FinDist (LocalChoice who ty) :=
  regretMatch (averageOfState state who ty)

theorem localUtility_row_eq (ty : Bool) (choice : LocalChoice 0 ty)
    (state : LearningState) :
    localUtility 0 ty choice state =
      (1 / 2) * (currentLaw state 1 ty).expect (fun other =>
        stagePayoff (actionOfChoice 0 ty choice)
          (actionOfChoice 1 ty other)) := by
  cases ty
  ·
    unfold localUtility counterfactualActionUtility
      counterfactualContinuationValue
    rw [Fintype.sum_unique]
    rw [informationHistory_eq_typedHistory 0 false
      (default : information.InformationHistory 0 (site 0 false).1)]
    rw [counterfactualReach_typedHistory]
    have hinfo (player : Fin 2) :
        information.infoOf player (typedHistory false).trace =
          (show information.InfoState player from .acting false) := by
      rw [Languages.Bayesian.infoOf_eq_viewOfState]
      rfl
    unfold behavioralContinuationValue
    rw [information.runBehavioralFrom_succ_of_not_terminal _ 0]
    · rw [FinDist.expect_bind]
      unfold InformationModel.behavioralJoint
      unfold strategyOfState
      dsimp [InfoSignals.infoOf, Languages.Bayesian.signals,
        Languages.Bayesian.phaseOfState, Languages.Bayesian.privateSignal,
        typedHistory, typeProfile]
      rw [FinDist.expect_map, FinDist.pi_eq_map_product 0]
      rw [FinDist.expect_map]
      unfold FinDist.product
      rw [FinDist.expect_bind]
      have hmarginal :
          (FinDist.pi fun j : {j : Fin 2 // j ≠ 0} =>
              Profile.update (sig := information.behavioralSignature)
                (policyOfState state) 0
                ((policyOfState state 0).commit (.acting false) choice)
                j.1 (.acting false)).map
              (fun draws => draws ⟨1, by decide⟩) =
            currentLaw state 1 false := by
        rw [FinDist.map_apply_pi]
        simp [currentLaw, policyOfState, Profile.update_of_ne]
      simp [Profile.update_same, InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero, terminalPayoff,
        choice_eq_some_actionOfChoice]
      rw [← hmarginal, FinDist.expect_map]
    · simp [typedHistory]
  ·
    unfold localUtility counterfactualActionUtility
      counterfactualContinuationValue
    rw [Fintype.sum_unique]
    rw [informationHistory_eq_typedHistory 0 true
      (default : information.InformationHistory 0 (site 0 true).1)]
    rw [counterfactualReach_typedHistory]
    have hinfo (player : Fin 2) :
        information.infoOf player (typedHistory true).trace =
          (show information.InfoState player from .acting true) := by
      rw [Languages.Bayesian.infoOf_eq_viewOfState]
      rfl
    unfold behavioralContinuationValue
    rw [information.runBehavioralFrom_succ_of_not_terminal _ 0]
    · rw [FinDist.expect_bind]
      unfold InformationModel.behavioralJoint
      unfold strategyOfState
      dsimp [InfoSignals.infoOf, Languages.Bayesian.signals,
        Languages.Bayesian.phaseOfState, Languages.Bayesian.privateSignal,
        typedHistory, typeProfile]
      rw [FinDist.expect_map, FinDist.pi_eq_map_product 0]
      rw [FinDist.expect_map]
      unfold FinDist.product
      rw [FinDist.expect_bind]
      have hmarginal :
          (FinDist.pi fun j : {j : Fin 2 // j ≠ 0} =>
              Profile.update (sig := information.behavioralSignature)
                (policyOfState state) 0
                ((policyOfState state 0).commit (.acting true) choice)
                j.1 (.acting true)).map
              (fun draws => draws ⟨1, by decide⟩) =
            currentLaw state 1 true := by
        rw [FinDist.map_apply_pi]
        simp [currentLaw, policyOfState, Profile.update_of_ne]
      simp [Profile.update_same, InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero, terminalPayoff,
        choice_eq_some_actionOfChoice]
      rw [← hmarginal, FinDist.expect_map]
    · simp [typedHistory]

theorem localUtility_column_eq (ty : Bool) (choice : LocalChoice 1 ty)
    (state : LearningState) :
    localUtility 1 ty choice state =
      -(1 / 2) * (currentLaw state 0 ty).expect (fun other =>
        stagePayoff (actionOfChoice 0 ty other)
          (actionOfChoice 1 ty choice)) := by
  cases ty
  ·
    unfold localUtility counterfactualActionUtility
      counterfactualContinuationValue
    rw [Fintype.sum_unique]
    rw [informationHistory_eq_typedHistory 1 false
      (default : information.InformationHistory 1 (site 1 false).1)]
    rw [counterfactualReach_typedHistory]
    unfold behavioralContinuationValue
    rw [information.runBehavioralFrom_succ_of_not_terminal _ 0]
    · rw [FinDist.expect_bind]
      unfold InformationModel.behavioralJoint
      unfold strategyOfState
      dsimp [InfoSignals.infoOf, Languages.Bayesian.signals,
        Languages.Bayesian.phaseOfState, Languages.Bayesian.privateSignal,
        typedHistory, typeProfile]
      rw [FinDist.expect_map, FinDist.pi_eq_map_product 1]
      rw [FinDist.expect_map]
      unfold FinDist.product
      rw [FinDist.expect_bind]
      have hmarginal :
          (FinDist.pi fun j : {j : Fin 2 // j ≠ 1} =>
              Profile.update (sig := information.behavioralSignature)
                (policyOfState state) 1
                ((policyOfState state 1).commit (.acting false) choice)
                j.1 (.acting false)).map
              (fun draws => draws ⟨0, by decide⟩) =
            currentLaw state 0 false := by
        rw [FinDist.map_apply_pi]
        simp [currentLaw, policyOfState, Profile.update_of_ne]
      simp [Profile.update_same, InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero, terminalPayoff,
        choice_eq_some_actionOfChoice]
      rw [← hmarginal, FinDist.expect_map]
      let μ : FinDist ((j : {j : Fin 2 // j ≠ 1}) →
          LocalChoice j.1 false) :=
        FinDist.pi fun j =>
          Profile.update (sig := information.behavioralSignature)
            (policyOfState state) 1
            ((policyOfState state 1).commit (.acting false) choice)
            j.1 (.acting false)
      let f : ((j : {j : Fin 2 // j ≠ 1}) → LocalChoice j.1 false) → ℝ :=
        fun draws => stagePayoff
          (actionOfChoice 0 false (draws ⟨0, by decide⟩))
          (actionOfChoice 1 false choice)
      have hneg : μ.expect (fun draws => -f draws) = -μ.expect f := by
        calc
          _ = μ.expect (fun draws => (-1 : ℝ) * f draws) := by
            apply FinDist.expect_congr
            intro draws _
            ring
          _ = (-1 : ℝ) * μ.expect f := FinDist.expect_smul (-1) μ f
          _ = _ := by ring
      dsimp only [μ, f] at hneg
      rw [hneg]
      ring
    · simp [typedHistory]
  ·
    unfold localUtility counterfactualActionUtility
      counterfactualContinuationValue
    rw [Fintype.sum_unique]
    rw [informationHistory_eq_typedHistory 1 true
      (default : information.InformationHistory 1 (site 1 true).1)]
    rw [counterfactualReach_typedHistory]
    unfold behavioralContinuationValue
    rw [information.runBehavioralFrom_succ_of_not_terminal _ 0]
    · rw [FinDist.expect_bind]
      unfold InformationModel.behavioralJoint
      unfold strategyOfState
      dsimp [InfoSignals.infoOf, Languages.Bayesian.signals,
        Languages.Bayesian.phaseOfState, Languages.Bayesian.privateSignal,
        typedHistory, typeProfile]
      rw [FinDist.expect_map, FinDist.pi_eq_map_product 1]
      rw [FinDist.expect_map]
      unfold FinDist.product
      rw [FinDist.expect_bind]
      have hmarginal :
          (FinDist.pi fun j : {j : Fin 2 // j ≠ 1} =>
              Profile.update (sig := information.behavioralSignature)
                (policyOfState state) 1
                ((policyOfState state 1).commit (.acting true) choice)
                j.1 (.acting true)).map
              (fun draws => draws ⟨0, by decide⟩) =
            currentLaw state 0 true := by
        rw [FinDist.map_apply_pi]
        simp [currentLaw, policyOfState, Profile.update_of_ne]
      simp [Profile.update_same, InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero, terminalPayoff,
        choice_eq_some_actionOfChoice]
      rw [← hmarginal, FinDist.expect_map]
      let μ : FinDist ((j : {j : Fin 2 // j ≠ 1}) →
          LocalChoice j.1 true) :=
        FinDist.pi fun j =>
          Profile.update (sig := information.behavioralSignature)
            (policyOfState state) 1
            ((policyOfState state 1).commit (.acting true) choice)
            j.1 (.acting true)
      let f : ((j : {j : Fin 2 // j ≠ 1}) → LocalChoice j.1 true) → ℝ :=
        fun draws => stagePayoff
          (actionOfChoice 0 true (draws ⟨0, by decide⟩))
          (actionOfChoice 1 true choice)
      have hneg : μ.expect (fun draws => -f draws) = -μ.expect f := by
        calc
          _ = μ.expect (fun draws => (-1 : ℝ) * f draws) := by
            apply FinDist.expect_congr
            intro draws _
            ring
          _ = (-1 : ℝ) * μ.expect f := FinDist.expect_smul (-1) μ f
          _ = _ := by ring
      dsimp only [μ, f] at hneg
      rw [hneg]
      ring
    · simp [typedHistory]

theorem learnedLaw_eq_current (who : Fin 2) (ty : Bool) (round : ℕ) :
    learnedLaw who ty round =
      currentLaw (learningState round) who ty := by
  rw [learnedLaw, localAverage_eq_state]
  rfl

/-- A pure strategic deviation specifies one legal action at each of the
player's two positive-probability type sites. -/
abbrev ContingentChoice (who : Fin 2) :=
  (ty : Bool) → LocalChoice who ty

def contingentLaw (who : Fin 2) (round : ℕ) :
    FinDist (ContingentChoice who) :=
  FinDist.pi fun ty => learnedLaw who ty round

def actionPlan (who : Fin 2) (choices : ContingentChoice who) : Bool → Bool :=
  fun ty => actionOfChoice who ty (choices ty)

def planProfile (row : ContingentChoice 0) (col : ContingentChoice 1) :
    Profile game.signature
  | 0 => actionPlan 0 row
  | 1 => actionPlan 1 col

def matrixPayoff (row : ContingentChoice 0) (col : ContingentChoice 1) : ℝ :=
  (1 / 2) * stagePayoff (actionPlan 0 row false) (actionPlan 1 col false) +
    (1 / 2) * stagePayoff (actionPlan 0 row true) (actionPlan 1 col true)

/-- The matrix carrier is not a surrogate game: on every pair of complete
contingent choices, its payoff is the direct Bayesian game's ex-ante payoff. -/
theorem matrixPayoff_eq_direct_expectedUtility
    (row : ContingentChoice 0) (col : ContingentChoice 1) :
    matrixPayoff row col =
      expectedUtility game.utility 0
        (game.toForm.play (planProfile row col)) := by
  rw [BayesianGame.toForm_play, expectedUtility, FinDist.expect_map]
  unfold matrixPayoff
  simp only [game, BayesianGame.utility]
  unfold commonPrior fairBit
  rw [FinDist.expect_map]
  rw [FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure]
  simp [planProfile, BayesianGame.actionsOf, typeProfile, stagePayoff]
  ring_nf

def localGain (who : Fin 2) (ty : Bool) (deviation : LocalChoice who ty)
    (round : ℕ) : ℝ :=
  localUtility who ty deviation (learningState round) -
    (learnedLaw who ty round).expect fun current =>
      localUtility who ty current (learningState round)

theorem localVector_coordinate_eq_gain (who : Fin 2) (ty : Bool)
    (deviation : LocalChoice who ty) (round : ℕ) :
    (localCounterfactualRegretVector information
      (localStrategyOf who ty (learnedLaw who ty round)
        (learningState round))
      who (site who ty) (localPayoffOf who ty (learningState round)) 1).ofLp
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
    (fun _ => 1) (fun _ round => learningState round) (contingentGain who)
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
  rw [FinDist.map_apply_pi]

theorem expectedPayoff_pureRow_eq_sum_localUtility
    (row : ContingentChoice 0) (round : ℕ) :
    MatrixGame.expectedPayoff matrixPayoff (FinDist.pure row)
        (contingentLaw 1 round) =
      ∑ ty : Bool, localUtility 0 ty (row ty) (learningState round) := by
  rw [MatrixGame.expectedPayoff_pure_row]
  unfold matrixPayoff
  rw [FinDist.expect_add, FinDist.expect_smul, FinDist.expect_smul,
    Fintype.sum_bool, localUtility_row_eq, localUtility_row_eq,
    ← learnedLaw_eq_current, ← learnedLaw_eq_current]
  rw [← contingentLaw_marginal 1 false round,
    ← contingentLaw_marginal 1 true round,
    FinDist.expect_map, FinDist.expect_map]
  simp only [actionPlan]
  ring

theorem expectedPayoff_pureColumn_eq_neg_sum_localUtility
    (col : ContingentChoice 1) (round : ℕ) :
    MatrixGame.expectedPayoff matrixPayoff (contingentLaw 0 round)
        (FinDist.pure col) =
      -(∑ ty : Bool, localUtility 1 ty (col ty) (learningState round)) := by
  rw [MatrixGame.expectedPayoff_pure_column]
  unfold matrixPayoff
  rw [FinDist.expect_add, FinDist.expect_smul, FinDist.expect_smul,
    Fintype.sum_bool, localUtility_column_eq, localUtility_column_eq,
    ← learnedLaw_eq_current, ← learnedLaw_eq_current]
  rw [← contingentLaw_marginal 0 false round,
    ← contingentLaw_marginal 0 true round,
    FinDist.expect_map, FinDist.expect_map]
  simp only [actionPlan]
  ring_nf

theorem expectedPayoff_current_eq_sum_expectedLocalUtility (round : ℕ) :
    MatrixGame.expectedPayoff matrixPayoff
        (contingentLaw 0 round) (contingentLaw 1 round) =
      ∑ ty : Bool, (learnedLaw 0 ty round).expect fun current =>
        localUtility 0 ty current (learningState round) := by
  rw [MatrixGame.expectedPayoff_eq_expect_rows]
  simp_rw [expectedPayoff_pureRow_eq_sum_localUtility]
  simp_rw [Fintype.sum_bool]
  rw [FinDist.expect_add]
  rw [← contingentLaw_marginal 0 false round,
    ← contingentLaw_marginal 0 true round,
    FinDist.expect_map, FinDist.expect_map]

def mixedRoundProfile (round : ℕ) :
    Profile (MatrixGame.form (ContingentChoice 0) (ContingentChoice 1)).sig.mixed :=
  MatrixGame.mixedProfile (contingentLaw 0 round) (contingentLaw 1 round)

def roundLaw (round : ℕ) :
    FinDist (Profile
      (MatrixGame.form (ContingentChoice 0) (ContingentChoice 1)).sig) :=
  FinDist.pi (mixedRoundProfile round)

theorem rowExternalRegret_roundLaw_eq_contingentGain
    (row : ContingentChoice 0) (round : ℕ) :
    (MatrixGame.utilityGame matrixPayoff).externalRegret
        (roundLaw round) 0 row = contingentGain 0 row round := by
  rw [roundLaw, (MatrixGame.utilityGame matrixPayoff).externalRegret_pi]
  unfold mixedRoundProfile
  rw [MatrixGame.mixedProfile_update_zero,
    MatrixGame.expectedUtility_zero_mixedProfile,
    MatrixGame.expectedUtility_zero_mixedProfile]
  calc
    _ = (∑ ty : Bool,
          localUtility 0 ty (row ty) (learningState round)) -
        (∑ ty : Bool, (learnedLaw 0 ty round).expect fun current =>
          localUtility 0 ty current (learningState round)) :=
      congrArg₂ (fun first second : ℝ => first - second)
        (expectedPayoff_pureRow_eq_sum_localUtility row round)
        (expectedPayoff_current_eq_sum_expectedLocalUtility round)
    _ = _ := by
      unfold contingentGain localGain
      rw [Finset.sum_sub_distrib]

theorem columnExternalRegret_roundLaw_eq_contingentGain
    (col : ContingentChoice 1) (round : ℕ) :
    (MatrixGame.utilityGame matrixPayoff).externalRegret
        (roundLaw round) 1 col = contingentGain 1 col round := by
  rw [roundLaw, (MatrixGame.utilityGame matrixPayoff).externalRegret_pi]
  unfold mixedRoundProfile
  rw [MatrixGame.mixedProfile_update_one,
    MatrixGame.expectedUtility_one_mixedProfile,
    MatrixGame.expectedUtility_one_mixedProfile]
  calc
    _ = -(-(∑ ty : Bool,
          localUtility 1 ty (col ty) (learningState round))) -
        -(MatrixGame.expectedPayoff matrixPayoff
          (contingentLaw 0 round) (contingentLaw 1 round)) :=
      congrArg₂ (fun first second : ℝ => -first - -second)
        (expectedPayoff_pureColumn_eq_neg_sum_localUtility col round) rfl
    _ = (∑ ty : Bool,
          localUtility 1 ty (col ty) (learningState round)) -
        (∑ ty : Bool, (learnedLaw 1 ty round).expect fun current =>
          localUtility 1 ty current (learningState round)) := by
      have hzeroSumCurrent :
          MatrixGame.expectedPayoff matrixPayoff
              (contingentLaw 0 round) (contingentLaw 1 round) =
            -(∑ ty : Bool, (learnedLaw 1 ty round).expect fun current =>
              localUtility 1 ty current (learningState round)) := by
        rw [MatrixGame.expectedPayoff_eq_expect_columns]
        simp_rw [expectedPayoff_pureColumn_eq_neg_sum_localUtility]
        simp_rw [Fintype.sum_bool]
        calc
          _ = (contingentLaw 1 round).expect (fun current =>
              (-1 : ℝ) *
                (localUtility 1 true (current true) (learningState round) +
                  localUtility 1 false (current false)
                    (learningState round))) := by
            apply FinDist.expect_congr
            intro current _
            ring
          _ = (-1 : ℝ) * (contingentLaw 1 round).expect (fun current =>
                localUtility 1 true (current true) (learningState round) +
                  localUtility 1 false (current false)
                    (learningState round)) :=
            FinDist.expect_smul (-1) _ _
          _ = -((contingentLaw 1 round).expect (fun current =>
                localUtility 1 true (current true) (learningState round)) +
              (contingentLaw 1 round).expect (fun current =>
                localUtility 1 false (current false)
                  (learningState round))) := by
            rw [FinDist.expect_add]
            ring
          _ = _ := by
            rw [← contingentLaw_marginal 1 false round,
              ← contingentLaw_marginal 1 true round,
              FinDist.expect_map, FinDist.expect_map]
      rw [hzeroSumCurrent]
      ring
    _ = _ := by
      unfold contingentGain localGain
      rw [Finset.sum_sub_distrib]

def finRoundLaw {T : ℕ} (round : Fin T) :
    FinDist (Profile
      (MatrixGame.form (ContingentChoice 0) (ContingentChoice 1)).sig) :=
  roundLaw round

def averageLaw (t : ℕ) :
    FinDist (Profile
      (MatrixGame.form (ContingentChoice 0) (ContingentChoice 1)).sig) :=
  (MatrixGame.form (ContingentChoice 0) (ContingentChoice 1)).timeAverage
    (finRoundLaw (T := t + 1))

theorem rowExternalRegret_average_tendsto_zero (row : ContingentChoice 0) :
    Tendsto
      (fun t => max
        ((MatrixGame.utilityGame matrixPayoff).externalRegret
          (averageLaw t) 0 row) 0)
      atTop (nhds 0) := by
  have hshift := (contingentGain_positiveAverage_tendsto_zero 0 row).comp
    (tendsto_add_atTop_nat 1)
  apply hshift.congr
  intro t
  apply congrArg (fun value : ℝ => max value 0)
  rw [averageLaw,
    (MatrixGame.utilityGame matrixPayoff).externalRegret_timeAverage]
  simp only [finRoundLaw]
  have hsum :
      (∑ round : Fin (t + 1),
        (MatrixGame.utilityGame matrixPayoff).externalRegret
          (roundLaw round) 0 row) =
        ∑ round : Fin (t + 1), contingentGain 0 row round := by
    apply Finset.sum_congr rfl
    intro round _
    exact rowExternalRegret_roundLaw_eq_contingentGain row round
  rw [hsum]
  rw [Fin.sum_univ_eq_sum_range
    (fun round => contingentGain 0 row round) (t + 1)]

theorem columnExternalRegret_average_tendsto_zero (col : ContingentChoice 1) :
    Tendsto
      (fun t => max
        ((MatrixGame.utilityGame matrixPayoff).externalRegret
          (averageLaw t) 1 col) 0)
      atTop (nhds 0) := by
  have hshift := (contingentGain_positiveAverage_tendsto_zero 1 col).comp
    (tendsto_add_atTop_nat 1)
  apply hshift.congr
  intro t
  apply congrArg (fun value : ℝ => max value 0)
  rw [averageLaw,
    (MatrixGame.utilityGame matrixPayoff).externalRegret_timeAverage]
  simp only [finRoundLaw]
  have hsum :
      (∑ round : Fin (t + 1),
        (MatrixGame.utilityGame matrixPayoff).externalRegret
          (roundLaw round) 1 col) =
        ∑ round : Fin (t + 1), contingentGain 1 col round := by
    apply Finset.sum_congr rfl
    intro round _
    exact columnExternalRegret_roundLaw_eq_contingentGain col round
  rw [hsum]
  rw [Fin.sum_univ_eq_sum_range
    (fun round => contingentGain 1 col round) (t + 1)]

def rowRegretBound (t : ℕ) : ℝ :=
  ∑ row : ContingentChoice 0,
    max ((MatrixGame.utilityGame matrixPayoff).externalRegret
      (averageLaw t) 0 row) 0

def columnRegretBound (t : ℕ) : ℝ :=
  ∑ col : ContingentChoice 1,
    max ((MatrixGame.utilityGame matrixPayoff).externalRegret
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
    (MatrixGame.utilityGame matrixPayoff).externalRegret
        (averageLaw t) 0 row ≤ rowRegretBound t := by
  apply le_trans (le_max_left _ 0)
  exact Finset.single_le_sum
    (fun current _ => le_max_right _ _) (Finset.mem_univ row)

theorem externalRegret_le_columnRegretBound (t : ℕ)
    (col : ContingentChoice 1) :
    (MatrixGame.utilityGame matrixPayoff).externalRegret
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
      (externalRegret_le_rowRegretBound t)
      (externalRegret_le_columnRegretBound t)

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
    learnedLaw who ty 0 = FinDist.pure (fallbackChoice who ty) := by
  simp [learnedLaw, localAverage, counterfactualRegretMatchAverage,
    avgVec, regretMatch, fallbackChoice]

theorem initial_type_saddleGain_eq_one (ty : Bool) :
    localGain 0 ty (improvingRowChoice ty) 0 +
      localGain 1 ty (improvingColumnChoice ty) 0 = 1 := by
  unfold localGain
  rw [learnedLaw_zero, learnedLaw_zero,
    FinDist.expect_pure, FinDist.expect_pure]
  rw [localUtility_row_eq, localUtility_row_eq,
    localUtility_column_eq, localUtility_column_eq]
  rw [← learnedLaw_eq_current, ← learnedLaw_eq_current,
    learnedLaw_zero, learnedLaw_zero,
    FinDist.expect_pure, FinDist.expect_pure,
    FinDist.expect_pure, FinDist.expect_pure]
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
    MatrixGame.expectedPayoff matrixPayoff
          (FinDist.pure improvingRowPlan)
          (MatrixGame.columnMarginal (roundLaw 0)) -
        MatrixGame.expectedPayoff matrixPayoff
          (MatrixGame.rowMarginal (roundLaw 0))
          (FinDist.pure improvingColumnPlan) = 2 := by
  rw [MatrixGame.saddleGap_eq_externalRegret_add,
    rowExternalRegret_roundLaw_eq_contingentGain,
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
    0 < (learnedLaw who ty 1).prob deviation := by
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
  rw [learnedLaw, regretMatch, dif_pos hsum, FinDist.prob_ofWeights]
  exact div_pos (by rw [max_eq_left hcoordinate.le]; exact hcoordinate) hsum

theorem localGain_fallback_zero (who : Fin 2) (ty : Bool) :
    localGain who ty (fallbackChoice who ty) 0 = 0 := by
  unfold localGain
  rw [learnedLaw_zero, FinDist.expect_pure]
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
  rw [hlaw, learnedLaw_zero, FinDist.prob_pure_of_ne hne] at hprob
  exact (lt_irrefl 0) hprob

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
