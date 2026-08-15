/-
# EXP-060: two-round hidden-phase FOSG serialization

This hostile slice strengthens EXP-059 in two ways.  The source has genuinely
trace-sensitive information after distinct first-round joints merge to one
execution state, and its second round has a privately known inactive slot.
The serialized target must therefore retain and erase an actual canonical
source history; reconstructing one from an outcome or source state is not
sound for this fixture.
-/

import GameTheory.Languages.EFG
import GameTheory.Languages.FOSG

noncomputable section

namespace GameTheory.Experimental.FOSGToEFGTwoRound

open GameTheory.Languages GameTheory.Math.Probability GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol

theorem map_pi_bool {α : Bool → Type*}
    (laws : (index : Bool) → FinDist (α index)) :
    FinDist.map (fun draws => (draws false, draws true))
        (FinDist.pi laws) =
      FinDist.product (laws false) (laws true) := by
  classical
  apply FinDist.ext_of_prob
  intro pair
  let assignment : (index : Bool) → α index
    | false => pair.1
    | true => pair.2
  have hpair : (assignment false, assignment true) = pair := rfl
  rw [← hpair, FinDist.prob_map_of_injective]
  · rw [FinDist.prob_pi, FinDist.prob_product, Fintype.prod_bool]
    simp [mul_comm]
  · intro first second hequal
    funext index
    cases index with
    | false => exact congrArg Prod.fst hequal
    | true => exact congrArg Prod.snd hequal

def boolPairAssignment {α : Bool → Type*}
    (pair : α false × α true) : (index : Bool) → α index
  | false => pair.1
  | true => pair.2

theorem pi_bool_eq_map_product {α : Bool → Type*}
    (laws : (index : Bool) → FinDist (α index)) :
    FinDist.pi laws =
      FinDist.map boolPairAssignment
        (FinDist.product (laws false) (laws true)) := by
  classical
  apply FinDist.ext_of_prob
  intro assignment
  have hrebuild :
      boolPairAssignment (assignment false, assignment true) = assignment := by
    funext index
    cases index <;> rfl
  conv_rhs => rw [← hrebuild]
  rw [FinDist.prob_pi,
    FinDist.prob_map_of_injective boolPairAssignment (by
      intro first second hequal
      exact Prod.ext
        (congrFun hequal false) (congrFun hequal true)),
    FinDist.prob_product, Fintype.prod_bool]
  simp [mul_comm]

namespace Source

inductive State
  | start
  | round2 (publicBit hiddenActiveBit : Bool)
  | finished (publicBit hiddenActiveBit falseAction : Bool)
      (trueAction : Option Bool) (secondCoin : Bool)
  deriving DecidableEq

def terminal : State → Prop
  | .finished .. => True
  | _ => False

def coin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

def firstResolution : FinDist (Bool × Bool) :=
  FinDist.product coin coin

theorem mem_support_coin (value : Bool) : value ∈ coin.support := by
  refine FinDist.prob_pos_iff.mp ?_
  cases value <;> norm_num [coin, FinDist.prob_pure_eq_ite]

theorem mem_support_firstResolution (publicBit hiddenActiveBit : Bool) :
    (publicBit, hiddenActiveBit) ∈ firstResolution.support := by
  refine FinDist.prob_pos_iff.mp ?_
  unfold firstResolution
  rw [FinDist.prob_product]
  exact mul_pos
    (FinDist.prob_pos_iff.mpr (mem_support_coin publicBit))
    (FinDist.prob_pos_iff.mpr (mem_support_coin hiddenActiveBit))

def active : State → Bool → Prop
  | .start, _ => True
  | .round2 _ hiddenActiveBit, player => !player ∨ hiddenActiveBit = true
  | .finished .., _ => False

private def actionAt
    (state : State)
    (joint : Bool → Option Bool)
    (hlegal : IsLegalJoint (active state) (fun _ => Set.univ) joint)
    (player : Bool) (hactive : active state player) : Bool :=
  match hchoice : joint player with
  | some action => action
  | none => False.elim (by
      have hplayer := hlegal player
      rw [hchoice] at hplayer
      exact hplayer hactive)

@[reducible]
def execution : ExecutionProtocol Bool where
  State := State
  Action _ := Bool
  init := .start
  active := active
  available _ _ := Set.univ
  terminal := terminal
  step state joint :=
    match state with
    | .start =>
        FinDist.map (fun bits => State.round2 bits.1 bits.2)
          firstResolution
    | .round2 publicBit hiddenActiveBit =>
        let falseAction := actionAt (.round2 publicBit hiddenActiveBit)
          joint.1 joint.2.2 false (by simp [active])
        let trueAction := joint.1 true
        FinDist.map
          (State.finished publicBit hiddenActiveBit falseAction trueAction)
          coin
    | .finished .. => False.elim (joint.2.1 trivial)
  progress := by
    intro state hterm
    cases state with
    | start =>
        refine ⟨fun _ => some false, fun _ => ?_⟩
        exact ⟨trivial, Set.mem_univ _⟩
    | round2 publicBit hiddenActiveBit =>
        cases hiddenActiveBit with
        | false =>
            refine ⟨fun player => if player then none else some false,
              fun player => ?_⟩
            cases player <;> simp [active]
        | true =>
            refine ⟨fun _ => some false, fun player => ?_⟩
            cases player <;> simp [active]
    | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
        exact False.elim (hterm trivial)

def firstJoint (left right : Bool) : Bool → Option Bool :=
  fun player => some (if player then right else left)

def secondJoint (hiddenActiveBit falseAction trueAction : Bool) :
    Bool → Option Bool :=
  fun player => if player then
    if hiddenActiveBit then some trueAction else none
  else some falseAction

theorem firstJoint_legal (left right : Bool) :
    execution.Legal .start (firstJoint left right) := by
  refine ⟨by simp [terminal], fun player => ?_⟩
  cases player <;> simp [firstJoint, active]

theorem secondJoint_legal (publicBit hiddenActiveBit falseAction trueAction : Bool) :
    execution.Legal (.round2 publicBit hiddenActiveBit)
      (secondJoint hiddenActiveBit falseAction trueAction) := by
  refine ⟨by simp [terminal], fun player => ?_⟩
  cases player <;> cases hiddenActiveBit <;>
    simp [secondJoint, active]

def round2History (left right publicBit hiddenActiveBit : Bool) :
    execution.History :=
  ⟨.round2 publicBit hiddenActiveBit,
    .extend .start (firstJoint left right) (firstJoint_legal left right) (by
      simpa [execution] using
        mem_support_firstResolution publicBit hiddenActiveBit)⟩

def finishedHistory (left right publicBit hiddenActiveBit falseAction
    trueAction secondCoin : Bool) : execution.History :=
  let prior := round2History left right publicBit hiddenActiveBit
  let joint := secondJoint hiddenActiveBit falseAction trueAction
  ⟨.finished publicBit hiddenActiveBit falseAction (joint true) secondCoin,
    .extend prior.trace joint
      (secondJoint_legal publicBit hiddenActiveBit falseAction trueAction) (by
        show State.finished publicBit hiddenActiveBit falseAction
            (joint true) secondCoin ∈
          (FinDist.map
            (State.finished publicBit hiddenActiveBit
              (actionAt (.round2 publicBit hiddenActiveBit) joint
                (secondJoint_legal publicBit hiddenActiveBit falseAction trueAction).2
                false (by simp [active]))
              (joint true)) coin).support
        have hfalse : actionAt (.round2 publicBit hiddenActiveBit) joint
            (secondJoint_legal publicBit hiddenActiveBit falseAction trueAction).2
            false (by simp [active]) = falseAction := by
          rfl
        rw [hfalse, FinDist.support_map]
        exact ⟨secondCoin, mem_support_coin secondCoin, rfl⟩)⟩

inductive PublicSignal
  | initial
  | firstResolved (publicBit : Bool)
  | secondResolved (secondCoin : Bool)
  deriving DecidableEq

inductive PrivateSignal
  | initial
  | firstResolved (opponentAction : Bool) (hiddenActiveBit : Option Bool)
  | secondResolved (opponentAction : Option Bool)
  deriving DecidableEq

inductive View
  | round1
  | round2 (publicBit opponentAction : Bool)
      (hiddenActiveBit : Option Bool) (ownAction : Bool)
  | done (publicBit opponentAction : Bool)
      (hiddenActiveBit : Option Bool) (ownFirstAction secondCoin : Bool)
      (opponentSecondAction ownSecondAction : Option Bool)
  deriving DecidableEq

def publicOfTransition (target : State) : PublicSignal :=
  match target with
  | .start => .initial
  | .round2 publicBit _ => .firstResolved publicBit
  | .finished _ _ _ _ secondCoin => .secondResolved secondCoin

def privateOfTransition (player : Bool) (joint : Bool → Option Bool)
    (target : State) : PrivateSignal :=
  match target with
  | .start => .initial
  | .round2 _ hiddenActiveBit =>
      .firstResolved ((joint (!player)).getD false)
        (if player then some hiddenActiveBit else none)
  | .finished .. => .secondResolved (joint (!player))

def pushView (prior : View) (ownAction : Option Bool)
    (privateSignal : PrivateSignal) (publicSignal : PublicSignal) : View :=
  match prior, ownAction, privateSignal, publicSignal with
  | .round1, some own, .firstResolved opponent hidden,
      .firstResolved publicBit =>
      .round2 publicBit opponent hidden own
  | .round2 publicBit opponent hidden ownFirst, ownSecond,
      .secondResolved opponentSecond, .secondResolved secondCoin =>
      .done publicBit opponent hidden ownFirst secondCoin opponentSecond ownSecond
  | view, _, _, _ => view

@[reducible]
def signals : InfoSignals execution where
  PublicSignal := PublicSignal
  PrivateSignal _ := PrivateSignal
  initialPublic := .initial
  initialPrivate _ := .initial
  publicSignal event := publicOfTransition event.target
  privateSignal player event :=
    privateOfTransition player event.joint event.target
  InfoState _ := View
  initInfo _ _ _ := .round1
  pushInfo _ := pushView

def menu (player : Bool) : View → Set (Option Bool)
  | .round1 => Set.range some
  | .round2 _ _ hiddenActiveBit _ =>
      if !player ∨ hiddenActiveBit = some true then Set.range some else {none}
  | .done .. => {none}

def ViewMatches (player : Bool) : State → View → Prop
  | .start, .round1 => True
  | .round2 publicBit hiddenActiveBit,
      .round2 seenPublic _ seenHidden _ =>
      seenPublic = publicBit ∧
        seenHidden = if player then some hiddenActiveBit else none
  | .finished .., .done .. => True
  | _, _ => False

theorem infoOf_matches (player : Bool) :
    ∀ {state : State} (trace : execution.Trace state),
      ViewMatches player state (signals.infoOf player trace)
  | _, .start => by simp [signals, ViewMatches]
  | target, .extend (source := source) prior joint isLegal realized => by
      have hprior := infoOf_matches player prior
      cases source with
      | start =>
          cases target with
          | start => simp [execution] at realized
          | round2 publicBit hiddenActiveBit =>
              have hchoice := isLegal.2 player
              cases hplayer : joint player with
              | none =>
                  rw [hplayer] at hchoice
                  exact False.elim (hchoice trivial)
              | some ownAction =>
                  cases hinfo : signals.infoOf player prior <;>
                    simp [ViewMatches, hinfo] at hprior
                  rw [InfoSignals.infoOf_extend, hinfo]
                  simp [pushView, publicOfTransition,
                    privateOfTransition, ViewMatches, hplayer]
          | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
              simp [execution] at realized
      | round2 priorPublic priorHidden =>
          cases target with
          | start => simp [execution] at realized
          | round2 publicBit hiddenActiveBit => simp [execution] at realized
          | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
              cases hinfo : signals.infoOf player prior <;>
                simp [ViewMatches, hinfo] at hprior
              rw [InfoSignals.infoOf_extend, hinfo]
              simp [pushView, publicOfTransition,
                privateOfTransition, ViewMatches]
      | finished priorPublic priorHidden priorFalse priorTrue priorCoin =>
          exact False.elim (isLegal.1 trivial)

theorem menu_adequate (player : Bool) {state : State}
    (trace : execution.Trace state) (choice : Option Bool) :
    choice ∈ menu player (signals.infoOf player trace) ↔
      LegalOption execution state player choice := by
  have hmatches := infoOf_matches player trace
  generalize hview : signals.infoOf player trace = view at hmatches ⊢
  cases state with
  | start =>
      cases view <;> simp [ViewMatches] at hmatches
      cases choice <;> simp [menu, LegalOption, active]
  | round2 publicBit hiddenActiveBit =>
      cases view <;> simp [ViewMatches] at hmatches
      next seenPublic opponent seenHidden own =>
        obtain ⟨rfl, rfl⟩ := hmatches
        cases player <;> cases hiddenActiveBit <;> cases choice <;>
          simp [menu, LegalOption, active]
  | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
      cases view <;> simp [ViewMatches] at hmatches
      cases choice <;> simp [menu, LegalOption, active]

@[reducible]
def information : InformationModel execution where
  toInfoSignals := signals
  menu := menu
  menu_adequate := menu_adequate

@[reducible]
def game : FOSG.Game Bool where
  execution := execution
  information := information

@[simp]
theorem infoOf_round2History (player left right publicBit hiddenActiveBit : Bool) :
    signals.infoOf player
        (round2History left right publicBit hiddenActiveBit).trace =
      .round2 publicBit (if player then left else right)
        (if player then some hiddenActiveBit else none)
        (if player then right else left) := by
  cases player <;>
    simp [round2History, InfoSignals.infoOf_extend, signals, pushView,
      publicOfTransition, privateOfTransition, firstJoint]

@[simp]
theorem infoOf_finishedHistory (player left right publicBit hiddenActiveBit
    falseAction trueAction secondCoin : Bool) :
    signals.infoOf player
        (finishedHistory left right publicBit hiddenActiveBit falseAction
          trueAction secondCoin).trace =
      .done publicBit (if player then left else right)
        (if player then some hiddenActiveBit else none)
        (if player then right else left) secondCoin
        ((secondJoint hiddenActiveBit falseAction trueAction) (!player))
        ((secondJoint hiddenActiveBit falseAction trueAction) player) := by
  cases player <;> cases hiddenActiveBit <;>
    simp [finishedHistory, round2History, InfoSignals.infoOf_extend,
      signals, pushView, publicOfTransition, privateOfTransition,
      firstJoint, secondJoint]

theorem round2_histories_merge (publicBit hiddenActiveBit : Bool) :
    (round2History false false publicBit hiddenActiveBit).state =
      (round2History true false publicBit hiddenActiveBit).state := rfl

theorem round2_traces_distinct (publicBit hiddenActiveBit : Bool) :
    (round2History false false publicBit hiddenActiveBit).trace ≠
      (round2History true false publicBit hiddenActiveBit).trace := by
  intro hequal
  have hinfo := congrArg
    (fun trace : execution.Trace (.round2 publicBit hiddenActiveBit) =>
      information.infoOf false trace) hequal
  simp [round2History, signals, InfoSignals.infoOf, pushView,
    publicOfTransition, privateOfTransition, firstJoint] at hinfo

theorem not_treeShaped : ¬ execution.IsTreeShaped := by
  intro htree
  have hequal :
      (round2History false false false false).trace =
        (round2History true false false false).trace :=
    (htree (.round2 false false)).allEq _ _
  exact round2_traces_distinct false false hequal

theorem start_not_mem_step (source : State)
    (certified : { joint : Bool → Option Bool // execution.Legal source joint }) :
    State.start ∉ (execution.step source certified).support := by
  cases source with
  | start => simp [execution, FinDist.support_map]
  | round2 publicBit hiddenActiveBit =>
      simp [execution, FinDist.support_map]
  | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
      exact fun _ => certified.2.1 trivial

theorem false_does_not_observe_hidden_activity (left right publicBit : Bool) :
    information.infoOf false
        (round2History left right publicBit false).trace =
      information.infoOf false
        (round2History left right publicBit true).trace := by
  rw [infoOf_round2History, infoOf_round2History]
  simp

theorem true_observes_hidden_activity (left right publicBit : Bool) :
    information.infoOf true
        (round2History left right publicBit false).trace ≠
      information.infoOf true
        (round2History left right publicBit true).trace := by
  rw [infoOf_round2History, infoOf_round2History]
  simp

theorem own_first_action_is_remembered (right publicBit hiddenActiveBit : Bool) :
    information.infoOf false
        (round2History false right publicBit hiddenActiveBit).trace ≠
      information.infoOf false
        (round2History true right publicBit hiddenActiveBit).trace := by
  rw [infoOf_round2History, infoOf_round2History]
  simp

theorem opponent_first_action_is_private (left publicBit hiddenActiveBit : Bool) :
    information.infoOf false
        (round2History left false publicBit hiddenActiveBit).trace ≠
      information.infoOf false
        (round2History left true publicBit hiddenActiveBit).trace := by
  rw [infoOf_round2History, infoOf_round2History]
  simp

theorem public_bit_is_observed (player left right hiddenActiveBit : Bool) :
    information.infoOf player
        (round2History left right false hiddenActiveBit).trace ≠
      information.infoOf player
        (round2History left right true hiddenActiveBit).trace := by
  rw [infoOf_round2History, infoOf_round2History]
  cases player <;> simp

end Source

namespace Serial

abbrev ChoiceAt (history : Source.execution.History) (player : Bool) :=
  { choice : Option Bool //
    LegalOption Source.execution history.state player choice }

inductive State (first : Bool)
  | boundary (history : Source.execution.History)
  | afterFirst (history : Source.execution.History)
      (choice : ChoiceAt history first)
  | ready (history : Source.execution.History)
      (firstChoice : ChoiceAt history first)
      (secondChoice : ChoiceAt history (!first))

def State.history {first : Bool} : State first → Source.execution.History
  | .boundary history => history
  | .afterFirst history _ => history
  | .ready history _ _ => history

def active (first : Bool) : State first → Bool → Prop
  | .boundary history, player =>
      player = first ∧ Source.execution.active history.state player
  | .afterFirst history _, player =>
      player = !first ∧ Source.execution.active history.state player
  | .ready .., _ => False

def terminal {first : Bool} (state : State first) : Prop :=
  Source.execution.terminal state.history.state

theorem terminal_of_history_finished {first : Bool} {state : State first}
    {publicBit hiddenActiveBit falseAction secondCoin : Bool}
    {trueAction : Option Bool}
    (hstate : state.history.state =
      .finished publicBit hiddenActiveBit falseAction trueAction secondCoin) :
    terminal state := by
  unfold terminal
  rw [hstate]
  trivial

def selectedJoint (owner : Bool) (choice : Option Bool) :
    Bool → Option Bool :=
  fun player => if player = owner then choice else none

def combine (first : Bool) {history : Source.execution.History}
    (firstChoice : ChoiceAt history first)
    (secondChoice : ChoiceAt history (!first)) : Bool → Option Bool :=
  fun player => if player = first then firstChoice.1 else secondChoice.1

theorem combine_legal (first : Bool) {history : Source.execution.History}
    (hterm : ¬ Source.execution.terminal history.state)
    (firstChoice : ChoiceAt history first)
    (secondChoice : ChoiceAt history (!first)) :
    Source.execution.Legal history.state
      (combine first firstChoice secondChoice) := by
  apply ExecutionProtocol.legal_of_legalOption hterm
  intro player
  cases first with
  | false =>
      cases player with
      | false =>
          simpa only [combine, ↓reduceIte] using firstChoice.2
      | true =>
          simpa only [combine, Bool.true_eq_false, ↓reduceIte]
            using (show ChoiceAt history true from secondChoice).2
  | true =>
      cases player with
      | false =>
          simpa only [combine, Bool.false_eq_true, ↓reduceIte]
            using (show ChoiceAt history false from secondChoice).2
      | true =>
          simpa only [combine, ↓reduceIte] using firstChoice.2

private def firstChoiceOfJoint (first : Bool)
    (history : Source.execution.History)
    (joint : Bool → Option Bool)
    (hlegal : IsLegalJoint (active first (.boundary history))
      (fun _ => Set.univ) joint) : ChoiceAt history first :=
  ⟨joint first, by
    have hfirst := hlegal first
    cases hchoice : joint first with
    | none => simpa [active, LegalOption, hchoice] using hfirst
    | some action => simpa [active, LegalOption, hchoice] using hfirst⟩

private def secondChoiceOfJoint (first : Bool)
    (history : Source.execution.History)
    (prior : ChoiceAt history first)
    (joint : Bool → Option Bool)
    (hlegal : IsLegalJoint (active first (.afterFirst history prior))
      (fun _ => Set.univ) joint) : ChoiceAt history (!first) :=
  ⟨joint (!first), by
    have hsecond := hlegal (!first)
    cases hchoice : joint (!first) with
    | none => simpa [active, LegalOption, hchoice] using hsecond
    | some action => simpa [active, LegalOption, hchoice] using hsecond⟩

def resolve (first : Bool) (history : Source.execution.History)
    (firstChoice : ChoiceAt history first)
    (secondChoice : ChoiceAt history (!first))
    (hterm : ¬ Source.execution.terminal history.state) :
    FinDist (State first) :=
  let sourceLegal := combine_legal first hterm firstChoice secondChoice
  (Source.execution.step history.state
      ⟨combine first firstChoice secondChoice, sourceLegal⟩).bindOnSupport
    fun _ realized =>
      FinDist.pure <| .boundary (history.extend sourceLegal realized)

theorem mem_support_resolve_iff (first : Bool)
    (history : Source.execution.History)
    (firstChoice : ChoiceAt history first)
    (secondChoice : ChoiceAt history (!first))
    (hterm : ¬ Source.execution.terminal history.state)
    (target : State first) :
    target ∈ (resolve first history firstChoice secondChoice hterm).support ↔
      ∃ (reached : Source.execution.State)
        (realized : reached ∈
          (Source.execution.step history.state
            ⟨combine first firstChoice secondChoice,
              combine_legal first hterm firstChoice secondChoice⟩).support),
        target = .boundary
          (history.extend
            (combine_legal first hterm firstChoice secondChoice) realized) := by
  simp [resolve, FinDist.support_bindOnSupport]

@[reducible]
def execution (first : Bool) : ExecutionProtocol Bool := by
  classical
  exact {
    State := State first
    Action _ := Bool
    init := .boundary Source.execution.initHistory
    active := active first
    available _ _ := Set.univ
    terminal := terminal
    step state joint :=
      match state with
      | .boundary history =>
          FinDist.pure <| .afterFirst history
            (firstChoiceOfJoint first history joint.1 joint.2.2)
      | .afterFirst history prior =>
          FinDist.pure <| .ready history prior
            (secondChoiceOfJoint first history prior joint.1 joint.2.2)
      | .ready history firstChoice secondChoice =>
          resolve first history firstChoice secondChoice
            (show ¬ Source.execution.terminal history.state from joint.2.1)
    progress := by
      classical
      intro state hterm
      refine ⟨fun player => if active first state player then some false else none,
        fun player => ?_⟩
      by_cases hactive : active first state player
      · simp [hactive]
      · simp [hactive]
  }

theorem step_boundary (first : Bool) (history : Source.execution.History)
    (joint : Bool → Option Bool)
    (hlegal : (execution first).Legal (.boundary history) joint) :
    (execution first).step (.boundary history) ⟨joint, hlegal⟩ =
      FinDist.pure (.afterFirst history
        (firstChoiceOfJoint first history joint hlegal.2)) := by
  rfl

theorem step_afterFirst (first : Bool) (history : Source.execution.History)
    (prior : ChoiceAt history first)
    (joint : Bool → Option Bool)
    (hlegal : (execution first).Legal (.afterFirst history prior) joint) :
    (execution first).step (.afterFirst history prior) ⟨joint, hlegal⟩ =
      FinDist.pure (.ready history prior
        (secondChoiceOfJoint first history prior joint hlegal.2)) := by
  rfl

theorem step_ready (first : Bool) (history : Source.execution.History)
    (firstChoice : ChoiceAt history first)
    (secondChoice : ChoiceAt history (!first))
    (joint : Bool → Option Bool)
    (hlegal : (execution first).Legal
      (.ready history firstChoice secondChoice) joint) :
    (execution first).step (.ready history firstChoice secondChoice)
        ⟨joint, hlegal⟩ =
      resolve first history firstChoice secondChoice hlegal.1 := by
  rfl

theorem singleMover (first : Bool) (state : State first) {one two : Bool}
    (hone : (execution first).active state one)
    (htwo : (execution first).active state two) : one = two := by
  cases state with
  | boundary history => exact hone.1.trans htwo.1.symm
  | afterFirst history prior => exact hone.1.trans htwo.1.symm
  | ready history firstChoice secondChoice => exact False.elim hone

theorem selection_preserves_history_first (first : Bool)
    (history : Source.execution.History)
    (joint : Bool → Option Bool)
    (hlegal : (execution first).Legal (.boundary history) joint) :
    ((State.afterFirst history
      (firstChoiceOfJoint first history joint hlegal.2)).history) = history := rfl

theorem selection_preserves_history_second (first : Bool)
    (history : Source.execution.History)
    (prior : ChoiceAt history first)
    (joint : Bool → Option Bool)
    (hlegal : (execution first).Legal (.afterFirst history prior) joint) :
    ((State.ready history prior
      (secondChoiceOfJoint first history prior joint hlegal.2)).history) = history := rfl

def choiceOfSourceLegal (history : Source.execution.History)
    (joint : Bool → Option Bool)
    (hlegal : Source.execution.Legal history.state joint)
    (player : Bool) : ChoiceAt history player :=
  ⟨joint player, Source.execution.legalOption_of_legal hlegal player⟩

theorem combine_choiceOfSourceLegal (first : Bool)
    (history : Source.execution.History)
    (joint : Bool → Option Bool)
    (hlegal : Source.execution.Legal history.state joint) :
    combine first (choiceOfSourceLegal history joint hlegal first)
      (choiceOfSourceLegal history joint hlegal (!first)) = joint := by
  funext player
  cases first <;> cases player <;> simp [combine, choiceOfSourceLegal]

def predecessor (first : Bool) : State first → Option (State first)
  | .boundary ⟨_, .start⟩ => none
  | .boundary ⟨_, .extend (source := source) prior joint hlegal _⟩ =>
      let history : Source.execution.History := ⟨source, prior⟩
      some <| .ready history
        (choiceOfSourceLegal history joint hlegal first)
        (choiceOfSourceLegal history joint hlegal (!first))
  | .afterFirst history _ => some (.boundary history)
  | .ready history firstChoice _ =>
      some (.afterFirst history firstChoice)

theorem history_extend_ne_init (history : Source.execution.History)
    {joint : Bool → Option Bool}
    (hlegal : Source.execution.Legal history.state joint)
    {target : Source.execution.State}
    (realized : target ∈
      (Source.execution.step history.state ⟨joint, hlegal⟩).support) :
    history.extend hlegal realized ≠ Source.execution.initHistory := by
  intro hequal
  have hlength := congrArg
    (fun reached : Source.execution.History => reached.trace.length) hequal
  have hextend :
      (history.extend hlegal realized).trace.length =
        history.trace.length + 1 := rfl
  have hinit : Source.execution.initHistory.trace.length = 0 := rfl
  omega

theorem predecessor_of_mem_resolve (first : Bool)
    (history : Source.execution.History)
    (firstChoice : ChoiceAt history first)
    (secondChoice : ChoiceAt history (!first))
    (hterm : ¬ Source.execution.terminal history.state)
    (target : State first)
    (realized : target ∈
      (resolve first history firstChoice secondChoice hterm).support) :
    predecessor first target = some (.ready history firstChoice secondChoice) := by
  rw [mem_support_resolve_iff] at realized
  obtain ⟨reached, hreached, rfl⟩ := realized
  show some
      (State.ready history
        (choiceOfSourceLegal history (combine first firstChoice secondChoice)
          (combine_legal first hterm firstChoice secondChoice) first)
        (choiceOfSourceLegal history (combine first firstChoice secondChoice)
          (combine_legal first hterm firstChoice secondChoice) (!first))) =
    some (State.ready history firstChoice secondChoice)
  have hfirst :
      choiceOfSourceLegal history (combine first firstChoice secondChoice)
          (combine_legal first hterm firstChoice secondChoice) first =
        firstChoice := by
    apply Subtype.ext
    simp [choiceOfSourceLegal, combine]
  have hsecond :
      choiceOfSourceLegal history (combine first firstChoice secondChoice)
          (combine_legal first hterm firstChoice secondChoice) (!first) =
        secondChoice := by
    apply Subtype.ext
    cases first <;> simp [choiceOfSourceLegal, combine]
  rw [hfirst, hsecond]

theorem root_not_mem_step (first : Bool) (source : State first)
    (certified : { joint : Bool → Option Bool //
      (execution first).Legal source joint }) :
    State.boundary Source.execution.initHistory ∉
      ((execution first).step source certified).support := by
  intro realized
  cases source with
  | boundary history =>
      cases hstate : history.state with
      | start =>
          rw [step_boundary first history certified.1 certified.2] at realized
          simp at realized
      | round2 publicBit hiddenActiveBit =>
          rw [step_boundary first history certified.1 certified.2] at realized
          simp at realized
      | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
          exact certified.2.1 (terminal_of_history_finished hstate)
  | afterFirst history prior =>
      cases hstate : history.state with
      | start =>
          rw [step_afterFirst first history prior certified.1 certified.2]
            at realized
          simp at realized
      | round2 publicBit hiddenActiveBit =>
          rw [step_afterFirst first history prior certified.1 certified.2]
            at realized
          simp at realized
      | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
          exact certified.2.1 (terminal_of_history_finished hstate)
  | ready history firstChoice secondChoice =>
      cases hstate : history.state with
      | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
          exact certified.2.1 (terminal_of_history_finished hstate)
      | start | round2 =>
          have hresolve :
            State.boundary Source.execution.initHistory ∈
                (resolve first history firstChoice secondChoice
                  certified.2.1).support := by
            rw [step_ready first history firstChoice secondChoice
              certified.1 certified.2] at realized
            exact realized
          rw [mem_support_resolve_iff] at hresolve
          obtain ⟨reached, hreached, hequal⟩ := hresolve
          have hhistory := State.boundary.inj hequal
          exact history_extend_ne_init history
            (combine_legal first certified.2.1 firstChoice secondChoice)
            hreached hhistory.symm

theorem source_eq_predecessor_of_mem_step (first : Bool)
    (source target : State first)
    (certified : { joint : Bool → Option Bool //
      (execution first).Legal source joint })
    (realized : target ∈
      ((execution first).step source certified).support) :
    some source = predecessor first target := by
  cases source with
  | boundary history =>
      cases hstate : history.state with
      | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
          exact False.elim
            (certified.2.1 (terminal_of_history_finished hstate))
      | start | round2 =>
          rw [step_boundary first history certified.1 certified.2] at realized
          simp at realized
          rw [realized]
          rfl
  | afterFirst history prior =>
      cases hstate : history.state with
      | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
          exact False.elim
            (certified.2.1 (terminal_of_history_finished hstate))
      | start | round2 =>
          rw [step_afterFirst first history prior certified.1 certified.2]
            at realized
          simp at realized
          rw [realized]
          rfl
  | ready history firstChoice secondChoice =>
      cases hstate : history.state with
      | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
          exact False.elim
            (certified.2.1 (terminal_of_history_finished hstate))
      | start | round2 =>
          have hresolve : target ∈
              (resolve first history firstChoice secondChoice
                certified.2.1).support := by
            rw [step_ready first history firstChoice secondChoice
              certified.1 certified.2] at realized
            exact realized
          rw [predecessor_of_mem_resolve first history firstChoice secondChoice
            certified.2.1 target hresolve]

theorem legal_joint_eq_of_at_most_owner (first : Bool)
    {state : State first} (owner : Bool)
    {one two : Bool → Option Bool}
    (hone : (execution first).Legal state one)
    (htwo : (execution first).Legal state two)
    (hunique : ∀ player, (execution first).active state player → player = owner)
    (howner : one owner = two owner) : one = two := by
  funext player
  by_cases hequal : player = owner
  · subst player
    exact howner
  · have hinactive : ¬ (execution first).active state player := by
      intro hactive
      exact hequal (hunique player hactive)
    have honePlayer := hone.2 player
    have htwoPlayer := htwo.2 player
    cases honeValue : one player with
    | some action =>
        rw [honeValue] at honePlayer
        exact False.elim (hinactive honePlayer.1)
    | none =>
        cases htwoValue : two player with
        | some action =>
            rw [htwoValue] at htwoPlayer
            exact False.elim (hinactive htwoPlayer.1)
        | none => rfl

theorem joint_eq_of_same_source_target (first : Bool)
    {source target : State first}
    {firstJoint secondJoint : Bool → Option Bool}
    (firstLegal : (execution first).Legal source firstJoint)
    (secondLegal : (execution first).Legal source secondJoint)
    (firstRealized : target ∈
      ((execution first).step source ⟨firstJoint, firstLegal⟩).support)
    (secondRealized : target ∈
      ((execution first).step source ⟨secondJoint, secondLegal⟩).support) :
    firstJoint = secondJoint := by
  cases source with
  | boundary history =>
      cases hstate : history.state with
      | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
          exact False.elim
            (firstLegal.1 (terminal_of_history_finished hstate))
      | start | round2 =>
          have hfirstTarget : target = .afterFirst history
              (firstChoiceOfJoint first history firstJoint firstLegal.2) := by
            rw [step_boundary first history firstJoint firstLegal]
              at firstRealized
            simpa using firstRealized
          have hsecondTarget : target = .afterFirst history
              (firstChoiceOfJoint first history secondJoint secondLegal.2) := by
            rw [step_boundary first history secondJoint secondLegal]
              at secondRealized
            simpa using secondRealized
          have hchoice :
              firstChoiceOfJoint first history firstJoint firstLegal.2 =
                firstChoiceOfJoint first history secondJoint secondLegal.2 := by
            simpa using hfirstTarget.symm.trans hsecondTarget
          apply legal_joint_eq_of_at_most_owner first first firstLegal secondLegal
          · intro player hactive
            exact hactive.1
          · exact congrArg Subtype.val hchoice
  | afterFirst history prior =>
      cases hstate : history.state with
      | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
          exact False.elim
            (firstLegal.1 (terminal_of_history_finished hstate))
      | start | round2 =>
          have hfirstTarget : target = .ready history prior
              (secondChoiceOfJoint first history prior firstJoint firstLegal.2) := by
            rw [step_afterFirst first history prior firstJoint firstLegal]
              at firstRealized
            simpa using firstRealized
          have hsecondTarget : target = .ready history prior
              (secondChoiceOfJoint first history prior secondJoint secondLegal.2) := by
            rw [step_afterFirst first history prior secondJoint secondLegal]
              at secondRealized
            simpa using secondRealized
          have hchoice :
              secondChoiceOfJoint first history prior firstJoint firstLegal.2 =
                secondChoiceOfJoint first history prior secondJoint secondLegal.2 := by
            simpa using hfirstTarget.symm.trans hsecondTarget
          apply legal_joint_eq_of_at_most_owner first (!first)
            firstLegal secondLegal
          · intro player hactive
            exact hactive.1
          · exact congrArg Subtype.val hchoice
  | ready history firstChoice secondChoice =>
      apply legal_joint_eq_of_at_most_owner first first firstLegal secondLegal
      · intro player hactive
        exact False.elim hactive
      · have hfirst := firstLegal.2 first
        have hsecond := secondLegal.2 first
        cases hone : firstJoint first with
        | some action =>
            rw [hone] at hfirst
            exact False.elim hfirst.1
        | none =>
            cases htwo : secondJoint first with
            | some action =>
                rw [htwo] at hsecond
                exact False.elim hsecond.1
            | none => rfl

theorem step_predecessor_unique (first : Bool)
    {target firstSource secondSource : State first}
    {firstJoint secondJoint : Bool → Option Bool}
    (firstLegal : (execution first).Legal firstSource firstJoint)
    (secondLegal : (execution first).Legal secondSource secondJoint)
    (firstRealized : target ∈
      ((execution first).step firstSource
        ⟨firstJoint, firstLegal⟩).support)
    (secondRealized : target ∈
      ((execution first).step secondSource
        ⟨secondJoint, secondLegal⟩).support) :
    firstSource = secondSource ∧ firstJoint = secondJoint := by
  have hfirst := source_eq_predecessor_of_mem_step first firstSource target
    ⟨firstJoint, firstLegal⟩ firstRealized
  have hsecond := source_eq_predecessor_of_mem_step first secondSource target
    ⟨secondJoint, secondLegal⟩ secondRealized
  have hsource : firstSource = secondSource :=
    Option.some.inj (hfirst.trans hsecond.symm)
  subst secondSource
  exact ⟨rfl, joint_eq_of_same_source_target first firstLegal secondLegal
    firstRealized secondRealized⟩

theorem trace_unique (first : Bool) :
    ∀ {state : State first}
      (one two : (execution first).Trace state), one = two
  | _, .start, .start => rfl
  | _, .start, .extend prior joint isLegal realized =>
      False.elim (root_not_mem_step first _ ⟨joint, isLegal⟩ realized)
  | _, .extend prior joint isLegal realized, .start =>
      False.elim (root_not_mem_step first _ ⟨joint, isLegal⟩ realized)
  | _, .extend prior joint isLegal realized,
      .extend secondPrior secondJoint secondLegal secondRealized => by
      obtain ⟨rfl, hjoint⟩ :=
        step_predecessor_unique first isLegal secondLegal realized secondRealized
      subst secondJoint
      have hprior := trace_unique first prior secondPrior
      subst secondPrior
      rfl
termination_by _ one _ => one.length
decreasing_by simp [ExecutionProtocol.Trace.length]

theorem treeShaped (first : Bool) :
    (execution first).IsTreeShaped :=
  fun _ => ⟨trace_unique first⟩

inductive Phase
  | firstSlot
  | secondSlot
  | resolving
  | done
  deriving DecidableEq

structure View where
  phase : Phase
  source : Source.View
  deriving DecidableEq

def phaseOfState {first : Bool} : State first → Phase
  | .boundary history =>
      match history.state with
      | .finished .. => .done
      | _ => .firstSlot
  | .afterFirst history _ =>
      match history.state with
      | .finished .. => .done
      | _ => .secondSlot
  | .ready history _ _ =>
      match history.state with
      | .finished .. => .done
      | _ => .resolving

def viewOfState {first : Bool} (player : Bool) (state : State first) : View :=
  ⟨phaseOfState state,
    Source.signals.infoOf player state.history.trace⟩

inductive PublicSignal
  | admin (phase : Phase)
  | resolve (phase : Phase) (source : Source.PublicSignal)
  deriving DecidableEq

inductive PrivateSignal
  | admin
  | resolve (sourceChoice : Option Bool) (source : Source.PrivateSignal)
  deriving DecidableEq

def publicSignalOfEvent {first : Bool}
    (event : (execution first).StepEvent) : PublicSignal :=
  match event.source, event.target with
  | .ready _ _ _, .boundary reached =>
      .resolve (phaseOfState event.target)
        (Source.publicOfTransition reached.state)
  | _, target => .admin (phaseOfState target)

def privateSignalOfEvent {first : Bool} (player : Bool)
    (event : (execution first).StepEvent) : PrivateSignal :=
  match event.source, event.target with
  | .ready _ firstChoice secondChoice, .boundary reached =>
      let joint := combine first firstChoice secondChoice
      .resolve (joint player)
        (Source.privateOfTransition player joint reached.state)
  | _, _ => .admin

def pushView (prior : View) (privateSignal : PrivateSignal)
    (publicSignal : PublicSignal) : View :=
  match privateSignal, publicSignal with
  | .admin, .admin phase => ⟨phase, prior.source⟩
  | .resolve sourceChoice sourcePrivate,
      .resolve phase sourcePublic =>
      ⟨phase, Source.pushView prior.source sourceChoice
        sourcePrivate sourcePublic⟩
  | _, _ => prior

@[reducible]
def signals (first : Bool) : InfoSignals (execution first) where
  PublicSignal := PublicSignal
  PrivateSignal _ := PrivateSignal
  initialPublic := .admin .firstSlot
  initialPrivate _ := .admin
  publicSignal := publicSignalOfEvent
  privateSignal := privateSignalOfEvent
  InfoState _ := View
  initInfo _ _ _ := ⟨.firstSlot, .round1⟩
  pushInfo _ prior _ privateSignal publicSignal :=
    pushView prior privateSignal publicSignal

theorem infoOf_eq_viewOfState (first player : Bool) :
    ∀ {state : State first} (trace : (execution first).Trace state),
      (signals first).infoOf player trace = viewOfState player state
  | _, .start => rfl
  | target, .extend (source := source) prior joint isLegal realized => by
      have hprior := infoOf_eq_viewOfState first player prior
      cases source with
      | boundary history =>
          cases hstate : history.state with
          | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
              exact False.elim
                (isLegal.1 (terminal_of_history_finished hstate))
          | start | round2 =>
              rw [step_boundary first history joint isLegal] at realized
              simp at realized
              cases realized
              rw [InfoSignals.infoOf_extend, hprior]
              rfl
      | afterFirst history firstChoice =>
          cases hstate : history.state with
          | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
              exact False.elim
                (isLegal.1 (terminal_of_history_finished hstate))
          | start | round2 =>
              rw [step_afterFirst first history firstChoice joint isLegal]
                at realized
              simp at realized
              cases realized
              rw [InfoSignals.infoOf_extend, hprior]
              rfl
      | ready history firstChoice secondChoice =>
          cases hstate : history.state with
          | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
              exact False.elim
                (isLegal.1 (terminal_of_history_finished hstate))
          | start | round2 =>
              have hresolve : target ∈
                  (resolve first history firstChoice secondChoice
                    isLegal.1).support := by
                rw [step_ready first history firstChoice secondChoice
                  joint isLegal] at realized
                exact realized
              rw [mem_support_resolve_iff] at hresolve
              obtain ⟨reached, hreached, rfl⟩ := hresolve
              rw [InfoSignals.infoOf_extend, hprior]
              simp [signals, pushView, publicSignalOfEvent,
                privateSignalOfEvent, viewOfState, phaseOfState,
                State.history, Source.signals]
              unfold ExecutionProtocol.History.extend
              rw [InfoSignals.infoOf_extend]

def menu (first player : Bool) (view : View) : Set (Option Bool) :=
  match view.phase with
  | .firstSlot =>
      if player = first then Source.menu player view.source else {none}
  | .secondSlot =>
      if player = !first then Source.menu player view.source else {none}
  | .resolving => {none}
  | .done => {none}

theorem legalOption_boundary_owner (first : Bool)
    (history : Source.execution.History) (choice : Option Bool) :
    LegalOption (execution first) (.boundary history) first choice ↔
      LegalOption Source.execution history.state first choice := by
  cases choice <;> simp [LegalOption, active]

theorem legalOption_afterFirst_owner (first : Bool)
    (history : Source.execution.History) (prior : ChoiceAt history first)
    (choice : Option Bool) :
    LegalOption (execution first) (.afterFirst history prior) (!first) choice ↔
      LegalOption Source.execution history.state (!first) choice := by
  cases first <;> cases choice <;> simp [LegalOption, active]

theorem menu_adequate (first player : Bool) {state : State first}
    (trace : (execution first).Trace state) (choice : Option Bool) :
    choice ∈ menu first player ((signals first).infoOf player trace) ↔
      LegalOption (execution first) state player choice := by
  rw [infoOf_eq_viewOfState]
  cases state with
  | boundary history =>
      cases hstate : history.state with
      | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
          cases choice <;>
            simp [menu, viewOfState, phaseOfState, State.history,
              LegalOption, active, Source.active, hstate]
      | start | round2 =>
          by_cases howner : player = first
          · subst player
            simp only [menu, viewOfState, phaseOfState, State.history,
              hstate, if_pos]
            rw [Source.menu_adequate]
            exact (legalOption_boundary_owner first history choice).symm
          · cases choice <;>
              simp [menu, viewOfState, phaseOfState, State.history,
                LegalOption, active, hstate, howner]
  | afterFirst history prior =>
      cases hstate : history.state with
      | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
          cases choice <;>
            simp [menu, viewOfState, phaseOfState, State.history,
              LegalOption, active, Source.active, hstate]
      | start | round2 =>
          by_cases howner : player = !first
          · rw [howner]
            simp only [menu, viewOfState, phaseOfState, State.history,
              hstate, if_pos]
            rw [Source.menu_adequate]
            exact (legalOption_afterFirst_owner first history prior choice).symm
          · cases choice <;>
              simp [menu, viewOfState, phaseOfState, State.history,
                LegalOption, active, hstate, howner]
  | ready history firstChoice secondChoice =>
      cases hstate : history.state <;> cases choice <;>
        simp [menu, viewOfState, phaseOfState, State.history,
          LegalOption, active, hstate]

@[reducible]
def information (first : Bool) : InformationModel (execution first) where
  toInfoSignals := signals first
  menu player := menu first player
  menu_adequate := menu_adequate first

@[reducible]
def game (first : Bool) : EFG.Game Bool where
  execution := execution first
  information := information first
  treeShaped := treeShaped first
  singleMover := singleMover first

theorem firstSlotLegal (first : Bool) (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (choice : ChoiceAt history first) :
    (execution first).Legal (.boundary history)
      (selectedJoint first choice.1) := by
  apply (execution first).legal_of_legalOption
    (show ¬ terminal (.boundary history) from hterm)
  intro player
  by_cases howner : player = first
  · subst player
    simpa [selectedJoint] using
      (legalOption_boundary_owner first history choice.1).mpr choice.2
  · simp [selectedJoint, LegalOption, active, howner]

theorem secondSlotLegal (first : Bool) (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (firstChoice : ChoiceAt history first)
    (secondChoice : ChoiceAt history (!first)) :
    (execution first).Legal (.afterFirst history firstChoice)
      (selectedJoint (!first) secondChoice.1) := by
  apply (execution first).legal_of_legalOption
    (show ¬ terminal (.afterFirst history firstChoice) from hterm)
  intro player
  by_cases howner : player = !first
  · rw [howner]
    simpa [selectedJoint] using
      (legalOption_afterFirst_owner first history firstChoice secondChoice.1).mpr
        secondChoice.2
  · simp [selectedJoint, LegalOption, active, howner]

theorem resolveLegal (first : Bool) (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (firstChoice : ChoiceAt history first)
    (secondChoice : ChoiceAt history (!first)) :
    (execution first).Legal (.ready history firstChoice secondChoice)
      (fun _ => none) := by
  refine ⟨hterm, fun player => ?_⟩
  simp [active]

theorem firstSlot_realized (first : Bool)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (choice : ChoiceAt history first) :
    State.afterFirst history choice ∈
      ((execution first).step (.boundary history)
        ⟨selectedJoint first choice.1,
          firstSlotLegal first history hterm choice⟩).support := by
  rw [step_boundary first history (selectedJoint first choice.1)
    (firstSlotLegal first history hterm choice)]
  simp [firstChoiceOfJoint, selectedJoint]

theorem secondSlot_realized (first : Bool)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (firstChoice : ChoiceAt history first)
    (secondChoice : ChoiceAt history (!first)) :
    State.ready history firstChoice secondChoice ∈
      ((execution first).step (.afterFirst history firstChoice)
        ⟨selectedJoint (!first) secondChoice.1,
          secondSlotLegal first history hterm firstChoice secondChoice⟩).support := by
  rw [step_afterFirst first history firstChoice
    (selectedJoint (!first) secondChoice.1)
    (secondSlotLegal first history hterm firstChoice secondChoice)]
  simp [secondChoiceOfJoint, selectedJoint]

theorem resolve_realized (first : Bool)
    (history : Source.execution.History)
    (joint : Bool → Option Bool)
    (sourceLegal : Source.execution.Legal history.state joint)
    {reached : Source.execution.State}
    (sourceRealized : reached ∈
      (Source.execution.step history.state ⟨joint, sourceLegal⟩).support) :
    let firstChoice := choiceOfSourceLegal history joint sourceLegal first
    let secondChoice := choiceOfSourceLegal history joint sourceLegal (!first)
    State.boundary (history.extend sourceLegal sourceRealized) ∈
      ((execution first).step (.ready history firstChoice secondChoice)
        ⟨fun _ => none,
          resolveLegal first history sourceLegal.1 firstChoice secondChoice⟩).support := by
  dsimp
  have hresolve :
      State.boundary (history.extend sourceLegal sourceRealized) ∈
        (resolve first history
          (choiceOfSourceLegal history joint sourceLegal first)
          (choiceOfSourceLegal history joint sourceLegal (!first))
          sourceLegal.1).support := by
    rw [mem_support_resolve_iff]
    let firstChoice := choiceOfSourceLegal history joint sourceLegal first
    let secondChoice := choiceOfSourceLegal history joint sourceLegal (!first)
    let combinedLegal := combine_legal first sourceLegal.1 firstChoice secondChoice
    have hcertified :
        (⟨combine first firstChoice secondChoice, combinedLegal⟩ :
          { candidate : Bool → Option Bool //
            Source.execution.Legal history.state candidate }) =
          ⟨joint, sourceLegal⟩ := by
      apply Subtype.ext
      exact combine_choiceOfSourceLegal first history joint sourceLegal
    have hsupport : reached ∈
        (Source.execution.step history.state
          ⟨combine first firstChoice secondChoice, combinedLegal⟩).support := by
      have hstep := congrArg (Source.execution.step history.state) hcertified
      have hsupportEq := congrArg FinDist.support hstep
      exact (Set.ext_iff.mp hsupportEq reached).mpr sourceRealized
    refine ⟨reached, hsupport, ?_⟩
    congr
    exact (combine_choiceOfSourceLegal first history joint sourceLegal).symm
  exact hresolve

def boundaryTrace (first : Bool) :
    (history : Source.execution.History) →
      (execution first).Trace (.boundary history)
  | ⟨_, .start⟩ => .start
  | ⟨target, .extend (source := source) prior joint sourceLegal sourceRealized⟩ =>
      let history : Source.execution.History := ⟨source, prior⟩
      let firstChoice := choiceOfSourceLegal history joint sourceLegal first
      let secondChoice := choiceOfSourceLegal history joint sourceLegal (!first)
      let afterFirst : (execution first).Trace (.afterFirst history firstChoice) :=
        .extend (boundaryTrace first history)
          (selectedJoint first firstChoice.1)
          (firstSlotLegal first history sourceLegal.1 firstChoice)
          (firstSlot_realized first history sourceLegal.1 firstChoice)
      let ready : (execution first).Trace
          (.ready history firstChoice secondChoice) :=
        .extend afterFirst (selectedJoint (!first) secondChoice.1)
          (secondSlotLegal first history sourceLegal.1 firstChoice secondChoice)
          (secondSlot_realized first history sourceLegal.1 firstChoice secondChoice)
      .extend ready (fun _ => none)
        (resolveLegal first history sourceLegal.1 firstChoice secondChoice)
        (resolve_realized first history joint sourceLegal sourceRealized)
termination_by history => history.trace.length
decreasing_by simp [ExecutionProtocol.Trace.length]

def scheduledPhase (first player : Bool) : Source.View → Phase
  | .done .. => .done
  | _ => if player = first then .firstSlot else .secondSlot

def scheduledView (first player : Bool) (source : Source.View) : View :=
  ⟨scheduledPhase first player source, source⟩

@[simp]
theorem scheduledView_source (first player : Bool) (source : Source.View) :
    (scheduledView first player source).source = source := rfl

theorem menu_scheduledView (first player : Bool) (source : Source.View) :
    menu first player (scheduledView first player source) =
      Source.menu player source := by
  cases source <;> cases first <;> cases player <;>
    simp [menu, scheduledView, scheduledPhase, Source.menu]

def choiceEquiv (first player : Bool) (source : Source.View) :
    (information first).Choice player (scheduledView first player source) ≃
      Source.information.Choice player source where
  toFun choice := ⟨choice.1, by
    have hmem : choice.1 ∈
        menu first player (scheduledView first player source) := choice.2
    rw [menu_scheduledView first player source] at hmem
    exact hmem⟩
  invFun choice := ⟨choice.1, by
    have hmem : choice.1 ∈ Source.menu player source := choice.2
    rw [← menu_scheduledView first player source] at hmem
    exact hmem⟩
  left_inv _ := rfl
  right_inv _ := rfl

def projectBehavioral (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player) :
    (player : Bool) → Source.information.BehavioralPolicy player :=
  fun player source =>
    FinDist.map (choiceEquiv first player source)
      (target player (scheduledView first player source))

noncomputable def defaultChoice (first player : Bool) (view : View) :
    (information first).Choice player view := by
  classical
  by_cases hsome : some false ∈ (information first).menu player view
  · exact ⟨some false, hsome⟩
  · refine ⟨none, ?_⟩
    show none ∈ menu first player view
    have hsome' : some false ∉ menu first player view := hsome
    cases view with
    | mk phase source =>
        cases phase <;> cases source <;> cases first <;> cases player <;>
          simp [menu, Source.menu] at hsome' ⊢
        all_goals split at * <;> simp_all

def translateBehavioral (first : Bool)
    (source : (player : Bool) →
      Source.information.BehavioralPolicy player) :
    (player : Bool) → (information first).BehavioralPolicy player :=
  fun player view =>
    if hview : view = scheduledView first player view.source then
      FinDist.map (fun choice => ⟨choice.1, by
        have hmenu : (information first).menu player view =
            Source.information.menu player view.source := by
          rw [hview]
          exact menu_scheduledView first player view.source
        rw [hmenu]
        exact choice.2⟩) (source player view.source)
    else
      FinDist.pure (defaultChoice first player view)

theorem project_translate (first player : Bool) (sourceView : Source.View)
    (source : (player : Bool) →
      Source.information.BehavioralPolicy player) :
    projectBehavioral first (translateBehavioral first source)
        player sourceView =
      source player sourceView := by
  unfold projectBehavioral translateBehavioral
  rw [dif_pos (by simp), FinDist.map_comp]
  show FinDist.map _ (source player sourceView) = source player sourceView
  convert FinDist.map_id (source player sourceView) using 1
  apply congrArg (fun f => FinDist.map f (source player sourceView))
  funext choice
  apply Subtype.ext
  rfl

def sourceChoiceAt (history : Source.execution.History) (player : Bool)
    (choice : Source.information.Choice player
      (Source.information.infoOf player history.trace)) :
    ChoiceAt history player :=
  ⟨choice.1,
    (Source.menu_adequate player history.trace choice.1).mp choice.2⟩

def extendCertifiedSourceLaw (history : Source.execution.History)
    (draw : { joint : Bool → Option Bool //
      Source.execution.Legal history.state joint }) :
    FinDist Source.execution.History :=
  (Source.execution.step history.state draw).bindOnSupport
    fun _ realized => FinDist.pure (history.extend draw.2 realized)

def extendSourceLaw (history : Source.execution.History)
    (joint : Bool → Option Bool)
    (hlegal : Source.execution.Legal history.state joint) :
    FinDist Source.execution.History :=
  extendCertifiedSourceLaw history ⟨joint, hlegal⟩

def orderedSourceHistoryLaw (first : Bool)
    (policies : (player : Bool) →
      Source.information.BehavioralPolicy player)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state) :
    FinDist Source.execution.History :=
  (policies first (Source.information.infoOf first history.trace)).bind
    fun firstChoice =>
      (policies (!first)
        (Source.information.infoOf (!first) history.trace)).bind
        fun secondChoice =>
          let firstAt := sourceChoiceAt history first firstChoice
          let secondAt := sourceChoiceAt history (!first) secondChoice
          extendSourceLaw history
            (combine first firstAt secondAt)
            (combine_legal first hterm firstAt secondAt)

theorem source_runBehavioralFrom_one_eq_ordered (first : Bool)
    (policies : (player : Bool) →
      Source.information.BehavioralPolicy player)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state) :
    Source.information.runBehavioralFrom policies 1 history =
      orderedSourceHistoryLaw first policies history hterm := by
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ 0 hterm]
  unfold InformationModel.randomizedChooser
  unfold InformationModel.behavioralJoint
  rw [FinDist.bind_map]
  unfold orderedSourceHistoryLaw
  simp_rw [ExecutionProtocol.runRandomizedFor_zero]
  rw [pi_bool_eq_map_product, FinDist.bind_map]
  unfold FinDist.product
  rw [FinDist.bind_bind]
  simp_rw [FinDist.bind_map]
  cases first
  · apply FinDist.bind_congr
    intro firstChoice _
    apply FinDist.bind_congr
    intro secondChoice _
    let draws := boolPairAssignment
      (α := fun player => Source.information.Choice player
        (Source.information.infoOf player history.trace))
      (firstChoice, secondChoice)
    let firstAt := sourceChoiceAt history false firstChoice
    let secondAt := sourceChoiceAt history true secondChoice
    have hcertified :
        (⟨fun player => (draws player).1,
          ExecutionProtocol.legal_of_legalOption hterm fun player =>
            (Source.menu_adequate player history.trace
              (draws player).1).mp (draws player).2⟩ :
          { joint : Bool → Option Bool //
            Source.execution.Legal history.state joint }) =
          ⟨combine false firstAt secondAt,
            combine_legal false hterm firstAt secondAt⟩ := by
      apply Subtype.ext
      funext player
      cases player <;> rfl
    show extendCertifiedSourceLaw history
        ⟨fun player => (draws player).1, _⟩ =
      extendCertifiedSourceLaw history
        ⟨combine false firstAt secondAt, _⟩
    exact congrArg (extendCertifiedSourceLaw history) hcertified
  · conv_lhs => rw [FinDist.bind_comm]
    apply FinDist.bind_congr
    intro firstChoice _
    apply FinDist.bind_congr
    intro secondChoice _
    let draws := boolPairAssignment
      (α := fun player => Source.information.Choice player
        (Source.information.infoOf player history.trace))
      (secondChoice, firstChoice)
    let firstAt := sourceChoiceAt history true firstChoice
    let secondAt := sourceChoiceAt history false secondChoice
    have hcertified :
        (⟨fun player => (draws player).1,
          ExecutionProtocol.legal_of_legalOption hterm fun player =>
            (Source.menu_adequate player history.trace
              (draws player).1).mp (draws player).2⟩ :
          { joint : Bool → Option Bool //
            Source.execution.Legal history.state joint }) =
          ⟨combine true firstAt secondAt,
            combine_legal true hterm firstAt secondAt⟩ := by
      apply Subtype.ext
      funext player
      cases player <;> rfl
    show extendCertifiedSourceLaw history
        ⟨fun player => (draws player).1, _⟩ =
      extendCertifiedSourceLaw history
        ⟨combine true firstAt secondAt, _⟩
    exact congrArg (extendCertifiedSourceLaw history) hcertified

def eraseHistory (first : Bool) (history : (execution first).History) :
    Source.execution.History :=
  history.state.history

def boundaryHistory (first : Bool) (history : Source.execution.History) :
    (execution first).History :=
  ⟨.boundary history, boundaryTrace first history⟩

theorem scheduledPhase_of_not_terminal (first player : Bool)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state) :
    scheduledPhase first player
        (Source.information.infoOf player history.trace) =
      if player = first then .firstSlot else .secondSlot := by
  have hmatches := Source.infoOf_matches player history.trace
  generalize hview : Source.information.infoOf player history.trace = view
    at hmatches ⊢
  cases hstate : history.state with
  | start =>
      cases view <;> simp [Source.ViewMatches, hstate] at hmatches
      simp [scheduledPhase]
  | round2 publicBit hiddenActiveBit =>
      cases view <;> simp [Source.ViewMatches, hstate] at hmatches
      simp [scheduledPhase]
  | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
      exact False.elim (hterm (by simp [Source.terminal, hstate]))

theorem boundary_info_eq_scheduled (first : Bool)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (trace : (execution first).Trace (.boundary history)) :
    (information first).infoOf first trace =
      scheduledView first first
        (Source.information.infoOf first history.trace) := by
  rw [infoOf_eq_viewOfState]
  unfold viewOfState scheduledView
  apply congrArg (fun phase =>
    View.mk phase (Source.information.infoOf first history.trace))
  rcases history with ⟨state, sourceTrace⟩
  cases state with
  | start | round2 =>
      rw [scheduledPhase_of_not_terminal first first _ hterm]
      simp [phaseOfState]
  | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
      exact False.elim (hterm (by simp [Source.terminal]))

theorem afterFirst_info_eq_scheduled (first : Bool)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (prior : ChoiceAt history first)
    (trace : (execution first).Trace (.afterFirst history prior)) :
    (information first).infoOf (!first) trace =
      scheduledView first (!first)
        (Source.information.infoOf (!first) history.trace) := by
  rw [infoOf_eq_viewOfState]
  unfold viewOfState scheduledView
  apply congrArg (fun phase =>
    View.mk phase (Source.information.infoOf (!first) history.trace))
  rcases history with ⟨state, sourceTrace⟩
  cases state with
  | start | round2 =>
      rw [scheduledPhase_of_not_terminal first (!first) _ hterm]
      cases first <;> simp [phaseOfState]
  | finished publicBit hiddenActiveBit falseAction trueAction secondCoin =>
      exact False.elim (hterm (by simp [Source.terminal]))

def scheduledChoiceAt (first : Bool)
    (history : Source.execution.History) (player : Bool)
    (choice : (information first).Choice player
      (scheduledView first player
        (Source.information.infoOf player history.trace))) :
    ChoiceAt history player :=
  sourceChoiceAt history player
    (choiceEquiv first player
      (Source.information.infoOf player history.trace) choice)

def targetChoiceAtLaw (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History) (player : Bool) :
    FinDist (ChoiceAt history player) :=
  FinDist.map (scheduledChoiceAt first history player)
    (target player
      (scheduledView first player
        (Source.information.infoOf player history.trace)))

def choiceAtOfViewEq (first : Bool)
    (history : Source.execution.History) (player : Bool)
    (view : (information first).InfoState player)
    (hview : view = scheduledView first player
      (Source.information.infoOf player history.trace))
    (choice : (information first).Choice player view) :
    ChoiceAt history player := by
  subst view
  exact scheduledChoiceAt first history player choice

@[simp]
theorem choiceAtOfViewEq_val (first : Bool)
    (history : Source.execution.History) (player : Bool)
    (view : (information first).InfoState player)
    (hview : view = scheduledView first player
      (Source.information.infoOf player history.trace))
    (choice : (information first).Choice player view) :
    (choiceAtOfViewEq first history player view hview choice).1 = choice.1 := by
  subst view
  rfl

theorem map_choiceAtOfViewEq (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History) (player : Bool)
    (view : (information first).InfoState player)
    (hview : view = scheduledView first player
      (Source.information.infoOf player history.trace)) :
    FinDist.map (choiceAtOfViewEq first history player view hview)
        (target player view) =
      targetChoiceAtLaw first target history player := by
  subst view
  rfl

def afterFirstChoiceAt (first : Bool)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (prior : ChoiceAt history first)
    (trace : (execution first).Trace (.afterFirst history prior))
    (choice : (information first).Choice (!first)
      ((information first).infoOf (!first) trace)) :
    ChoiceAt history (!first) :=
  choiceAtOfViewEq first history (!first)
    ((information first).infoOf (!first) trace)
    (afterFirst_info_eq_scheduled first history
      hterm prior trace)
    choice

theorem map_erase_runBehavioralFrom_ready (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (firstChoice : ChoiceAt history first)
    (secondChoice : ChoiceAt history (!first))
    (trace : (execution first).Trace
      (.ready history firstChoice secondChoice)) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioralFrom target 1
          ⟨.ready history firstChoice secondChoice, trace⟩) =
      extendSourceLaw history
        (combine first firstChoice secondChoice)
        (combine_legal first hterm firstChoice secondChoice) := by
  have htargetTerm : ¬ (execution first).terminal
      (.ready history firstChoice secondChoice) := hterm
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 0 htargetTerm,
    FinDist.map_bind]
  unfold InformationModel.randomizedChooser
  rw [InformationModel.behavioralJoint_eq_pure_of_no_active
    (information first) target trace htargetTerm (by
      intro player
      simp [active]),
    FinDist.pure_bind,
    FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun state => FinDist.pure state.history) (by
      intro state realized
      rw [ExecutionProtocol.runRandomizedFor_zero, FinDist.map_pure]
      rfl)]
  rw [← FinDist.map_eq_bind]
  show FinDist.map (fun state : State first => state.history)
      (resolve first history firstChoice secondChoice hterm) =
    extendSourceLaw history
      (combine first firstChoice secondChoice)
      (combine_legal first hterm firstChoice secondChoice)
  unfold extendSourceLaw extendCertifiedSourceLaw resolve
  rw [FinDist.map_bindOnSupport]
  exact FinDist.bindOnSupport_congr fun reached realized => by
    rw [FinDist.map_pure]
    rfl

theorem map_erase_runBehavioralFrom_afterFirst (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (firstChoice : ChoiceAt history first)
    (trace : (execution first).Trace
      (.afterFirst history firstChoice)) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioralFrom target 2
          ⟨.afterFirst history firstChoice, trace⟩) =
      (target (!first)
        ((information first).infoOf (!first) trace)).bind
        fun choice =>
          extendSourceLaw history
            (combine first firstChoice
              (afterFirstChoiceAt first history hterm firstChoice trace choice))
            (combine_legal first hterm firstChoice
              (afterFirstChoiceAt first history hterm firstChoice trace choice)) := by
  have htargetTerm : ¬ (execution first).terminal
      (.afterFirst history firstChoice) := hterm
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 1 htargetTerm,
    FinDist.map_bind]
  unfold InformationModel.randomizedChooser
  rw [InformationModel.behavioralJoint_eq_map_of_at_most_one_active
    (information first) target trace htargetTerm (!first) (by
      intro player hactive
      exact (show player = !first ∧
        Source.execution.active history.state player from hactive).1),
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro choice hchoice
  refine FinDist.map_bindOnSupport_const _ fun state realized => ?_
  simp [execution] at realized
  subst state
  let secondAt := secondChoiceOfJoint first history firstChoice
    (fun other => if other = !first then choice.1 else none)
    (ExecutionProtocol.legal_of_legalOption htargetTerm (fun other => by
      by_cases howner : other = !first
      · subst other
        simpa using ((information first).menu_adequate (!first) trace
          choice.1).mp choice.2
      · simp [LegalOption, active, howner])).2
  show FinDist.map (eraseHistory first)
      ((information first).runBehavioralFrom target 1
        ⟨.ready history firstChoice secondAt, _⟩) = _
  rw [map_erase_runBehavioralFrom_ready first target history hterm
    firstChoice secondAt]
  have hsecond : secondAt.1 = choice.1 := by
    unfold secondAt secondChoiceOfJoint
    simp
  unfold extendSourceLaw
  apply congrArg (extendCertifiedSourceLaw history)
  apply Subtype.ext
  funext player
  cases first <;> cases player <;>
    simp [combine, hsecond, afterFirstChoiceAt]

theorem map_erase_runBehavioralFrom_afterFirst_eq_choiceAtLaw
    (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (firstChoice : ChoiceAt history first)
    (trace : (execution first).Trace
      (.afterFirst history firstChoice)) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioralFrom target 2
          ⟨.afterFirst history firstChoice, trace⟩) =
      (targetChoiceAtLaw first target history (!first)).bind
        fun secondChoice =>
          extendSourceLaw history
            (combine first firstChoice secondChoice)
            (combine_legal first hterm firstChoice secondChoice) := by
  rw [map_erase_runBehavioralFrom_afterFirst first target history hterm
    firstChoice trace]
  unfold afterFirstChoiceAt
  rw [← map_choiceAtOfViewEq first target history (!first)
    ((information first).infoOf (!first) trace)
    (afterFirst_info_eq_scheduled first history hterm firstChoice trace),
    FinDist.bind_map]

def boundaryChoiceAt (first : Bool)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (trace : (execution first).Trace (.boundary history))
    (choice : (information first).Choice first
      ((information first).infoOf first trace)) :
    ChoiceAt history first :=
  choiceAtOfViewEq first history first
    ((information first).infoOf first trace)
    (boundary_info_eq_scheduled first history hterm trace)
    choice

theorem map_erase_runBehavioralFrom_boundary (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (trace : (execution first).Trace (.boundary history)) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioralFrom target 3
          ⟨.boundary history, trace⟩) =
      (target first ((information first).infoOf first trace)).bind
        fun firstChoice =>
          (targetChoiceAtLaw first target history (!first)).bind
            fun secondChoice =>
              extendSourceLaw history
                (combine first
                  (boundaryChoiceAt first history hterm trace firstChoice)
                  secondChoice)
                (combine_legal first hterm
                  (boundaryChoiceAt first history hterm trace firstChoice)
                  secondChoice) := by
  have htargetTerm : ¬ (execution first).terminal
      (.boundary history) := hterm
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 2 htargetTerm,
    FinDist.map_bind]
  unfold InformationModel.randomizedChooser
  rw [InformationModel.behavioralJoint_eq_map_of_at_most_one_active
    (information first) target trace htargetTerm first (by
      intro player hactive
      exact (show player = first ∧
        Source.execution.active history.state player from hactive).1),
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro choice hchoice
  refine FinDist.map_bindOnSupport_const _ fun state realized => ?_
  simp [execution] at realized
  subst state
  let firstAt := firstChoiceOfJoint first history
    (fun other => if other = first then choice.1 else none)
    (ExecutionProtocol.legal_of_legalOption htargetTerm (fun other => by
      by_cases howner : other = first
      · subst other
        simpa using ((information first).menu_adequate first trace
          choice.1).mp choice.2
      · simp [LegalOption, active, howner])).2
  show FinDist.map (eraseHistory first)
      ((information first).runBehavioralFrom target 2
        ⟨.afterFirst history firstAt, _⟩) = _
  rw [map_erase_runBehavioralFrom_afterFirst_eq_choiceAtLaw
    first target history hterm firstAt]
  apply FinDist.bind_congr
  intro secondChoice _
  have hfirst : firstAt.1 = choice.1 := by
    unfold firstAt firstChoiceOfJoint
    simp
  unfold extendSourceLaw
  apply congrArg (extendCertifiedSourceLaw history)
  apply Subtype.ext
  funext player
  cases first <;> cases player <;>
    simp [combine, hfirst, boundaryChoiceAt]

theorem map_erase_runBehavioralFrom_boundary_eq_choiceAtLaws
    (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (trace : (execution first).Trace (.boundary history)) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioralFrom target 3
          ⟨.boundary history, trace⟩) =
      (targetChoiceAtLaw first target history first).bind
        fun firstChoice =>
          (targetChoiceAtLaw first target history (!first)).bind
            fun secondChoice =>
              extendSourceLaw history
                (combine first firstChoice secondChoice)
                (combine_legal first hterm firstChoice secondChoice) := by
  rw [map_erase_runBehavioralFrom_boundary first target history hterm trace]
  unfold boundaryChoiceAt
  rw [← map_choiceAtOfViewEq first target history first
    ((information first).infoOf first trace)
    (boundary_info_eq_scheduled first history hterm trace),
    FinDist.bind_map]

def sourceChoiceAtLaw
    (policies : (player : Bool) →
      Source.information.BehavioralPolicy player)
    (history : Source.execution.History) (player : Bool) :
    FinDist (ChoiceAt history player) :=
  FinDist.map (sourceChoiceAt history player)
    (policies player
      (Source.information.infoOf player history.trace))

theorem targetChoiceAtLaw_eq_projected (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History) (player : Bool) :
    targetChoiceAtLaw first target history player =
      sourceChoiceAtLaw (projectBehavioral first target) history player := by
  unfold targetChoiceAtLaw sourceChoiceAtLaw projectBehavioral
  rw [FinDist.map_comp]
  rfl

theorem orderedSourceHistoryLaw_eq_choiceAtLaws (first : Bool)
    (policies : (player : Bool) →
      Source.information.BehavioralPolicy player)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state) :
    orderedSourceHistoryLaw first policies history hterm =
      (sourceChoiceAtLaw policies history first).bind
        fun firstChoice =>
          (sourceChoiceAtLaw policies history (!first)).bind
            fun secondChoice =>
              extendSourceLaw history
                (combine first firstChoice secondChoice)
                (combine_legal first hterm firstChoice secondChoice) := by
  unfold orderedSourceHistoryLaw sourceChoiceAtLaw
  rw [FinDist.bind_map]
  apply FinDist.bind_congr
  intro firstChoice _
  rw [FinDist.bind_map]

/-- Three administrative target steps erase to one literal source-history
step for every target behavioral profile, not only for translated profiles. -/
theorem map_erase_runBehavioralFrom_boundary_eq_source (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (trace : (execution first).Trace (.boundary history)) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioralFrom target 3
          ⟨.boundary history, trace⟩) =
      Source.information.runBehavioralFrom
        (projectBehavioral first target) 1 history := by
  rw [map_erase_runBehavioralFrom_boundary_eq_choiceAtLaws
    first target history hterm trace,
    targetChoiceAtLaw_eq_projected,
    targetChoiceAtLaw_eq_projected,
    ← orderedSourceHistoryLaw_eq_choiceAtLaws first
      (projectBehavioral first target) history hterm,
    ← source_runBehavioralFrom_one_eq_ordered first
      (projectBehavioral first target) history hterm]

theorem map_erase_runBehavioralFrom_boundary_eq_source_any (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History)
    (trace : (execution first).Trace (.boundary history)) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioralFrom target 3
          ⟨.boundary history, trace⟩) =
      Source.information.runBehavioralFrom
        (projectBehavioral first target) 1 history := by
  by_cases hterm : Source.execution.terminal history.state
  · have htarget : (execution first).terminal (.boundary history) := hterm
    rw [InformationModel.runBehavioralFrom,
      ExecutionProtocol.runRandomizedFor_of_terminal _ 3 htarget,
      FinDist.map_pure,
      InformationModel.runBehavioralFrom,
      ExecutionProtocol.runRandomizedFor_of_terminal _ 1 hterm]
    rfl
  · exact map_erase_runBehavioralFrom_boundary_eq_source
      first target history hterm trace

theorem runRandomizedFor_add {ι : Type*} (E : ExecutionProtocol ι)
    (chooser : E.RandomizedChooser) (firstFuel secondFuel : ℕ)
    (history : E.History) :
    E.runRandomizedFor chooser (firstFuel + secondFuel) history =
      (E.runRandomizedFor chooser firstFuel history).bind
        (E.runRandomizedFor chooser secondFuel) := by
  induction firstFuel generalizing history with
  | zero => simp [FinDist.pure_bind]
  | succ firstFuel ih =>
      by_cases hterm : E.terminal history.state
      · rw [ExecutionProtocol.runRandomizedFor_of_terminal _ _ hterm,
          ExecutionProtocol.runRandomizedFor_of_terminal _ _ hterm,
          FinDist.pure_bind,
          ExecutionProtocol.runRandomizedFor_of_terminal _ _ hterm]
      · rw [show firstFuel + 1 + secondFuel =
            (firstFuel + secondFuel) + 1 by omega,
          ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
            chooser _ hterm,
          ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
            chooser _ hterm,
          FinDist.bind_bind]
        apply FinDist.bind_congr
        intro draw _
        rw [FinDist.bind_bindOnSupport]
        exact FinDist.bindOnSupport_congr fun reached realized =>
          ih (history.extend draw.2 realized)

theorem runBehavioralFrom_add {ι : Type*} [Fintype ι]
    {E : ExecutionProtocol ι} (model : InformationModel E)
    (policies : (player : ι) → model.BehavioralPolicy player)
    (firstFuel secondFuel : ℕ) (history : E.History) :
    model.runBehavioralFrom policies (firstFuel + secondFuel) history =
      (model.runBehavioralFrom policies firstFuel history).bind
        (model.runBehavioralFrom policies secondFuel) :=
  runRandomizedFor_add E (model.randomizedChooser policies)
    firstFuel secondFuel history

theorem state_of_mem_runBehavioralFrom_one_boundary (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (trace : (execution first).Trace (.boundary history))
    {reached : (execution first).History}
    (hreached : reached ∈
      ((information first).runBehavioralFrom target 1
        ⟨.boundary history, trace⟩).support) :
    ∃ choice : ChoiceAt history first,
      reached.state = .afterFirst history choice := by
  have htargetTerm : ¬ (execution first).terminal (.boundary history) := hterm
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 0 htargetTerm] at hreached
  simp only [FinDist.support_bind, Set.mem_iUnion] at hreached
  obtain ⟨draw, hdraw, hreached⟩ := hreached
  simp only [FinDist.support_bindOnSupport, Set.mem_iUnion] at hreached
  obtain ⟨state, hstate, hreached⟩ := hreached
  rw [ExecutionProtocol.runRandomizedFor_zero,
    FinDist.mem_support_pure] at hreached
  subst reached
  rw [FinDist.mem_support_pure] at hstate
  subst state
  exact ⟨firstChoiceOfJoint first history draw.1 draw.2.2, rfl⟩

theorem state_of_mem_runBehavioralFrom_one_afterFirst (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (firstChoice : ChoiceAt history first)
    (trace : (execution first).Trace (.afterFirst history firstChoice))
    {reached : (execution first).History}
    (hreached : reached ∈
      ((information first).runBehavioralFrom target 1
        ⟨.afterFirst history firstChoice, trace⟩).support) :
    ∃ choice : ChoiceAt history (!first),
      reached.state = .ready history firstChoice choice := by
  have htargetTerm : ¬ (execution first).terminal
      (.afterFirst history firstChoice) := hterm
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 0 htargetTerm] at hreached
  simp only [FinDist.support_bind, Set.mem_iUnion] at hreached
  obtain ⟨draw, hdraw, hreached⟩ := hreached
  simp only [FinDist.support_bindOnSupport, Set.mem_iUnion] at hreached
  obtain ⟨state, hstate, hreached⟩ := hreached
  rw [ExecutionProtocol.runRandomizedFor_zero,
    FinDist.mem_support_pure] at hreached
  subst reached
  rw [FinDist.mem_support_pure] at hstate
  subst state
  exact ⟨secondChoiceOfJoint first history firstChoice
    draw.1 draw.2.2, rfl⟩

theorem state_of_mem_runBehavioralFrom_one_ready (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (firstChoice : ChoiceAt history first)
    (secondChoice : ChoiceAt history (!first))
    (trace : (execution first).Trace
      (.ready history firstChoice secondChoice))
    {reached : (execution first).History}
    (hreached : reached ∈
      ((information first).runBehavioralFrom target 1
        ⟨.ready history firstChoice secondChoice, trace⟩).support) :
    ∃ sourceHistory : Source.execution.History,
      reached.state = .boundary sourceHistory := by
  have htargetTerm : ¬ (execution first).terminal
      (.ready history firstChoice secondChoice) := hterm
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 0 htargetTerm] at hreached
  simp only [FinDist.support_bind, Set.mem_iUnion] at hreached
  obtain ⟨draw, hdraw, hreached⟩ := hreached
  simp only [FinDist.support_bindOnSupport, Set.mem_iUnion] at hreached
  obtain ⟨state, hstate, hreached⟩ := hreached
  rw [ExecutionProtocol.runRandomizedFor_zero,
    FinDist.mem_support_pure] at hreached
  subst reached
  rw [mem_support_resolve_iff] at hstate
  obtain ⟨sourceState, realized, rfl⟩ := hstate
  exact ⟨history.extend
    (combine_legal first hterm firstChoice secondChoice) realized, rfl⟩

theorem state_of_mem_runBehavioralFrom_three_boundary (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (trace : (execution first).Trace (.boundary history))
    {reached : (execution first).History}
    (hreached : reached ∈
      ((information first).runBehavioralFrom target 3
        ⟨.boundary history, trace⟩).support) :
    ∃ sourceHistory : Source.execution.History,
      reached.state = .boundary sourceHistory := by
  unfold InformationModel.runBehavioralFrom at hreached
  rw [show 3 = 1 + 2 by norm_num,
    runRandomizedFor_add] at hreached
  simp only [FinDist.support_bind, Set.mem_iUnion] at hreached
  obtain ⟨middle1, hmiddle1, hreached⟩ := hreached
  have hmiddle1' : middle1 ∈
      ((information first).runBehavioralFrom target 1
        ⟨.boundary history, trace⟩).support := hmiddle1
  obtain ⟨firstChoice, hmiddle1State⟩ :=
    state_of_mem_runBehavioralFrom_one_boundary first target history
      hterm trace hmiddle1'
  rcases middle1 with ⟨middle1State, middle1Trace⟩
  have hmiddle1State' :
      middle1State = .afterFirst history firstChoice := hmiddle1State
  subst middle1State
  rw [show 2 = 1 + 1 by norm_num,
    runRandomizedFor_add] at hreached
  simp only [FinDist.support_bind, Set.mem_iUnion] at hreached
  obtain ⟨middle2, hmiddle2, hreached⟩ := hreached
  have hmiddle2' : middle2 ∈
      ((information first).runBehavioralFrom target 1
        ⟨.afterFirst history firstChoice, middle1Trace⟩).support := hmiddle2
  obtain ⟨secondChoice, hmiddle2State⟩ :=
    state_of_mem_runBehavioralFrom_one_afterFirst first target history
      hterm firstChoice middle1Trace hmiddle2'
  rcases middle2 with ⟨middle2State, middle2Trace⟩
  have hmiddle2State' :
      middle2State = .ready history firstChoice secondChoice := hmiddle2State
  subst middle2State
  have hreached' : reached ∈
      ((information first).runBehavioralFrom target 1
        ⟨.ready history firstChoice secondChoice, middle2Trace⟩).support
      := hreached
  exact state_of_mem_runBehavioralFrom_one_ready first target history
    hterm firstChoice secondChoice middle2Trace hreached'

/-- Six literal target microsteps carry exactly the same complete-history law
as the two source rounds, for every target behavioral profile. -/
theorem map_erase_runBehavioral_eq_source (first : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioral target 6) =
      Source.information.runBehavioral
        (projectBehavioral first target) 2 := by
  let sourcePolicies := projectBehavioral first target
  have hsourceStart : ¬ Source.execution.terminal
      Source.execution.initHistory.state := by
    simp [Source.execution, Source.terminal]
  have hfirstLaw :
      FinDist.map (eraseHistory first)
          ((information first).runBehavioralFrom target 3
            (execution first).initHistory) =
        Source.information.runBehavioralFrom sourcePolicies 1
          Source.execution.initHistory := by
    exact map_erase_runBehavioralFrom_boundary_eq_source
      first target Source.execution.initHistory hsourceStart
        (execution first).initHistory.trace
  unfold InformationModel.runBehavioral
  rw [show 6 = 3 + 3 by norm_num,
    runBehavioralFrom_add,
    FinDist.map_bind]
  calc
    _ = ((information first).runBehavioralFrom target 3
          (execution first).initHistory).bind
        (fun middle =>
          Source.information.runBehavioralFrom sourcePolicies 1
            (eraseHistory first middle)) := by
      apply FinDist.bind_congr
      intro middle hmiddle
      have hboundary := state_of_mem_runBehavioralFrom_three_boundary
        first target Source.execution.initHistory hsourceStart
          (execution first).initHistory.trace hmiddle
      obtain ⟨sourceHistory, hstate⟩ := hboundary
      rcases middle with ⟨middleState, middleTrace⟩
      have hstate' : middleState = .boundary sourceHistory := hstate
      subst middleState
      exact map_erase_runBehavioralFrom_boundary_eq_source_any
        first target sourceHistory middleTrace
    _ = (FinDist.map (eraseHistory first)
          ((information first).runBehavioralFrom target 3
            (execution first).initHistory)).bind
        (Source.information.runBehavioralFrom sourcePolicies 1) := by
      rw [FinDist.bind_map]
    _ = (Source.information.runBehavioralFrom sourcePolicies 1
          Source.execution.initHistory).bind
        (Source.information.runBehavioralFrom sourcePolicies 1) := by
      rw [hfirstLaw]
    _ = Source.information.runBehavioralFrom sourcePolicies 2
          Source.execution.initHistory := by
      rw [show 2 = 1 + 1 by norm_num, runBehavioralFrom_add]

theorem project_translate_profile (first : Bool)
    (source : (player : Bool) →
      Source.information.BehavioralPolicy player) :
    projectBehavioral first (translateBehavioral first source) = source := by
  funext player sourceView
  exact project_translate first player sourceView source

/-- Forward translation preserves the complete two-round history law. -/
theorem map_erase_runBehavioral_translate (first : Bool)
    (source : (player : Bool) →
      Source.information.BehavioralPolicy player) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioral
          (translateBehavioral first source) 6) =
      Source.information.runBehavioral source 2 := by
  rw [map_erase_runBehavioral_eq_source,
    project_translate_profile]

/-- Either fixed player order serializes a translated profile to the same
literal source-history law. -/
theorem map_erase_runBehavioral_order_independent
    (source : (player : Bool) →
      Source.information.BehavioralPolicy player) :
    FinDist.map (eraseHistory false)
        ((information false).runBehavioral
          (translateBehavioral false source) 6) =
      FinDist.map (eraseHistory true)
        ((information true).runBehavioral
          (translateBehavioral true source) 6) := by
  rw [map_erase_runBehavioral_translate,
    map_erase_runBehavioral_translate]

/-- An arbitrary target profile in one order transports through its projected
source profile to the opposite order without changing the erased history law. -/
theorem map_erase_runBehavioral_arbitrary_order_transport
    (first second : Bool)
    (target : (player : Bool) →
      (information first).BehavioralPolicy player) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioral target 6) =
      FinDist.map (eraseHistory second)
        ((information second).runBehavioral
          (translateBehavioral second (projectBehavioral first target)) 6) := by
  rw [map_erase_runBehavioral_eq_source,
    map_erase_runBehavioral_translate]

end Serial

end GameTheory.Experimental.FOSGToEFGTwoRound
