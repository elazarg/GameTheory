/-
# EXP-059: hostile simultaneous stochastic serialization

This file tests one semantic question before any generic bridge is promoted:
can a single-mover EFG serialize a simultaneous stochastic FOSG without
letting a later mover observe an earlier choice?  The target state retains the
full decision prefix so tree shape is real; its information model hides that
prefix until the source transition resolves.
-/

import GameTheory.Languages.EFG
import GameTheory.Languages.FOSG

noncomputable section

namespace GameTheory.Experimental.FOSGToEFG

open GameTheory.Languages GameTheory.Probability GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol

abbrev Outcome := Bool × Bool × Bool

def independentOutcomeLaw (resolution left right : FinDist Bool) : FinDist Outcome :=
  (FinDist.product left right).bind fun actions =>
    FinDist.map (fun coin => (actions.1, actions.2, coin)) resolution

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
  have hpair : (assignment false, assignment true) = pair := by
    rfl
  rw [← hpair, FinDist.prob_map_of_injective]
  · rw [FinDist.prob_pi, FinDist.prob_product, Fintype.prod_bool]
    simp [mul_comm]
  · intro first second hequal
    funext index
    cases index with
    | false => exact congrArg Prod.fst hequal
    | true => exact congrArg Prod.snd hequal

/-! ## Source simultaneous stochastic FOSG -/

namespace Source

inductive State
  | start
  | terminal (left right coin : Bool)
  deriving DecidableEq

def State.isTerminal : State → Bool
  | .start => false
  | .terminal .. => true

def coin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

theorem mem_support_coin (value : Bool) : value ∈ coin.support := by
  refine FinDist.prob_pos_iff.mp ?_
  cases value <;> norm_num [coin, FinDist.prob_pure_eq_ite]

private def actionAt
    (joint : (i : Bool) → Option Bool)
    (hlegal : IsLegalJoint (fun _ => True) (fun _ => Set.univ) joint)
    (i : Bool) : Bool :=
  match hchoice : joint i with
  | some action => action
  | none => False.elim (by
      have hi := hlegal i
      rw [hchoice] at hi
      exact hi trivial)

@[simp]
private theorem actionAt_some (actions : Bool → Bool)
    (hlegal : IsLegalJoint (fun _ => True) (fun _ => Set.univ)
      (fun i => some (actions i))) (i : Bool) :
    actionAt (fun i => some (actions i)) hlegal i = actions i :=
  rfl

@[reducible]
def execution : ExecutionProtocol Bool where
  State := State
  Action _ := Bool
  init := .start
  active state _ :=
    match state with
    | .start => True
    | .terminal .. => False
  available _ _ := Set.univ
  terminal state := state.isTerminal = true
  step state joint :=
    match state with
    | .start =>
        FinDist.map
          (State.terminal
            (actionAt joint.1 joint.2.2 false)
            (actionAt joint.1 joint.2.2 true)) coin
    | .terminal .. => False.elim (joint.2.1 rfl)
  progress := by
    intro state hterm
    cases state with
    | start =>
        refine ⟨fun _ => some false, fun _ => ?_⟩
        exact ⟨trivial, Set.mem_univ _⟩
    | terminal left right value => exact False.elim (hterm rfl)

inductive View
  | acting
  | done
  deriving DecidableEq

def viewOfState : State → View
  | .start => .acting
  | .terminal .. => .done

@[reducible]
def signals : InfoSignals execution where
  PublicSignal := View
  PrivateSignal _ := Unit
  initialPublic := .acting
  initialPrivate _ := ()
  publicSignal event := viewOfState event.target
  privateSignal _ _ := ()
  InfoState _ := View
  initInfo _ _ announced := announced
  pushInfo _ _ _ _ announced := announced

theorem infoOf_eq_viewOfState (i : Bool) :
    ∀ {state : State} (trace : execution.Trace state),
      signals.infoOf i trace = viewOfState state
  | _, .start => rfl
  | _, .extend prior joint isLegal realized => by
      rw [InfoSignals.infoOf_extend]

def menu : View → Set (Option Bool)
  | .acting => Set.range some
  | .done => {none}

theorem menu_adequate (i : Bool) {state : State}
    (trace : execution.Trace state) (choice : Option Bool) :
    choice ∈ menu (signals.infoOf i trace) ↔
      LegalOption execution state i choice := by
  rw [infoOf_eq_viewOfState i trace]
  cases state with
  | start =>
      cases choice with
      | none => simp [menu, viewOfState, LegalOption]
      | some action => cases action <;>
          simp [menu, viewOfState, LegalOption]
  | terminal left right value =>
      cases choice <;> simp [menu, viewOfState, LegalOption]

@[reducible]
def information : InformationModel execution where
  toInfoSignals := signals
  menu _ := menu
  menu_adequate := menu_adequate

@[reducible]
def game : FOSG.Game Bool where
  execution := execution
  information := information

def actionOfChoice {player : Bool}
    (choice : information.Choice player .acting) : Bool :=
  choice.1.getD false

def actionLaw
    (policies : (player : Bool) → information.BehavioralPolicy player)
    (player : Bool) : FinDist Bool :=
  FinDist.map actionOfChoice (policies player .acting)

theorem start_not_terminal : ¬ execution.terminal .start := by
  simp [State.isTerminal]

theorem map_behavioralJoint_start
    (policies : (player : Bool) → information.BehavioralPolicy player) :
    FinDist.map
        (fun joint =>
          ((joint.1 false).getD false, (joint.1 true).getD false))
        (information.behavioralJoint policies
          (.start : execution.Trace .start) start_not_terminal) =
      FinDist.product (actionLaw policies false)
        (actionLaw policies true) := by
  unfold InformationModel.behavioralJoint actionLaw
  rw [FinDist.map_comp]
  show FinDist.map
      ((fun pair => (actionOfChoice pair.1, actionOfChoice pair.2)) ∘
        fun draws => (draws false, draws true))
      (FinDist.pi fun player => policies player .acting) = _
  rw [← FinDist.map_comp, map_pi_bool]
  show FinDist.map (Prod.map actionOfChoice actionOfChoice)
      (FinDist.product (policies false .acting) (policies true .acting)) = _
  rw [FinDist.map_product]

def outcomeOfState : State → Outcome
  | .start => (false, false, false)
  | .terminal left right coinValue => (left, right, coinValue)

def oneRoundOutcomeLaw
    (policies : (player : Bool) → information.BehavioralPolicy player) :
    FinDist Outcome :=
  FinDist.map outcomeOfState <|
    (information.behavioralJoint policies
      (.start : execution.Trace .start)
      start_not_terminal).bind fun joint =>
        execution.step .start joint

theorem actionAt_eq_getD
    (joint : (player : Bool) → Option Bool)
    (hlegal : IsLegalJoint (fun _ : Bool => True) (fun _ => Set.univ) joint)
    (player : Bool) :
    actionAt joint hlegal player = (joint player).getD false := by
  unfold actionAt
  split
  next action hsome => simp [hsome]
  next hnone =>
    have hplayer := hlegal player
    rw [hnone] at hplayer
    exact False.elim (hplayer trivial)

theorem joint_eq_some_actionAt
    (joint : (player : Bool) → Option Bool)
    (hlegal : IsLegalJoint (fun _ : Bool => True) (fun _ => Set.univ) joint) :
    joint = fun player => some (actionAt joint hlegal player) := by
  funext player
  unfold actionAt
  split
  next action hsome => exact hsome
  next hnone =>
    have hplayer := hlegal player
    rw [hnone] at hplayer
    exact False.elim (hplayer trivial)

def predecessor : State → Option State
  | .start => none
  | .terminal .. => some .start

theorem source_eq_predecessor_of_mem_step
    (source target : State)
    (certified : {joint : Bool → Option Bool // execution.Legal source joint})
    (realized : target ∈ (execution.step source certified).support) :
    some source = predecessor target := by
  cases source with
  | start =>
      cases target <;>
        simp [execution, predecessor, FinDist.support_map] at realized ⊢
  | terminal left right coinValue =>
      exact False.elim (certified.2.1 rfl)

theorem start_not_mem_step (source : State)
    (certified : {joint : Bool → Option Bool // execution.Legal source joint}) :
    State.start ∉ (execution.step source certified).support := by
  intro realized
  have hpredecessor :=
    source_eq_predecessor_of_mem_step source .start certified realized
  simp [predecessor] at hpredecessor

theorem joint_eq_of_same_source_target
    {source target : State}
    {firstJoint secondJoint : Bool → Option Bool}
    (firstLegal : execution.Legal source firstJoint)
    (secondLegal : execution.Legal source secondJoint)
    (firstRealized : target ∈
      (execution.step source ⟨firstJoint, firstLegal⟩).support)
    (secondRealized : target ∈
      (execution.step source ⟨secondJoint, secondLegal⟩).support) :
    firstJoint = secondJoint := by
  cases source with
  | terminal left right coinValue =>
      exact False.elim (firstLegal.1 rfl)
  | start =>
      cases target with
      | start =>
          exact False.elim
            (start_not_mem_step .start ⟨firstJoint, firstLegal⟩ firstRealized)
      | terminal left right coinValue =>
          have firstImage : State.terminal left right coinValue ∈
              (FinDist.map
                (State.terminal
                  (actionAt firstJoint firstLegal.2 false)
                  (actionAt firstJoint firstLegal.2 true)) coin).support :=
            firstRealized
          have secondImage : State.terminal left right coinValue ∈
              (FinDist.map
                (State.terminal
                  (actionAt secondJoint secondLegal.2 false)
                  (actionAt secondJoint secondLegal.2 true)) coin).support :=
            secondRealized
          rw [FinDist.support_map] at firstImage secondImage
          obtain ⟨firstCoin, hfirstCoin, hfirstState⟩ := firstImage
          obtain ⟨secondCoin, hsecondCoin, hsecondState⟩ := secondImage
          have hstates := hfirstState.trans hsecondState.symm
          have hfields := State.terminal.inj hstates
          rw [joint_eq_some_actionAt firstJoint firstLegal.2,
            joint_eq_some_actionAt secondJoint secondLegal.2]
          funext player
          congr 1
          cases player with
          | false => exact hfields.1
          | true => exact hfields.2.1

theorem step_predecessor_unique
    {target firstSource secondSource : State}
    {firstJoint secondJoint : Bool → Option Bool}
    (firstLegal : execution.Legal firstSource firstJoint)
    (secondLegal : execution.Legal secondSource secondJoint)
    (firstRealized : target ∈
      (execution.step firstSource ⟨firstJoint, firstLegal⟩).support)
    (secondRealized : target ∈
      (execution.step secondSource ⟨secondJoint, secondLegal⟩).support) :
    firstSource = secondSource ∧ firstJoint = secondJoint := by
  have hfirst := source_eq_predecessor_of_mem_step firstSource target
    ⟨firstJoint, firstLegal⟩ firstRealized
  have hsecond := source_eq_predecessor_of_mem_step secondSource target
    ⟨secondJoint, secondLegal⟩ secondRealized
  have hsource : firstSource = secondSource :=
    Option.some.inj (hfirst.trans hsecond.symm)
  subst secondSource
  exact ⟨rfl, joint_eq_of_same_source_target firstLegal secondLegal
    firstRealized secondRealized⟩

theorem trace_unique :
    ∀ {state : State} (one two : execution.Trace state), one = two
  | _, .start, .start => rfl
  | _, .start, .extend prior joint isLegal realized =>
      False.elim (start_not_mem_step _ ⟨joint, isLegal⟩ realized)
  | _, .extend prior joint isLegal realized, .start =>
      False.elim (start_not_mem_step _ ⟨joint, isLegal⟩ realized)
  | _, .extend prior joint isLegal realized,
      .extend secondPrior secondJoint secondLegal secondRealized => by
      obtain ⟨rfl, hjoint⟩ :=
        step_predecessor_unique isLegal secondLegal realized secondRealized
      subst secondJoint
      have hprior := trace_unique prior secondPrior
      subst secondPrior
      rfl
termination_by _ one _ => one.length
decreasing_by simp [ExecutionProtocol.Trace.length]

theorem treeShaped : execution.IsTreeShaped :=
  fun _ => ⟨trace_unique⟩

def simultaneousJoint (left right : Bool) : Bool → Option Bool :=
  fun player => some (if player then right else left)

theorem simultaneousJoint_legal (left right : Bool) :
    execution.Legal .start (simultaneousJoint left right) := by
  refine ⟨by simp [State.isTerminal], fun player => ?_⟩
  cases player <;> simp [simultaneousJoint]

def historyOfOutcome : Outcome → execution.History
  | (left, right, coinValue) =>
      ⟨.terminal left right coinValue,
        .extend .start (simultaneousJoint left right)
          (simultaneousJoint_legal left right) (by
            show State.terminal left right coinValue ∈
              (FinDist.map
                (State.terminal
                  (actionAt (simultaneousJoint left right)
                    (simultaneousJoint_legal left right).2 false)
                  (actionAt (simultaneousJoint left right)
                    (simultaneousJoint_legal left right).2 true)) coin).support
            have hleft : actionAt (simultaneousJoint left right)
                (simultaneousJoint_legal left right).2 false = left :=
              actionAt_some
                (fun player => if player then right else left)
                (simultaneousJoint_legal left right).2 false
            have hright : actionAt (simultaneousJoint left right)
                (simultaneousJoint_legal left right).2 true = right :=
              actionAt_some
                (fun player => if player then right else left)
                (simultaneousJoint_legal left right).2 true
            rw [hleft, hright, FinDist.support_map]
            exact ⟨coinValue, mem_support_coin coinValue, rfl⟩)⟩

@[simp]
theorem historyOfOutcome_state (outcome : Outcome) :
    (historyOfOutcome outcome).state =
      .terminal outcome.1 outcome.2.1 outcome.2.2 := by
  rcases outcome with ⟨left, right, coinValue⟩
  rfl

theorem history_state_injective :
    Function.Injective (fun history : execution.History => history.state) := by
  intro first second hequal
  rcases first with ⟨firstState, firstTrace⟩
  rcases second with ⟨secondState, secondTrace⟩
  simp only at hequal
  subst secondState
  congr
  exact trace_unique firstTrace secondTrace

theorem map_historyOfOutcome_oneRoundOutcomeLaw
    (policies : (player : Bool) → information.BehavioralPolicy player) :
    FinDist.map historyOfOutcome (oneRoundOutcomeLaw policies) =
      information.runBehavioral policies 1 := by
  unfold oneRoundOutcomeLaw InformationModel.runBehavioral
  have hterminal : ¬ execution.terminal execution.initHistory.state :=
    start_not_terminal
  rw [FinDist.map_comp, FinDist.map_bind,
    InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 0 hterminal]
  unfold InformationModel.randomizedChooser
  apply FinDist.bind_congr
  intro joint hjoint
  rw [FinDist.map_comp]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun state =>
      FinDist.pure (historyOfOutcome (outcomeOfState state))) (by
      intro state realized
      rw [ExecutionProtocol.runRandomizedFor_zero]
      apply congrArg FinDist.pure
      apply history_state_injective
      cases state with
      | start =>
          exact False.elim (start_not_mem_step .start joint realized)
      | terminal left right coinValue => rfl)]
  rw [← FinDist.map_eq_bind]
  show FinDist.map
      ((historyOfOutcome ∘ outcomeOfState) ∘
        State.terminal
          (actionAt joint.1 joint.2.2 false)
          (actionAt joint.1 joint.2.2 true)) coin =
    FinDist.map (fun state => historyOfOutcome (outcomeOfState state))
      (FinDist.map
        (State.terminal
          (actionAt joint.1 joint.2.2 false)
          (actionAt joint.1 joint.2.2 true)) coin)
  rw [FinDist.map_comp]
  apply congrArg (fun function : Bool → execution.History =>
    FinDist.map function coin)
  funext coinValue
  rfl

theorem oneRoundOutcomeLaw_eq_independent
    (policies : (player : Bool) → information.BehavioralPolicy player) :
    oneRoundOutcomeLaw policies =
      independentOutcomeLaw coin (actionLaw policies false)
        (actionLaw policies true) := by
  unfold oneRoundOutcomeLaw independentOutcomeLaw
  rw [FinDist.map_bind]
  show (information.behavioralJoint policies
      (.start : execution.Trace .start)
      start_not_terminal).bind
      (fun joint => FinDist.map outcomeOfState
        (FinDist.map
          (State.terminal (actionAt joint.1 joint.2.2 false)
            (actionAt joint.1 joint.2.2 true)) coin)) = _
  simp_rw [FinDist.map_comp]
  simp_rw [show outcomeOfState ∘
      State.terminal (actionAt _ _ false) (actionAt _ _ true) =
        fun coinValue =>
          (actionAt _ _ false, actionAt _ _ true, coinValue) by rfl]
  simp_rw [actionAt_eq_getD]
  calc
    _ = (FinDist.map
          (fun joint =>
            ((joint.1 false).getD false, (joint.1 true).getD false))
          (information.behavioralJoint policies
            (.start : execution.Trace .start)
            start_not_terminal)).bind
          (fun actions => FinDist.map
            (fun coinValue => (actions.1, actions.2, coinValue)) coin) := by
        rw [FinDist.bind_map]
    _ = _ := by rw [map_behavioralJoint_start]

def runOutcomeLaw
    (policies : (player : Bool) → information.BehavioralPolicy player) :
    FinDist Outcome :=
  FinDist.map (fun history => outcomeOfState history.state)
    (information.runBehavioral policies 1)

/-- The source one-round law is the mapped law of the canonical Protocol
behavioral runner, not a parallel execution semantics. -/
theorem runOutcomeLaw_eq_oneRound
    (policies : (player : Bool) → information.BehavioralPolicy player) :
    runOutcomeLaw policies = oneRoundOutcomeLaw policies := by
  unfold runOutcomeLaw InformationModel.runBehavioral
  have hterminal : ¬ execution.terminal execution.initHistory.state := by
    simp [State.isTerminal]
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 0 hterminal,
    FinDist.map_bind]
  unfold InformationModel.randomizedChooser oneRoundOutcomeLaw
  rw [FinDist.map_bind]
  apply FinDist.bind_congr
  intro joint hjoint
  rw [FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun state => FinDist.pure (outcomeOfState state)) (by
      intro state realized
      rw [ExecutionProtocol.runRandomizedFor_zero, FinDist.map_pure]
      rfl)]
  rw [← FinDist.map_eq_bind]
  rfl

end Source

/-! ## Ordered single-mover presentation -/

namespace Serial

/-- The concrete state retains every serialized joint action.  Information
will hide these fields, but retaining them gives every reachable state a unique
predecessor and prevents tree shape from being asserted by erasure. -/
inductive State
  | root
  | afterFirst (firstJoint : Bool → Option Bool)
  | ready (firstJoint secondJoint : Bool → Option Bool)
  | terminal (firstJoint secondJoint resolutionJoint : Bool → Option Bool)
      (coin : Bool)

def active (first : Bool) : State → Bool → Prop
  | .root, player => player = first
  | .afterFirst _, player => player = !first
  | .ready .., _ => False
  | .terminal .., _ => False

def terminal : State → Prop
  | .terminal .. => True
  | _ => False

def onlyMove (who action : Bool) : Bool → Option Bool :=
  fun player => if player = who then some action else none

private def actionAt
    (first : Bool) (state : State)
    (joint : (i : Bool) → Option Bool)
    (hlegal : IsLegalJoint (active first state) (fun _ => Set.univ) joint)
    (who : Bool) (hactive : active first state who) : Bool :=
  match hchoice : joint who with
  | some action => action
  | none => False.elim (by
      have hwho := hlegal who
      rw [hchoice] at hwho
      exact hwho hactive)

@[reducible]
def execution (first : Bool) : ExecutionProtocol Bool where
  State := State
  Action _ := Bool
  init := .root
  active := active first
  available _ _ := Set.univ
  terminal := terminal
  step state joint :=
    match state with
    | .root => FinDist.pure (.afterFirst joint.1)
    | .afterFirst firstJoint =>
        FinDist.pure (.ready firstJoint joint.1)
    | .ready firstJoint secondJoint =>
        FinDist.map (.terminal firstJoint secondJoint joint.1) Source.coin
    | .terminal .. => False.elim (joint.2.1 trivial)
  progress := by
    intro state hterm
    cases state with
    | root =>
        refine ⟨onlyMove first false, fun player => ?_⟩
        by_cases hplayer : player = first
        · subst player
          simp [onlyMove, active]
        · simp [onlyMove, active, hplayer]
    | afterFirst firstJoint =>
        refine ⟨onlyMove (!first) false, fun player => ?_⟩
        by_cases hplayer : player = !first
        · subst player
          simp [onlyMove, active]
        · simp [onlyMove, active, hplayer]
    | ready firstJoint secondJoint =>
        exact ⟨fun _ => none, fun _ => by simp [active]⟩
    | terminal firstJoint secondJoint resolutionJoint value =>
        exact False.elim (hterm trivial)

theorem inactive_ready (first : Bool) (firstJoint secondJoint : Bool → Option Bool)
    (player : Bool) :
    ¬ (execution first).active (.ready firstJoint secondJoint) player := by
  simp [active]

theorem singleMover (first : Bool) (state : State) {one two : Bool}
    (hone : (execution first).active state one)
    (htwo : (execution first).active state two) : one = two := by
  cases state with
  | root => exact hone.trans htwo.symm
  | afterFirst firstJoint => exact hone.trans htwo.symm
  | ready firstJoint secondJoint => exact False.elim hone
  | terminal firstJoint secondJoint resolutionJoint value =>
      exact False.elim hone

def predecessor : State → Option State
  | .root => none
  | .afterFirst _ => some .root
  | .ready firstJoint _ => some (.afterFirst firstJoint)
  | .terminal firstJoint secondJoint _ _ =>
      some (.ready firstJoint secondJoint)

theorem source_eq_predecessor_of_mem_step (first : Bool)
    (source target : State)
    (certified :
      { joint : Bool → Option Bool //
        (execution first).Legal source joint })
    (realized : target ∈
      ((execution first).step source certified).support) :
    some source = predecessor target := by
  cases source <;> cases target <;>
    simp [ExecutionProtocol.Legal, execution, terminal, predecessor,
      FinDist.support_map] at certified realized ⊢ <;> aesop

theorem joint_eq_of_same_source_target (first : Bool)
    {source target : State}
    {firstJoint secondJoint : Bool → Option Bool}
    (firstLegal : (execution first).Legal source firstJoint)
    (secondLegal : (execution first).Legal source secondJoint)
    (firstRealized : target ∈
      ((execution first).step source ⟨firstJoint, firstLegal⟩).support)
    (secondRealized : target ∈
      ((execution first).step source ⟨secondJoint, secondLegal⟩).support) :
    firstJoint = secondJoint := by
  cases source with
  | root =>
      cases target <;>
        simp [execution] at firstRealized secondRealized ⊢
      all_goals aesop
  | afterFirst storedFirst =>
      cases target <;>
        simp [execution] at firstRealized secondRealized ⊢
      all_goals aesop
  | ready storedFirst storedSecond =>
      cases target <;>
        simp [execution] at firstRealized secondRealized ⊢
      all_goals aesop
  | terminal storedFirst storedSecond storedResolution value =>
      exact False.elim (firstLegal.1 trivial)

theorem root_not_mem_step (first : Bool) (source : State)
    (certified :
      { joint : Bool → Option Bool //
        (execution first).Legal source joint }) :
    State.root ∉ ((execution first).step source certified).support := by
  intro realized
  have hpredecessor :=
    source_eq_predecessor_of_mem_step first source .root certified realized
  simp [predecessor] at hpredecessor

theorem step_predecessor_unique (first : Bool)
    {target firstSource secondSource : State}
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
  have hsource : firstSource = secondSource := Option.some.inj (hfirst.trans hsecond.symm)
  subst secondSource
  exact ⟨rfl, joint_eq_of_same_source_target first firstLegal secondLegal
    firstRealized secondRealized⟩

theorem trace_unique (first : Bool) :
    ∀ {state : State}
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

/-! The serialized state remembers the concrete prefix for tree shape, while
the information state exposes only the current serialization phase. -/

inductive View
  | firstTurn
  | secondTurn
  | resolving
  | done
  deriving DecidableEq

def viewOfState : State → View
  | .root => .firstTurn
  | .afterFirst _ => .secondTurn
  | .ready .. => .resolving
  | .terminal .. => .done

@[reducible]
def signals (first : Bool) : InfoSignals (execution first) where
  PublicSignal := View
  PrivateSignal _ := Unit
  initialPublic := .firstTurn
  initialPrivate _ := ()
  publicSignal event := viewOfState event.target
  privateSignal _ _ := ()
  InfoState _ := View
  initInfo _ _ announced := announced
  pushInfo _ _ _ _ announced := announced

theorem infoOf_eq_viewOfState (first player : Bool) :
    ∀ {state : State} (trace : (execution first).Trace state),
      (signals first).infoOf player trace = viewOfState state
  | _, .start => rfl
  | _, .extend prior joint isLegal realized => by
      rw [InfoSignals.infoOf_extend]

def menu (first player : Bool) : View → Set (Option Bool)
  | .firstTurn =>
      if player = first then Set.range some else {none}
  | .secondTurn =>
      if player = !first then Set.range some else {none}
  | .resolving => {none}
  | .done => {none}

theorem menu_adequate (first player : Bool) {state : State}
    (trace : (execution first).Trace state) (choice : Option Bool) :
    choice ∈ menu first player ((signals first).infoOf player trace) ↔
      LegalOption (execution first) state player choice := by
  rw [infoOf_eq_viewOfState first player trace]
  cases state with
  | root =>
      by_cases hplayer : player = first
      · subst player
        cases choice with
        | none => simp [menu, viewOfState, LegalOption, active]
        | some action => cases action <;>
            simp [menu, viewOfState, LegalOption, active]
      · cases choice with
        | none => simp [menu, viewOfState, LegalOption, active, hplayer]
        | some action => cases action <;>
            simp [menu, viewOfState, LegalOption, active, hplayer]
  | afterFirst firstJoint =>
      by_cases hplayer : player = !first
      · cases choice with
        | none => simp [menu, viewOfState, LegalOption, active, hplayer]
        | some action => cases action <;>
            simp [menu, viewOfState, LegalOption, active, hplayer]
      · cases choice with
        | none => simp [menu, viewOfState, LegalOption, active, hplayer]
        | some action => cases action <;>
            simp [menu, viewOfState, LegalOption, active, hplayer]
  | ready firstJoint secondJoint =>
      cases choice <;> simp [menu, viewOfState, LegalOption, active]
  | terminal firstJoint secondJoint resolutionJoint value =>
      cases choice <;> simp [menu, viewOfState, LegalOption, active]

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

theorem firstMoveLegal (first action : Bool) :
    (execution first).Legal .root (onlyMove first action) := by
  refine ⟨by simp [terminal], fun player => ?_⟩
  by_cases hplayer : player = first
  · subst player
    simp [onlyMove, active]
  · simp [onlyMove, active, hplayer]

def afterFirstTrace (first action : Bool) :
    (execution first).Trace (.afterFirst (onlyMove first action)) :=
  .extend .start (onlyMove first action) (firstMoveLegal first action) (by
    simp [execution])

/-- The second mover receives exactly the same information after either first
action, even though the underlying reached states retain different prefixes. -/
theorem second_info_hides_first (first : Bool) :
    (information first).infoOf (!first) (afterFirstTrace first false) =
      (information first).infoOf (!first) (afterFirstTrace first true) := by
  rw [infoOf_eq_viewOfState, infoOf_eq_viewOfState]
  rfl

theorem afterFirst_states_distinct (first : Bool) :
    State.afterFirst (onlyMove first false) ≠
      State.afterFirst (onlyMove first true) := by
  intro hequal
  have hjoint := State.afterFirst.inj hequal
  have hat := congrFun hjoint first
  simp [onlyMove] at hat

def outcomeOfState (first : Bool) : State → Option Outcome
  | .terminal firstJoint secondJoint _ coin =>
      let firstAction := (firstJoint first).getD false
      let secondAction := (secondJoint (!first)).getD false
      if first then some (secondAction, firstAction, coin)
      else some (firstAction, secondAction, coin)
  | _ => none

@[simp]
theorem outcomeOfState_ordered (first left right coinValue : Bool) :
    outcomeOfState first
        (.terminal
          (onlyMove first (if first then right else left))
          (onlyMove (!first) (if first then left else right))
          (fun _ => none) coinValue) =
      some (left, right, coinValue) := by
  cases first <;> simp [outcomeOfState, onlyMove]

theorem ordered_terminal_separates_left (first right coinValue : Bool) :
    State.terminal
        (onlyMove first (if first then right else false))
        (onlyMove (!first) (if first then false else right))
        (fun _ => none) coinValue ≠
      State.terminal
        (onlyMove first (if first then right else true))
        (onlyMove (!first) (if first then true else right))
        (fun _ => none) coinValue := by
  intro hequal
  have houtcome := congrArg (outcomeOfState first) hequal
  rw [outcomeOfState_ordered first false right coinValue,
    outcomeOfState_ordered first true right coinValue] at houtcome
  simp at houtcome

theorem ordered_terminal_separates_right (first left coinValue : Bool) :
    State.terminal
        (onlyMove first (if first then false else left))
        (onlyMove (!first) (if first then left else false))
        (fun _ => none) coinValue ≠
      State.terminal
        (onlyMove first (if first then true else left))
        (onlyMove (!first) (if first then left else true))
        (fun _ => none) coinValue := by
  intro hequal
  have houtcome := congrArg (outcomeOfState first) hequal
  rw [outcomeOfState_ordered first left false coinValue,
    outcomeOfState_ordered first left true coinValue] at houtcome
  simp at houtcome

theorem ordered_terminal_separates_coin (first left right : Bool) :
    State.terminal
        (onlyMove first (if first then right else left))
        (onlyMove (!first) (if first then left else right))
        (fun _ => none) false ≠
      State.terminal
        (onlyMove first (if first then right else left))
        (onlyMove (!first) (if first then left else right))
        (fun _ => none) true := by
  intro hequal
  have houtcome := congrArg (outcomeOfState first) hequal
  simp at houtcome

/-! Behavioral policies cross the bridge only at the two decision phases.
All other target menus are singletons, so they add no strategic choice. -/

def firstChoiceEquiv (first : Bool) :
    Source.information.Choice first .acting ≃
      (information first).Choice first .firstTurn where
  toFun choice := ⟨choice.1, by
    simpa [Source.information, Source.menu, information, menu] using choice.2⟩
  invFun choice := ⟨choice.1, by
    simpa [Source.information, Source.menu, information, menu] using choice.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def secondChoiceEquiv (first : Bool) :
    Source.information.Choice (!first) .acting ≃
      (information first).Choice (!first) .secondTurn where
  toFun choice := ⟨choice.1, by
    simpa [Source.information, Source.menu, information, menu] using choice.2⟩
  invFun choice := ⟨choice.1, by
    simpa [Source.information, Source.menu, information, menu] using choice.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem eq_not_of_ne {player first : Bool} (hne : player ≠ first) :
    player = !first := by
  cases player <;> cases first <;> simp_all

def translateBehavioral (first : Bool)
    (source : (player : Bool) → Source.information.BehavioralPolicy player) :
    (player : Bool) → (information first).BehavioralPolicy player :=
  fun player view =>
    match view with
    | .firstTurn =>
        if hplayer : player = first then by
          subst player
          exact FinDist.map (firstChoiceEquiv first) (source first .acting)
        else FinDist.pure ⟨none, by
          simp [menu, hplayer]⟩
    | .secondTurn =>
        if hplayer : player = !first then by
          subst player
          exact FinDist.map (secondChoiceEquiv first) (source (!first) .acting)
        else FinDist.pure ⟨none, by
          simp [menu, hplayer]⟩
    | .resolving => FinDist.pure ⟨none, by
        simp [menu]⟩
    | .done => FinDist.pure ⟨none, by
        simp [menu]⟩

def projectBehavioral (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    (player : Bool) → Source.information.BehavioralPolicy player :=
  fun player view =>
    match view with
    | .acting =>
        if hplayer : player = first then by
          subst player
          exact FinDist.map (firstChoiceEquiv first).symm
            (target first .firstTurn)
        else by
          have hsecond : player = !first := eq_not_of_ne hplayer
          subst player
          exact FinDist.map (secondChoiceEquiv first).symm
            (target (!first) .secondTurn)
    | .done => FinDist.pure ⟨none, by
        simp [Source.menu]⟩

theorem project_translate_acting (first player : Bool)
    (source : (i : Bool) → Source.information.BehavioralPolicy i) :
    projectBehavioral first (translateBehavioral first source) player .acting =
      source player .acting := by
  cases first <;> cases player <;>
    simp [projectBehavioral, translateBehavioral, FinDist.map_comp] <;>
    rfl

theorem translate_project_firstTurn (first : Bool)
    (target : (i : Bool) → (information first).BehavioralPolicy i) :
    translateBehavioral first (projectBehavioral first target) first .firstTurn =
      target first .firstTurn := by
  cases first <;>
    simp [translateBehavioral, projectBehavioral, FinDist.map_comp]

theorem translate_project_secondTurn (first : Bool)
    (target : (i : Bool) → (information first).BehavioralPolicy i) :
    translateBehavioral first (projectBehavioral first target) (!first) .secondTurn =
      target (!first) .secondTurn := by
  cases first <;>
    simp [translateBehavioral, projectBehavioral, FinDist.map_comp]

def firstActionLaw (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    FinDist Bool :=
  Source.actionLaw (projectBehavioral first target) first

def secondActionLaw (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    FinDist Bool :=
  Source.actionLaw (projectBehavioral first target) (!first)

theorem firstActionLaw_eq_map (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    firstActionLaw first target =
      FinDist.map (fun choice => choice.1.getD false)
        (target first .firstTurn) := by
  cases first <;>
    simp [firstActionLaw, Source.actionLaw, projectBehavioral,
      firstChoiceEquiv, FinDist.map_comp] <;>
    rfl

theorem secondActionLaw_eq_map (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    secondActionLaw first target =
      FinDist.map (fun choice => choice.1.getD false)
        (target (!first) .secondTurn) := by
  cases first <;>
    simp [secondActionLaw, Source.actionLaw, projectBehavioral,
      secondChoiceEquiv, FinDist.map_comp] <;>
    rfl

def orderedOutcomeLaw (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    FinDist Outcome :=
  (firstActionLaw first target).bind fun firstAction =>
    (secondActionLaw first target).bind fun secondAction =>
      FinDist.map
        (fun coinValue =>
          if first then (secondAction, firstAction, coinValue)
          else (firstAction, secondAction, coinValue)) Source.coin

theorem orderedOutcomeLaw_eq_policy_binds (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    orderedOutcomeLaw first target =
      (target first .firstTurn).bind fun firstChoice =>
        (target (!first) .secondTurn).bind fun secondChoice =>
          FinDist.map
            (fun coinValue =>
              if first then
                (secondChoice.1.getD false,
                  firstChoice.1.getD false, coinValue)
              else
                (firstChoice.1.getD false,
                  secondChoice.1.getD false, coinValue))
            Source.coin := by
  unfold orderedOutcomeLaw
  rw [firstActionLaw_eq_map, FinDist.bind_map,
    secondActionLaw_eq_map]
  simp_rw [FinDist.bind_map]

theorem firstActionLaw_translate (first : Bool)
    (source : (player : Bool) → Source.information.BehavioralPolicy player) :
    firstActionLaw first (translateBehavioral first source) =
      Source.actionLaw source first := by
  unfold firstActionLaw Source.actionLaw
  rw [project_translate_acting]

theorem secondActionLaw_translate (first : Bool)
    (source : (player : Bool) → Source.information.BehavioralPolicy player) :
    secondActionLaw first (translateBehavioral first source) =
      Source.actionLaw source (!first) := by
  unfold secondActionLaw Source.actionLaw
  rw [project_translate_acting]

theorem independentOutcomeLaw_eq_binds (left right : FinDist Bool) :
    independentOutcomeLaw Source.coin left right =
      left.bind fun leftAction =>
        right.bind fun rightAction =>
          FinDist.map
            (fun coinValue => (leftAction, rightAction, coinValue))
            Source.coin := by
  unfold independentOutcomeLaw FinDist.product
  rw [FinDist.bind_bind]
  simp only [FinDist.map_eq_bind, FinDist.bind_bind,
    FinDist.pure_bind]

/-- Either explicit serialization order gives the source's exact simultaneous
one-round outcome law.  The reverse order uses independence to commute the two
behavioral draws; no outcome coordinate is erased. -/
theorem orderedOutcomeLaw_translate (first : Bool)
    (source : (player : Bool) → Source.information.BehavioralPolicy player) :
    orderedOutcomeLaw first (translateBehavioral first source) =
      Source.oneRoundOutcomeLaw source := by
  rw [Source.oneRoundOutcomeLaw_eq_independent,
    independentOutcomeLaw_eq_binds, orderedOutcomeLaw,
    firstActionLaw_translate, secondActionLaw_translate]
  cases first with
  | false => rfl
  | true =>
      simp only [Bool.not_true, ↓reduceIte]
      exact FinDist.bind_comm
        (Source.actionLaw source true)
        (Source.actionLaw source false)
        (fun rightAction leftAction =>
          FinDist.map
            (fun coinValue => (leftAction, rightAction, coinValue))
            Source.coin)

theorem mapped_order_independent
    (source : (player : Bool) → Source.information.BehavioralPolicy player) :
    orderedOutcomeLaw false (translateBehavioral false source) =
      orderedOutcomeLaw true (translateBehavioral true source) := by
  rw [orderedOutcomeLaw_translate, orderedOutcomeLaw_translate]

def terminalOutcomeOfState (first : Bool) (state : State) : Outcome :=
  (outcomeOfState first state).getD (false, false, false)

theorem map_runBehavioralFrom_ready (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player)
    (firstJoint secondJoint : Bool → Option Bool)
    (trace : (execution first).Trace (.ready firstJoint secondJoint)) :
    FinDist.map
        (fun history => terminalOutcomeOfState first history.state)
        ((information first).runBehavioralFrom target 1
          ⟨.ready firstJoint secondJoint, trace⟩) =
      FinDist.map
        (fun coinValue => terminalOutcomeOfState first
          (.terminal firstJoint secondJoint (fun _ => none) coinValue))
        Source.coin := by
  have hterminal : ¬ (execution first).terminal
      (.ready firstJoint secondJoint) := by
    simp [terminal]
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 0 hterminal,
    FinDist.map_bind]
  unfold InformationModel.randomizedChooser
  rw [InformationModel.behavioralJoint_eq_pure_of_no_active
    (information first) target trace hterminal (by
      intro player
      simp [active]),
    FinDist.pure_bind,
    FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support (g := fun state =>
    FinDist.pure (terminalOutcomeOfState first state)) (by
      intro state realized
      rw [ExecutionProtocol.runRandomizedFor_zero, FinDist.map_pure]
      rfl)]
  rw [← FinDist.map_eq_bind]
  show FinDist.map (terminalOutcomeOfState first)
      (FinDist.map
        (.terminal firstJoint secondJoint (fun _ => none)) Source.coin) = _
  rw [FinDist.map_comp]
  rfl

theorem map_runBehavioralFrom_afterFirst (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player)
    (firstJoint : Bool → Option Bool)
    (trace : (execution first).Trace (.afterFirst firstJoint)) :
    FinDist.map
        (fun history => terminalOutcomeOfState first history.state)
        ((information first).runBehavioralFrom target 2
          ⟨.afterFirst firstJoint, trace⟩) =
      (target (!first) ((information first).infoOf (!first) trace)).bind
        fun choice =>
        FinDist.map
          (fun coinValue =>
            if first then
              (choice.1.getD false, (firstJoint first).getD false, coinValue)
            else
              ((firstJoint first).getD false, choice.1.getD false, coinValue))
          Source.coin := by
  have hterminal : ¬ (execution first).terminal
      (.afterFirst firstJoint) := by
    simp [terminal]
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 1 hterminal,
    FinDist.map_bind]
  unfold InformationModel.randomizedChooser
  rw [InformationModel.behavioralJoint_eq_map_of_at_most_one_active
    (information first) target trace hterminal (!first) (by
      intro player hactive
      exact hactive),
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro choice hchoice
  refine FinDist.map_bindOnSupport_const _ fun state realized => ?_
  simp [execution] at realized
  subst state
  show FinDist.map
      (fun history => terminalOutcomeOfState first history.state)
      ((information first).runBehavioralFrom target 1
        ⟨.ready firstJoint
          (fun other => if other = !first then choice.1 else none), _⟩) = _
  rw [map_runBehavioralFrom_ready]
  apply congrArg (fun function : Bool → Outcome =>
    FinDist.map function Source.coin)
  funext coinValue
  cases first <;> simp [terminalOutcomeOfState, outcomeOfState]

def runOutcomeLaw (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    FinDist Outcome :=
  FinDist.map
    (fun history => terminalOutcomeOfState first history.state)
    ((information first).runBehavioral target 3)

/-- The named target law is not a second evaluator: it is exactly the mapped
law of the canonical Protocol behavioral history runner after the three
serialization microsteps. -/
theorem runOutcomeLaw_eq_ordered (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    runOutcomeLaw first target = orderedOutcomeLaw first target := by
  rw [orderedOutcomeLaw_eq_policy_binds]
  unfold runOutcomeLaw InformationModel.runBehavioral
  have hterminal : ¬ (execution first).terminal
      (execution first).initHistory.state := by
    simp [terminal]
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 2 hterminal,
    FinDist.map_bind]
  unfold InformationModel.randomizedChooser
  rw [InformationModel.behavioralJoint_eq_map_of_at_most_one_active
    (information first) target (execution first).initHistory.trace
    hterminal first (by
      intro player hactive
      exact hactive),
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro choice hchoice
  refine FinDist.map_bindOnSupport_const _ fun state realized => ?_
  simp [execution] at realized
  subst state
  show FinDist.map
      (fun history => terminalOutcomeOfState first history.state)
      ((information first).runBehavioralFrom target 2
        ⟨.afterFirst
          (fun other => if other = first then choice.1 else none), _⟩) = _
  rw [map_runBehavioralFrom_afterFirst]
  rw [infoOf_eq_viewOfState]
  simp [viewOfState]

theorem orderedOutcomeLaw_eq_projected (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    orderedOutcomeLaw first target =
      Source.oneRoundOutcomeLaw (projectBehavioral first target) := by
  calc
    orderedOutcomeLaw first target =
        orderedOutcomeLaw first
          (translateBehavioral first (projectBehavioral first target)) := by
      rw [orderedOutcomeLaw_eq_policy_binds,
        orderedOutcomeLaw_eq_policy_binds,
        translate_project_firstTurn,
        translate_project_secondTurn]
    _ = Source.oneRoundOutcomeLaw (projectBehavioral first target) :=
      orderedOutcomeLaw_translate first (projectBehavioral first target)

/-- Every target behavioral profile projects to a source profile with exactly
the same full outcome law.  This is the law-level no-strategy-enlargement
certificate. -/
theorem runOutcomeLaw_eq_projected (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    runOutcomeLaw first target =
      Source.runOutcomeLaw (projectBehavioral first target) := by
  rw [runOutcomeLaw_eq_ordered, Source.runOutcomeLaw_eq_oneRound]
  exact orderedOutcomeLaw_eq_projected first target

/-- Forward translation preserves the full mapped canonical-run law. -/
theorem runOutcomeLaw_translate (first : Bool)
    (source : (player : Bool) → Source.information.BehavioralPolicy player) :
    runOutcomeLaw first (translateBehavioral first source) =
      Source.runOutcomeLaw source := by
  rw [runOutcomeLaw_eq_ordered, orderedOutcomeLaw_translate,
    Source.runOutcomeLaw_eq_oneRound]

/-- Reversing the explicit serialization order changes neither action nor
chance coordinates in the mapped canonical-run law. -/
theorem runOutcomeLaw_order_independent
    (source : (player : Bool) → Source.information.BehavioralPolicy player) :
    runOutcomeLaw false (translateBehavioral false source) =
      runOutcomeLaw true (translateBehavioral true source) := by
  rw [runOutcomeLaw_translate, runOutcomeLaw_translate]

def eraseState (first : Bool) (state : State) : Source.execution.History :=
  match outcomeOfState first state with
  | some outcome => Source.historyOfOutcome outcome
  | none => Source.execution.initHistory

def eraseHistory (first : Bool) (history : (execution first).History) :
    Source.execution.History :=
  eraseState first history.state

theorem map_erase_runBehavioralFrom_ready (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player)
    (firstJoint secondJoint : Bool → Option Bool)
    (trace : (execution first).Trace (.ready firstJoint secondJoint)) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioralFrom target 1
          ⟨.ready firstJoint secondJoint, trace⟩) =
      FinDist.map
        (fun coinValue => eraseState first
          (.terminal firstJoint secondJoint (fun _ => none) coinValue))
        Source.coin := by
  have hterminal : ¬ (execution first).terminal
      (.ready firstJoint secondJoint) := by
    simp [terminal]
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 0 hterminal,
    FinDist.map_bind]
  unfold InformationModel.randomizedChooser
  rw [InformationModel.behavioralJoint_eq_pure_of_no_active
    (information first) target trace hterminal (by
      intro player
      simp [active]),
    FinDist.pure_bind,
    FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support (g := fun state =>
    FinDist.pure (eraseState first state)) (by
      intro state realized
      rw [ExecutionProtocol.runRandomizedFor_zero, FinDist.map_pure]
      rfl)]
  rw [← FinDist.map_eq_bind]
  show FinDist.map (eraseState first)
      (FinDist.map
        (.terminal firstJoint secondJoint (fun _ => none)) Source.coin) = _
  rw [FinDist.map_comp]
  rfl

theorem map_erase_runBehavioralFrom_afterFirst (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player)
    (firstJoint : Bool → Option Bool)
    (trace : (execution first).Trace (.afterFirst firstJoint)) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioralFrom target 2
          ⟨.afterFirst firstJoint, trace⟩) =
      (target (!first) ((information first).infoOf (!first) trace)).bind
        fun choice =>
          FinDist.map
            (fun coinValue => eraseState first
              (.terminal firstJoint
                (fun other => if other = !first then choice.1 else none)
                (fun _ => none) coinValue))
            Source.coin := by
  have hterminal : ¬ (execution first).terminal
      (.afterFirst firstJoint) := by
    simp [terminal]
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 1 hterminal,
    FinDist.map_bind]
  unfold InformationModel.randomizedChooser
  rw [InformationModel.behavioralJoint_eq_map_of_at_most_one_active
    (information first) target trace hterminal (!first) (by
      intro player hactive
      exact hactive),
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro choice hchoice
  refine FinDist.map_bindOnSupport_const _ fun state realized => ?_
  simp [execution] at realized
  subst state
  show FinDist.map (eraseHistory first)
      ((information first).runBehavioralFrom target 1
        ⟨.ready firstJoint
          (fun other => if other = !first then choice.1 else none), _⟩) = _
  rw [map_erase_runBehavioralFrom_ready]

theorem map_erase_runBehavioral_eq_policy_binds (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioral target 3) =
      (target first .firstTurn).bind fun firstChoice =>
        (target (!first) .secondTurn).bind fun secondChoice =>
          FinDist.map
            (fun coinValue => eraseState first
              (.terminal
                (fun other => if other = first then firstChoice.1 else none)
                (fun other =>
                  if other = !first then secondChoice.1 else none)
                (fun _ => none) coinValue))
            Source.coin := by
  unfold InformationModel.runBehavioral
  have hterminal : ¬ (execution first).terminal
      (execution first).initHistory.state := by
    simp [terminal]
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
      _ 2 hterminal,
    FinDist.map_bind]
  unfold InformationModel.randomizedChooser
  rw [InformationModel.behavioralJoint_eq_map_of_at_most_one_active
    (information first) target (execution first).initHistory.trace
    hterminal first (by
      intro player hactive
      exact hactive),
    FinDist.bind_map]
  apply FinDist.bind_congr
  intro choice hchoice
  refine FinDist.map_bindOnSupport_const _ fun state realized => ?_
  simp [execution] at realized
  subst state
  show FinDist.map (eraseHistory first)
      ((information first).runBehavioralFrom target 2
        ⟨.afterFirst
          (fun other => if other = first then choice.1 else none), _⟩) = _
  rw [map_erase_runBehavioralFrom_afterFirst]
  rw [infoOf_eq_viewOfState]
  simp [viewOfState]

theorem map_erase_runBehavioral_eq_map_ordered (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioral target 3) =
      FinDist.map Source.historyOfOutcome (orderedOutcomeLaw first target) := by
  rw [map_erase_runBehavioral_eq_policy_binds,
    orderedOutcomeLaw_eq_policy_binds,
    FinDist.map_bind]
  apply FinDist.bind_congr
  intro firstChoice hfirstChoice
  rw [FinDist.map_bind]
  apply FinDist.bind_congr
  intro secondChoice hsecondChoice
  rw [FinDist.map_comp]
  apply congrArg (fun function : Bool → Source.execution.History =>
    FinDist.map function Source.coin)
  funext coinValue
  cases first <;> simp [eraseState, outcomeOfState]

/-- Literal canonical-history preservation for every target behavioral
profile.  Nonterminal target states erase to the source initial history, while
the three-step target run is proved directly to erase to the one-step source
run, so no default outcome can hide unfinished mass. -/
theorem map_erase_runBehavioral_eq_source (first : Bool)
    (target : (player : Bool) → (information first).BehavioralPolicy player) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioral target 3) =
      Source.information.runBehavioral
        (projectBehavioral first target) 1 := by
  calc
    _ = FinDist.map Source.historyOfOutcome
          (orderedOutcomeLaw first target) :=
      map_erase_runBehavioral_eq_map_ordered first target
    _ = FinDist.map Source.historyOfOutcome
          (Source.oneRoundOutcomeLaw (projectBehavioral first target)) := by
      rw [orderedOutcomeLaw_eq_projected]
    _ = _ := Source.map_historyOfOutcome_oneRoundOutcomeLaw
      (projectBehavioral first target)

theorem map_erase_runBehavioral_translate (first : Bool)
    (source : (player : Bool) → Source.information.BehavioralPolicy player) :
    FinDist.map (eraseHistory first)
        ((information first).runBehavioral
          (translateBehavioral first source) 3) =
      Source.information.runBehavioral source 1 := by
  calc
    _ = FinDist.map Source.historyOfOutcome
          (orderedOutcomeLaw first (translateBehavioral first source)) :=
      map_erase_runBehavioral_eq_map_ordered first
        (translateBehavioral first source)
    _ = FinDist.map Source.historyOfOutcome
          (Source.oneRoundOutcomeLaw source) := by
      rw [orderedOutcomeLaw_translate]
    _ = _ := Source.map_historyOfOutcome_oneRoundOutcomeLaw source

theorem map_erase_runBehavioral_order_independent
    (source : (player : Bool) → Source.information.BehavioralPolicy player) :
    FinDist.map (eraseHistory false)
        ((information false).runBehavioral
          (translateBehavioral false source) 3) =
      FinDist.map (eraseHistory true)
        ((information true).runBehavioral
          (translateBehavioral true source) 3) := by
  rw [map_erase_runBehavioral_translate,
    map_erase_runBehavioral_translate]

end Serial

end GameTheory.Experimental.FOSGToEFG
