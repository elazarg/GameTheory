/-
# Explicit-order typed MAID serialization

The execution state stores the resolved topological prefix; information states
expose only the current decision site and its declared observed-parent
configuration. EXP-041 proves its complete assignment law equals the
order-free native frontier evaluator.
-/

import GameTheory.Languages.MAID.Basic
import GameTheory.Languages.EFG

noncomputable section

namespace GameTheory.Languages.MAID.ToEFG

open GameTheory.Languages
open GameTheory.Probability
open GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : GameTheory.Languages.MAID.Structure Player Node}

abbrev TaggedValue (diagram : GameTheory.Languages.MAID.Structure Player Node) :=
  Σ node, diagram.Value node

/-- A serialized state is exactly a resolved prefix of the selected order.
The values retain their dependent node indices. -/
structure Stage (diagram : GameTheory.Languages.MAID.Structure Player Node)
    (topological : GameTheoryMath.DAG.TopologicalOrder diagram.parents) where
  path : List (TaggedValue diagram)
  length_le : path.length ≤ topological.order.length
  follows :
    path.map Sigma.fst = topological.order.take path.length

namespace Stage

variable
  (topological : GameTheoryMath.DAG.TopologicalOrder diagram.parents)

def initial : Stage diagram topological where
  path := []
  length_le := by simp
  follows := rfl

def resolved [DecidableEq Node]
    (state : Stage diagram topological) : Finset Node :=
  (state.path.map Sigma.fst).toFinset

def IsTerminal (state : Stage diagram topological) : Prop :=
  state.path.length = topological.order.length

theorem not_terminal_iff (state : Stage diagram topological) :
    ¬ state.IsTerminal ↔
      state.path.length < topological.order.length := by
  constructor
  · intro hne
    exact Nat.lt_of_le_of_ne state.length_le hne
  · exact Nat.ne_of_lt

def pending (state : Stage diagram topological) : Option Node :=
  topological.order[state.path.length]?

def pendingNode (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length) : Node :=
  topological.order[state.path.length]'hpending

def Assignment.setOne [DecidableEq Node]
    (assignment : GameTheory.Languages.MAID.Assignment diagram)
    (entry : TaggedValue diagram) : GameTheory.Languages.MAID.Assignment diagram :=
  GameTheory.Languages.MAID.Assignment.resolve diagram assignment {entry.1}
      fun (node : {node // node ∈ ({entry.1} : Finset Node)}) => by
    have hnode : node.1 = entry.1 :=
      Finset.mem_singleton.mp node.2
    cases node with
    | mk value _ =>
        dsimp only at hnode
        subst value
        exact entry.2

def assignment [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (state : Stage diagram topological) : GameTheory.Languages.MAID.Assignment diagram :=
  state.path.foldl Assignment.setOne semantics.defaultValue

theorem pending_parents_resolved [DecidableEq Node]
    (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length) :
    diagram.parents (state.pendingNode topological hpending) ⊆
      state.resolved topological := by
  intro parent hparent
  obtain ⟨earlier, hearlier, hnode⟩ :=
    topological.respects
      ⟨state.path.length, hpending⟩ parent
        (by simpa [pendingNode] using hparent)
  rw [resolved, List.mem_toFinset, state.follows]
  rw [List.mem_iff_getElem]
  refine ⟨earlier.val, ?_, ?_⟩
  · simpa using hearlier
  · simpa [hearlier] using hnode

def configOf [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (state : Stage diagram topological) (nodes : Finset Node) :
    GameTheory.Languages.MAID.Config diagram nodes :=
  GameTheory.Languages.MAID.Assignment.restrict diagram
    (state.assignment topological semantics) nodes

def advanceTagged (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length)
    (entry : TaggedValue diagram)
    (hnode : entry.1 = state.pendingNode topological hpending) :
    Stage diagram topological where
  path := state.path ++ [entry]
  length_le := by simp only [List.length_append, List.length_singleton]
                  omega
  follows := by
    rw [List.map_append, List.map_singleton, state.follows]
    rw [hnode]
    simp only [List.length_append, List.length_singleton, pendingNode]
    exact (List.take_append_getElem
      (l := topological.order) hpending)

def advance (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length)
    (value : diagram.Value (state.pendingNode topological hpending)) :
    Stage diagram topological :=
  state.advanceTagged topological hpending
    ⟨state.pendingNode topological hpending, value⟩ rfl

@[simp]
theorem advance_path (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length)
    (value : diagram.Value (state.pendingNode topological hpending)) :
    (state.advance topological hpending value).path =
      state.path ++
        [⟨state.pendingNode topological hpending, value⟩] :=
  rfl

@[simp]
theorem advance_length (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length)
    (value : diagram.Value (state.pendingNode topological hpending)) :
    (state.advance topological hpending value).path.length =
      state.path.length + 1 := by
  simp [advance, advanceTagged]

theorem eq_of_path_eq
    {first second : Stage diagram topological}
    (hpath : first.path = second.path) :
    first = second := by
  cases first with
  | mk firstPath firstLength firstFollows =>
      cases second with
      | mk secondPath secondLength secondFollows =>
          dsimp only at hpath
          subst secondPath
          rfl

end Stage

/-- One source action carrier per source owner. Its tag is a decision site,
and its payload has exactly that site's value type. -/
def Action (diagram : GameTheory.Languages.MAID.Structure Player Node) (owner : Player) :=
  Σ site : GameTheory.Languages.MAID.DecisionSite diagram owner,
    diagram.Value site.1

variable
  (topological : GameTheoryMath.DAG.TopologicalOrder diagram.parents)

def Active (state : Stage diagram topological) (owner : Player) : Prop :=
  ∃ node, state.pending topological = some node ∧
    diagram.kind node = .decision owner

def Available (state : Stage diagram topological) (owner : Player) :
    Set (Action diagram owner) :=
  { action | state.pending topological = some action.1.1 }

theorem active_iff
    (state : Stage diagram topological) (owner : Player) :
    Active topological state owner ↔
      ∃ node, state.pending topological = some node ∧
        diagram.kind node = .decision owner :=
  Iff.rfl

theorem pending_eq_some {state : Stage diagram topological}
    (hpending : state.path.length < topological.order.length)
    : state.pending topological =
      some (state.pendingNode topological hpending) := by
  simp [Stage.pending, Stage.pendingNode, hpending]

theorem pendingNode_eq_of_pending_eq
    {state : Stage diagram topological}
    (hpending : state.path.length < topological.order.length)
    {node : Node}
    (heq : state.pending topological = some node) :
    state.pendingNode topological hpending = node :=
  Option.some.inj
    ((pending_eq_some topological hpending).symm.trans heq)

def jointFor [DecidableEq Player] (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length)
    {owner : Player}
    (hkind : diagram.kind (state.pendingNode topological hpending) =
      .decision owner)
    (value : diagram.Value (state.pendingNode topological hpending)) :
    (other : Player) → Option (Action diagram other) := fun other =>
  if howner : other = owner then by
    subst other
    exact some ⟨
      ⟨state.pendingNode topological hpending, hkind⟩,
      value⟩
  else none

theorem jointFor_legal [DecidableEq Player]
    (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length)
    {owner : Player}
    (hkind : diagram.kind (state.pendingNode topological hpending) =
      .decision owner)
    (value : diagram.Value (state.pendingNode topological hpending)) :
    IsLegalJoint (Active topological state) (Available topological state)
      (jointFor topological state hpending hkind value) := by
  intro other
  by_cases howner : other = owner
  · subst other
    simp only [jointFor, dite_true]
    exact ⟨
      ⟨state.pendingNode topological hpending,
        pending_eq_some topological hpending, hkind⟩,
      pending_eq_some topological hpending⟩
  · simp only [jointFor, dite_false, howner]
    intro hactive
    obtain ⟨otherNode, hotherPending, hotherKind⟩ := hactive
    have hsame :
        otherNode = state.pendingNode topological hpending :=
      Option.some.inj
        (hotherPending.symm.trans
          (pending_eq_some topological hpending))
    rw [hsame, hkind] at hotherKind
    exact howner (GameTheory.Languages.MAID.NodeKind.decision.inj hotherKind.symm)

theorem exists_eq_some_of_active
    {state : Stage diagram topological}
    {joint : (owner : Player) → Option (Action diagram owner)}
    (hlegal :
      IsLegalJoint (Active topological state)
        (Available topological state) joint)
    {owner : Player} (hactive : Active topological state owner) :
    ∃ action, joint owner = some action := by
  have hlegalOwner := hlegal owner
  cases hchoice : joint owner with
  | none =>
      rw [hchoice] at hlegalOwner
      exact False.elim (hlegalOwner hactive)
  | some action => exact ⟨action, rfl⟩

noncomputable def selectedAction
    {state : Stage diagram topological}
    (joint : (owner : Player) → Option (Action diagram owner))
    (hlegal :
      IsLegalJoint (Active topological state)
        (Available topological state) joint)
    (owner : Player) (hactive : Active topological state owner) :
    Action diagram owner :=
  Classical.choose
    (exists_eq_some_of_active topological hlegal hactive)

theorem selectedAction_spec
    {state : Stage diagram topological}
    (joint : (owner : Player) → Option (Action diagram owner))
    (hlegal :
      IsLegalJoint (Active topological state)
        (Available topological state) joint)
    (owner : Player) (hactive : Active topological state owner) :
    joint owner =
      some (selectedAction topological joint hlegal owner hactive) :=
  Classical.choose_spec
    (exists_eq_some_of_active topological hlegal hactive)

def transitionAt [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length)
    (joint : (owner : Player) → Option (Action diagram owner))
    (hlegal :
      IsLegalJoint (Active topological state)
        (Available topological state) joint) :
    FinDist (Stage diagram topological) := by
  let node := state.pendingNode topological hpending
  match hkind : diagram.kind node with
  | .chance =>
      exact FinDist.map
        (state.advance topological hpending)
        (semantics.chanceLaw node hkind
          (state.configOf topological semantics (diagram.parents node)))
  | .decision owner =>
      have hactive : Active topological state owner :=
        ⟨node, pending_eq_some topological hpending, hkind⟩
      let action :=
        selectedAction topological joint hlegal owner hactive
      have hlegalOwner := hlegal owner
      have hselected :=
        selectedAction_spec topological joint hlegal owner hactive
      rw [hselected] at hlegalOwner
      have hsite :
          action.1.1 = state.pendingNode topological hpending :=
        Option.some.inj
          (hlegalOwner.2.symm.trans
            (pending_eq_some topological hpending))
      exact FinDist.pure
        (state.advanceTagged topological hpending
          ⟨action.1.1, action.2⟩ hsite)

def transition [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (state : Stage diagram topological) :
    { joint : (owner : Player) → Option (Action diagram owner) //
      ¬ state.IsTerminal topological ∧
        IsLegalJoint (Active topological state)
          (Available topological state) joint } →
      FinDist (Stage diagram topological) := fun certified =>
  transitionAt topological semantics state
    ((state.not_terminal_iff topological).mp certified.2.1)
    certified.1 certified.2.2

@[reducible]
def execution [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram) :
    ExecutionProtocol Player where
  State := Stage diagram topological
  Action := Action diagram
  init := Stage.initial topological
  active := Active topological
  available := Available topological
  terminal := Stage.IsTerminal topological
  step := transition topological semantics
  progress := by
    intro state hterminal
    have hpending :
        state.path.length < topological.order.length :=
      (state.not_terminal_iff topological).mp hterminal
    let node := state.pendingNode topological hpending
    match hkind : diagram.kind node with
    | .chance =>
        refine ⟨fun _ => none, ?_⟩
        intro owner hactive
        obtain ⟨ownerNode, hownerPending, hownerKind⟩ := hactive
        have hsame :
            ownerNode = state.pendingNode topological hpending :=
          Option.some.inj
            (hownerPending.symm.trans
              (pending_eq_some topological hpending))
        rw [hsame, hkind] at hownerKind
        contradiction
    | .decision owner =>
        exact ⟨
          jointFor topological state hpending hkind
            (semantics.defaultValue node),
          jointFor_legal topological state hpending hkind
            (semantics.defaultValue node)⟩

/-- A player either has no move or sees one source decision site together with
exactly that site's declared observation configuration. -/
inductive View (diagram : GameTheory.Languages.MAID.Structure Player Node) (owner : Player)
  | inactive
  | acting (site : GameTheory.Languages.MAID.DecisionSite diagram owner)
      (observed :
        GameTheory.Languages.MAID.Config diagram (diagram.observedParents site.1))

def viewOf [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (owner : Player) (state : Stage diagram topological) :
    View diagram owner :=
  match state.pending topological with
  | none => .inactive
  | some node =>
      if hkind : diagram.kind node = .decision owner then
        .acting ⟨node, hkind⟩
          (state.configOf topological semantics
            (diagram.observedParents node))
      else .inactive

theorem viewOf_eq_acting [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (owner : Player) (state : Stage diagram topological)
    {node : Node} (hpending : state.pending topological = some node)
    (hkind : diagram.kind node = .decision owner) :
    viewOf topological semantics owner state =
      .acting ⟨node, hkind⟩
        (state.configOf topological semantics
          (diagram.observedParents node)) := by
  simp [viewOf, hpending, hkind]

def menu (owner : Player) :
    View diagram owner → Set (Option (Action diagram owner))
  | .inactive => {none}
  | .acting site _ =>
      { choice | ∃ value, choice = some ⟨site, value⟩ }

theorem menu_adequate_at [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (owner : Player) (state : Stage diagram topological)
    (choice : Option (Action diagram owner)) :
    choice ∈ menu owner (viewOf topological semantics owner state) ↔
      LegalOption (execution topological semantics) state owner choice := by
  unfold viewOf
  split
  next hpending =>
    have hinactive : ¬ Active topological state owner := by
      rintro ⟨node, hnode, _⟩
      rw [hpending] at hnode
      contradiction
    cases choice with
    | none =>
        simp [menu, LegalOption, hinactive]
    | some action =>
        simp [menu, LegalOption, hinactive]
  next node hpending =>
    split
    next hkind =>
      have hactive : Active topological state owner :=
        ⟨node, hpending, hkind⟩
      cases choice with
      | none =>
          simp [menu, LegalOption, hactive]
      | some action =>
          constructor
          · rintro ⟨value, hchoice⟩
            have haction :
                action = ⟨⟨node, hkind⟩, value⟩ :=
              Option.some.inj hchoice
            cases haction
            exact ⟨hactive, hpending⟩
          · intro hlegal
            have havailable :
                state.pending topological = some action.1.1 :=
              hlegal.2
            have hnode : action.1.1 = node :=
              Option.some.inj (havailable.symm.trans hpending)
            obtain ⟨⟨actionNode, actionKind⟩, value⟩ := action
            dsimp only at hnode
            subst actionNode
            have hsite :
                (⟨node, actionKind⟩ :
                  GameTheory.Languages.MAID.DecisionSite diagram owner) =
                    ⟨node, hkind⟩ :=
              Subtype.ext rfl
            cases hsite
            exact ⟨value, rfl⟩
    next hkind =>
      have hinactive : ¬ Active topological state owner := by
        rintro ⟨activeNode, hactiveNode, hactiveKind⟩
        have hnode : activeNode = node :=
          Option.some.inj (hactiveNode.symm.trans hpending)
        subst activeNode
        exact hkind hactiveKind
      cases choice with
      | none =>
          simp [menu, LegalOption, hinactive]
      | some action =>
          simp [menu, LegalOption, hinactive]

@[reducible]
def signals [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram) :
    InfoSignals (execution topological semantics) where
  PublicSignal := Unit
  PrivateSignal := View diagram
  initialPublic := ()
  initialPrivate :=
    fun owner => viewOf topological semantics owner
      (Stage.initial topological)
  publicSignal := fun _ => ()
  privateSignal :=
    fun owner event => viewOf topological semantics owner event.target
  InfoState := View diagram
  initInfo := fun _ signal _ => signal
  pushInfo := fun _ _ _ signal _ => signal

theorem infoOf_eq_viewOf [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (owner : Player) {state : (execution topological semantics).State}
    (trace : (execution topological semantics).Trace state) :
    (signals topological semantics).infoOf owner trace =
      viewOf topological semantics owner state := by
  induction trace with
  | start => rfl
  | extend _ _ _ _ _ =>
      rw [InfoSignals.infoOf_extend]

@[reducible]
def information [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram) :
    InformationModel (execution topological semantics) where
  toInfoSignals := signals topological semantics
  menu := menu
  menu_adequate := by
    intro owner state trace choice
    rw [infoOf_eq_viewOf topological semantics owner trace]
    exact menu_adequate_at topological semantics owner state choice

theorem mem_transition_path [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (source target : Stage diagram topological)
    (certified :
      { joint : (owner : Player) → Option (Action diagram owner) //
        ¬ source.IsTerminal topological ∧
          IsLegalJoint (Active topological source)
            (Available topological source) joint })
    (htarget :
      target ∈ (transition topological semantics source certified).support) :
    ∃ entry : TaggedValue diagram,
      target.path = source.path ++ [entry] := by
  unfold transition transitionAt at htarget
  dsimp only at htarget
  split at htarget
  next hkind =>
    rw [FinDist.support_map] at htarget
    obtain ⟨value, _, rfl⟩ := htarget
    exact ⟨_, rfl⟩
  next owner hkind =>
    rw [FinDist.mem_support_pure] at htarget
    subst target
    exact ⟨_, rfl⟩

def eraseAction {owner : Player}
    (action : Action diagram owner) : TaggedValue diagram :=
  ⟨action.1.1, action.2⟩

theorem eraseAction_injective {owner : Player} :
    Function.Injective
      (eraseAction (diagram := diagram) (owner := owner)) := by
  rintro ⟨⟨firstNode, firstKind⟩, firstValue⟩
    ⟨⟨secondNode, secondKind⟩, secondValue⟩ hequal
  cases hequal
  rfl

theorem legal_eq_none_of_chance
    [DecidableEq Player] [DecidableEq Node]
    (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length)
    (hkind :
      diagram.kind (state.pendingNode topological hpending) =
        .chance)
    (joint : (owner : Player) → Option (Action diagram owner))
    (hlegal :
      IsLegalJoint (Active topological state)
        (Available topological state) joint)
    (owner : Player) :
    joint owner = none := by
  cases hchoice : joint owner with
  | none => rfl
  | some action =>
      have howner := hlegal owner
      rw [hchoice] at howner
      obtain ⟨⟨activeNode, hactiveNode, hactiveKind⟩, _⟩ := howner
      have hnode :
          activeNode = state.pendingNode topological hpending :=
        Option.some.inj
          (hactiveNode.symm.trans
            (pending_eq_some topological hpending))
      rw [hnode, hkind] at hactiveKind
      contradiction

theorem legal_eq_none_of_ne_owner
    [DecidableEq Player] [DecidableEq Node]
    (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length)
    {activeOwner : Player}
    (hkind :
      diagram.kind (state.pendingNode topological hpending) =
        .decision activeOwner)
    (joint : (owner : Player) → Option (Action diagram owner))
    (hlegal :
      IsLegalJoint (Active topological state)
        (Available topological state) joint)
    {owner : Player} (hne : owner ≠ activeOwner) :
    joint owner = none := by
  cases hchoice : joint owner with
  | none => rfl
  | some action =>
      have howner := hlegal owner
      rw [hchoice] at howner
      obtain ⟨⟨activeNode, hactiveNode, hactiveKind⟩, _⟩ := howner
      have hnode :
          activeNode = state.pendingNode topological hpending :=
        Option.some.inj
          (hactiveNode.symm.trans
            (pending_eq_some topological hpending))
      rw [hnode, hkind] at hactiveKind
      exact False.elim
        (hne (GameTheory.Languages.MAID.NodeKind.decision.inj hactiveKind.symm))

theorem mem_transition_decision_path
    [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (source target : Stage diagram topological)
    (certified :
      { joint : (owner : Player) → Option (Action diagram owner) //
        ¬ source.IsTerminal topological ∧
          IsLegalJoint (Active topological source)
            (Available topological source) joint })
    (hpending : source.path.length < topological.order.length)
    {owner : Player}
    (hkind :
      diagram.kind (source.pendingNode topological hpending) =
        .decision owner)
    (htarget :
      target ∈ (transition topological semantics source certified).support) :
    ∃ action : Action diagram owner,
      certified.1 owner = some action ∧
        target.path =
          source.path ++ [eraseAction action] := by
  have hpendingEq :
      hpending =
        (source.not_terminal_iff topological).mp certified.2.1 :=
    Subsingleton.elim _ _
  subst hpending
  unfold transition transitionAt at htarget
  dsimp only at htarget
  split at htarget
  next hchance =>
    rw [hkind] at hchance
    contradiction
  next activeOwner hdecision =>
    have howner : activeOwner = owner :=
      GameTheory.Languages.MAID.NodeKind.decision.inj
        (hdecision.symm.trans hkind)
    subst activeOwner
    rw [FinDist.mem_support_pure] at htarget
    subst target
    refine ⟨_, ?_, rfl⟩
    exact selectedAction_spec topological certified.1
      certified.2.2 owner _

theorem source_eq_of_same_target
    [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    {firstSource secondSource target : Stage diagram topological}
    (first :
      { joint : (owner : Player) → Option (Action diagram owner) //
        ¬ firstSource.IsTerminal topological ∧
          IsLegalJoint (Active topological firstSource)
            (Available topological firstSource) joint })
    (second :
      { joint : (owner : Player) → Option (Action diagram owner) //
        ¬ secondSource.IsTerminal topological ∧
          IsLegalJoint (Active topological secondSource)
            (Available topological secondSource) joint })
    (hfirst :
      target ∈ (transition topological semantics firstSource first).support)
    (hsecond :
      target ∈ (transition topological semantics secondSource second).support) :
    firstSource = secondSource := by
  obtain ⟨firstEntry, hfirstPath⟩ :=
    mem_transition_path topological semantics firstSource target first hfirst
  obtain ⟨secondEntry, hsecondPath⟩ :=
    mem_transition_path topological semantics secondSource target second
      hsecond
  have hpaths :
      firstSource.path ++ [firstEntry] =
        secondSource.path ++ [secondEntry] :=
    hfirstPath.symm.trans hsecondPath
  have hlength :
      firstSource.path.length = secondSource.path.length := by
    have := congrArg List.length hpaths
    simpa using this
  have hprefix : firstSource.path = secondSource.path :=
    (List.append_inj hpaths hlength).1
  cases firstSource with
  | mk firstPath firstLength firstFollows =>
      cases secondSource with
      | mk secondPath secondLength secondFollows =>
          dsimp only at hprefix
          subst secondPath
          rfl

theorem joint_eq_of_same_target
    [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    {source target : Stage diagram topological}
    (first second :
      { joint : (owner : Player) → Option (Action diagram owner) //
        ¬ source.IsTerminal topological ∧
          IsLegalJoint (Active topological source)
            (Available topological source) joint })
    (hfirst :
      target ∈ (transition topological semantics source first).support)
    (hsecond :
      target ∈ (transition topological semantics source second).support) :
    first.1 = second.1 := by
  have hpending :
      source.path.length < topological.order.length :=
    (source.not_terminal_iff topological).mp first.2.1
  match hkind :
      diagram.kind (source.pendingNode topological hpending) with
  | .chance =>
      funext owner
      rw [
        legal_eq_none_of_chance topological source hpending hkind
          first.1 first.2.2 owner,
        legal_eq_none_of_chance topological source hpending hkind
          second.1 second.2.2 owner]
  | .decision activeOwner =>
      obtain ⟨firstAction, hfirstAction, hfirstPath⟩ :=
        mem_transition_decision_path topological semantics source target
          first hpending hkind hfirst
      obtain ⟨secondAction, hsecondAction, hsecondPath⟩ :=
        mem_transition_decision_path topological semantics source target
          second hpending hkind hsecond
      have happend :
          source.path ++ [eraseAction firstAction] =
            source.path ++ [eraseAction secondAction] :=
        hfirstPath.symm.trans hsecondPath
      have hsingle :
          [eraseAction firstAction] = [eraseAction secondAction] :=
        List.append_cancel_left happend
      have herase :
          eraseAction firstAction = eraseAction secondAction := by
        simpa using hsingle
      have haction : firstAction = secondAction :=
        eraseAction_injective herase
      funext owner
      by_cases howner : owner = activeOwner
      · subst owner
        rw [hfirstAction, hsecondAction, haction]
      · rw [
          legal_eq_none_of_ne_owner topological source hpending hkind
            first.1 first.2.2 howner,
          legal_eq_none_of_ne_owner topological source hpending hkind
            second.1 second.2.2 howner]

theorem initial_not_mem_transition
    [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (source : Stage diagram topological)
    (certified :
      { joint : (owner : Player) → Option (Action diagram owner) //
        ¬ source.IsTerminal topological ∧
          IsLegalJoint (Active topological source)
            (Available topological source) joint }) :
    Stage.initial topological ∉
      (transition topological semantics source certified).support := by
  intro hinitial
  obtain ⟨entry, hpath⟩ :=
    mem_transition_path topological semantics source
      (Stage.initial topological) certified hinitial
  simp [Stage.initial] at hpath

theorem step_predecessor_unique
    [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    {target firstSource secondSource :
      (execution topological semantics).State}
    {firstJoint secondJoint :
      (owner : Player) →
        Option ((execution topological semantics).Action owner)}
    (firstLegal :
      (execution topological semantics).Legal firstSource firstJoint)
    (secondLegal :
      (execution topological semantics).Legal secondSource secondJoint)
    (firstRealized :
      target ∈
        ((execution topological semantics).step firstSource
          ⟨firstJoint, firstLegal⟩).support)
    (secondRealized :
      target ∈
        ((execution topological semantics).step secondSource
          ⟨secondJoint, secondLegal⟩).support) :
    firstSource = secondSource ∧ firstJoint = secondJoint := by
  have hsource :=
    source_eq_of_same_target topological semantics
      ⟨firstJoint, firstLegal⟩ ⟨secondJoint, secondLegal⟩
      firstRealized secondRealized
  subst secondSource
  exact ⟨rfl,
    joint_eq_of_same_target topological semantics
      ⟨firstJoint, firstLegal⟩ ⟨secondJoint, secondLegal⟩
      firstRealized secondRealized⟩

theorem trace_unique [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram) :
    ∀ {state : (execution topological semantics).State}
      (first second : (execution topological semantics).Trace state),
      first = second
  | _, .start, .start => rfl
  | _, .start, .extend prior joint isLegal realized =>
      False.elim
        (initial_not_mem_transition topological semantics _
          ⟨joint, isLegal⟩ realized)
  | _, .extend prior joint isLegal realized, .start =>
      False.elim
        (initial_not_mem_transition topological semantics _
          ⟨joint, isLegal⟩ realized)
  | _, .extend prior joint isLegal realized,
      .extend secondPrior secondJoint secondLegal secondRealized => by
      obtain ⟨rfl, hjoint⟩ :=
        step_predecessor_unique topological semantics isLegal secondLegal
          realized secondRealized
      subst secondJoint
      have hprior :=
        trace_unique semantics prior secondPrior
      subst secondPrior
      rfl
termination_by _ first _ => first.length
decreasing_by simp [ExecutionProtocol.Trace.length]

theorem execution_treeShaped
    [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram) :
    (execution topological semantics).IsTreeShaped :=
  fun _ => ⟨trace_unique (topological := topological) semantics⟩

theorem execution_singleMover
    [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (state : (execution topological semantics).State)
    {first second : Player}
    (hfirst : (execution topological semantics).active state first)
    (hsecond : (execution topological semantics).active state second) :
    first = second := by
  obtain ⟨firstNode, hfirstPending, hfirstKind⟩ := hfirst
  obtain ⟨secondNode, hsecondPending, hsecondKind⟩ := hsecond
  have hnode : firstNode = secondNode :=
    Option.some.inj (hfirstPending.symm.trans hsecondPending)
  subst secondNode
  exact GameTheory.Languages.MAID.NodeKind.decision.inj
    (hfirstKind.symm.trans hsecondKind)

@[reducible]
def game [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram) :
    EFG.Game Player where
  execution := execution topological semantics
  information := information topological semantics
  treeShaped := execution_treeShaped topological semantics
  singleMover := execution_singleMover topological semantics

/-- A native site-local policy becomes an EFG behavioral policy without
receiving the serialized execution prefix. -/
def behavioralPolicy [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram) (owner : Player) :
    (information topological semantics).BehavioralPolicy owner
  | .inactive => FinDist.pure ⟨none, rfl⟩
  | .acting site observed =>
      FinDist.map
        (fun value => ⟨some ⟨site, value⟩, ⟨value, rfl⟩⟩)
        (policy owner site observed)

def behavioralProfile [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram) :
    (owner : Player) →
      (information topological semantics).BehavioralPolicy owner :=
  fun owner => behavioralPolicy topological semantics policy owner

/-- With one source owner, the independent behavioral product is just that
owner's local choice law embedded in the only joint coordinate. -/
theorem behavioralJoint_unit_coordinate
    {Vertex : Type uNode}
    {unitDiagram : GameTheory.Languages.MAID.Structure Unit Vertex}
    (unitTopological :
      GameTheoryMath.DAG.TopologicalOrder unitDiagram.parents)
    [DecidableEq Vertex]
    (semantics : GameTheory.Languages.MAID.Semantics unitDiagram)
    (policy : GameTheory.Languages.MAID.Policy unitDiagram)
    (state : Stage unitDiagram unitTopological)
    (trace : (execution unitTopological semantics).Trace state)
    (hterminal :
      ¬ (execution unitTopological semantics).terminal state) :
    (information unitTopological semantics).behavioralJoint
        (behavioralProfile unitTopological semantics policy)
        trace hterminal =
      FinDist.map
        (fun choice :
            (information unitTopological semantics).Choice ()
              ((information unitTopological semantics).infoOf () trace) =>
          ⟨(fun _ => choice.1),
            ExecutionProtocol.legal_of_legalOption hterminal
              fun owner => by
                cases owner
                exact
                  ((information unitTopological semantics).menu_adequate
                    () trace choice.1).mp choice.2⟩)
        (behavioralPolicy unitTopological semantics policy ()
          ((information unitTopological semantics).infoOf () trace)) := by
  let model := information unitTopological semantics
  let assemble :
      ((owner : Unit) →
        model.Choice owner (model.infoOf owner trace)) →
          { joint : (owner : Unit) →
              Option ((execution unitTopological semantics).Action owner) //
            (execution unitTopological semantics).Legal state joint } :=
    fun draws => ⟨
      (fun owner => (draws owner).1),
      ExecutionProtocol.legal_of_legalOption hterminal fun owner =>
        (model.menu_adequate owner trace (draws owner).1).mp
          (draws owner).2⟩
  let atUnit :
      model.Choice () (model.infoOf () trace) →
        { joint : (owner : Unit) →
            Option ((execution unitTopological semantics).Action owner) //
          (execution unitTopological semantics).Legal state joint } :=
    fun choice => ⟨
      fun _ => choice.1,
      ExecutionProtocol.legal_of_legalOption hterminal fun owner => by
        cases owner
        exact (model.menu_adequate () trace choice.1).mp choice.2⟩
  have hassemble :
      assemble = atUnit ∘ (fun draws => draws ()) := by
    funext draws
    apply Subtype.ext
    funext owner
    cases owner
    rfl
  unfold InformationModel.behavioralJoint
  rw [show (fun draws => ⟨
      (fun owner => (draws owner).1),
      ExecutionProtocol.legal_of_legalOption hterminal fun owner =>
        ((information unitTopological semantics).menu_adequate
          owner trace (draws owner).1).mp (draws owner).2⟩) =
      assemble by rfl,
    hassemble, ← FinDist.map_comp, FinDist.map_apply_pi]
  rfl

theorem finDist_map_injective {α β : Type*} {f : α → β}
    (hf : Function.Injective f) :
    Function.Injective (FinDist.map f) := by
  intro first second hequal
  letI : Nonempty α := ⟨first.support_nonempty.choose⟩
  have hback :=
    congrArg (FinDist.map (Function.invFun f)) hequal
  rw [FinDist.map_comp, FinDist.map_comp] at hback
  have hleft : Function.invFun f ∘ f = id := by
    funext value
    exact Function.leftInverse_invFun hf value
  simpa only [hleft, FinDist.map_id] using hback

/-- The source-level law for resolving exactly the pending topological node. -/
def serialNodeLaw [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram)
    (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length) :
    FinDist
      (diagram.Value (state.pendingNode topological hpending)) := by
  let node := state.pendingNode topological hpending
  match hkind : diagram.kind node with
  | .chance =>
      exact semantics.chanceLaw node hkind
        (state.configOf topological semantics (diagram.parents node))
  | .decision owner =>
      exact policy owner ⟨node, hkind⟩
        (state.configOf topological semantics
          (diagram.observedParents node))

def serialStep [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram)
    (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length) :
    FinDist (Stage diagram topological) :=
  FinDist.map (state.advance topological hpending)
    (serialNodeLaw topological semantics policy state hpending)

theorem serialNodeLaw_of_chance
    [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram)
    (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length)
    (hkind :
      diagram.kind (state.pendingNode topological hpending) =
        .chance) :
    serialNodeLaw topological semantics policy state hpending =
      semantics.chanceLaw
        (state.pendingNode topological hpending) hkind
        (state.configOf topological semantics
          (diagram.parents
            (state.pendingNode topological hpending))) := by
  unfold serialNodeLaw
  dsimp only
  split
  next => rfl
  next owner hdecision =>
    rw [hkind] at hdecision
    contradiction

theorem serialNodeLaw_of_decision
    [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram)
    (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length)
    {owner : Player}
    (hkind :
      diagram.kind (state.pendingNode topological hpending) =
        .decision owner) :
    serialNodeLaw topological semantics policy state hpending =
      policy owner
        ⟨state.pendingNode topological hpending, hkind⟩
        (state.configOf topological semantics
          (diagram.observedParents
            (state.pendingNode topological hpending))) := by
  unfold serialNodeLaw
  dsimp only
  split
  next hchance =>
    rw [hkind] at hchance
    contradiction
  next activeOwner hdecision =>
    have howner : activeOwner = owner :=
      GameTheory.Languages.MAID.NodeKind.decision.inj
        (hdecision.symm.trans hkind)
    subst activeOwner
    rfl

theorem inactive_of_pending_chance
    [DecidableEq Player] [DecidableEq Node]
    (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length)
    (hkind :
      diagram.kind (state.pendingNode topological hpending) =
        .chance)
    (owner : Player) :
    ¬ Active topological state owner := by
  rintro ⟨node, hnode, hdecision⟩
  have hsame :
      node = state.pendingNode topological hpending :=
    Option.some.inj
      (hnode.symm.trans (pending_eq_some topological hpending))
  rw [hsame, hkind] at hdecision
  contradiction

/-- The joint-action law corresponding directly to one native site law. This
is the source-facing midpoint for comparison with `behavioralJoint`. -/
def serialJointLaw [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram)
    (state : Stage diagram topological)
    (hterminal : ¬ (execution topological semantics).terminal state) :
    FinDist
      { joint : (owner : Player) →
          Option ((execution topological semantics).Action owner) //
        (execution topological semantics).Legal state joint } := by
  have hpending :
      state.path.length < topological.order.length :=
    (state.not_terminal_iff topological).mp hterminal
  let node := state.pendingNode topological hpending
  match hkind : diagram.kind node with
  | .chance =>
      exact FinDist.pure ⟨fun _ => none, hterminal,
        fun owner => inactive_of_pending_chance topological state
          hpending hkind owner⟩
  | .decision owner =>
      exact FinDist.map
        (fun value => ⟨
          jointFor topological state hpending hkind value,
          hterminal,
          jointFor_legal topological state hpending hkind value⟩)
        (policy owner ⟨node, hkind⟩
          (state.configOf topological semantics
            (diagram.observedParents node)))

theorem behavioralJoint_eq_serialJointLaw_unit
    {Vertex : Type uNode}
    {unitDiagram : GameTheory.Languages.MAID.Structure Unit Vertex}
    (unitTopological :
      GameTheoryMath.DAG.TopologicalOrder unitDiagram.parents)
    [DecidableEq Vertex]
    (semantics : GameTheory.Languages.MAID.Semantics unitDiagram)
    (policy : GameTheory.Languages.MAID.Policy unitDiagram)
    (state : Stage unitDiagram unitTopological)
    (trace : (execution unitTopological semantics).Trace state)
    (hterminal :
      ¬ (execution unitTopological semantics).terminal state) :
    (information unitTopological semantics).behavioralJoint
        (behavioralProfile unitTopological semantics policy)
        trace hterminal =
      serialJointLaw unitTopological semantics policy state hterminal := by
  apply finDist_map_injective
    (f := fun joint => joint.1) Subtype.val_injective
  rw [behavioralJoint_unit_coordinate unitTopological semantics
    policy state trace hterminal, FinDist.map_comp]
  let jointOfOption :
      Option (Action unitDiagram ()) →
        (owner : Unit) → Option (Action unitDiagram owner) :=
    fun choice owner => by
      cases owner
      exact choice
  have hfactor :
      (fun choice :
          (information unitTopological semantics).Choice ()
            ((information unitTopological semantics).infoOf () trace) =>
        (fun _ => choice.1)) =
        jointOfOption ∘ (fun choice => choice.1) := by
    funext choice owner
    cases owner
    rfl
  have hfull :
      ((fun joint :
          { joint : (owner : Unit) → Option (Action unitDiagram owner) //
            (execution unitTopological semantics).Legal state joint } =>
          joint.1) ∘
        (fun choice :
            (information unitTopological semantics).Choice ()
              ((information unitTopological semantics).infoOf () trace) =>
          (⟨(fun _ => choice.1),
            ExecutionProtocol.legal_of_legalOption hterminal
              fun owner => by
                cases owner
                exact
                  ((information unitTopological semantics).menu_adequate
                    () trace choice.1).mp choice.2⟩ :
            { joint :
                (owner : Unit) → Option (Action unitDiagram owner) //
              (execution unitTopological semantics).Legal state joint }))) =
        jointOfOption ∘ (fun choice => choice.1) := by
    funext choice owner
    cases owner
    rfl
  rw [hfull, ← FinDist.map_comp]
  have hinfoAction :=
    congrArg
      (fun view =>
        FinDist.map (fun choice => choice.1)
          (behavioralPolicy unitTopological semantics policy () view))
      (infoOf_eq_viewOf unitTopological semantics () trace)
  rw [hinfoAction]
  have hpending :
      state.path.length < unitTopological.order.length :=
    (state.not_terminal_iff unitTopological).mp hterminal
  let node := state.pendingNode unitTopological hpending
  match hkind : unitDiagram.kind node with
  | .chance =>
      have hstateView :
          viewOf unitTopological semantics () state =
            .inactive := by
        have hnotDecision :
            unitDiagram.kind
                (state.pendingNode unitTopological hpending) ≠
              .decision () := by
          intro hdecision
          rw [hkind] at hdecision
          contradiction
        unfold viewOf
        rw [pending_eq_some unitTopological hpending]
        simp [hnotDecision]
      rw [hstateView, behavioralPolicy, FinDist.map_pure,
        FinDist.map_pure]
      unfold serialJointLaw
      dsimp only
      split
      next =>
        rw [FinDist.map_pure]
      next owner hdecision =>
        rw [hkind] at hdecision
        contradiction
  | .decision owner =>
      have howner : owner = () := Subsingleton.elim _ _
      subst owner
      have hstateView :
          viewOf unitTopological semantics () state =
            .acting ⟨node, hkind⟩
              (state.configOf unitTopological semantics
                (unitDiagram.observedParents node)) :=
        viewOf_eq_acting unitTopological semantics () state
          (pending_eq_some unitTopological hpending) hkind
      rw [hstateView, behavioralPolicy, FinDist.map_comp,
        FinDist.map_comp]
      unfold serialJointLaw
      dsimp only
      split
      next hchance =>
        rw [hkind] at hchance
        contradiction
      next activeOwner hdecision =>
        have hactiveOwner : activeOwner = () := Subsingleton.elim _ _
        subst activeOwner
        rw [FinDist.map_comp]
        congr 1

theorem transition_of_chance
    [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (state : Stage diagram topological)
    (certified :
      { joint : (owner : Player) → Option (Action diagram owner) //
        ¬ state.IsTerminal topological ∧
          IsLegalJoint (Active topological state)
            (Available topological state) joint })
    (hpending : state.path.length < topological.order.length)
    (hkind :
      diagram.kind (state.pendingNode topological hpending) =
        .chance) :
    transition topological semantics state certified =
      FinDist.map (state.advance topological hpending)
        (semantics.chanceLaw
          (state.pendingNode topological hpending) hkind
          (state.configOf topological semantics
            (diagram.parents
              (state.pendingNode topological hpending)))) := by
  have hpendingEq :
      hpending =
        (state.not_terminal_iff topological).mp certified.2.1 :=
    Subsingleton.elim _ _
  subst hpending
  unfold transition transitionAt
  dsimp only
  split
  next => rfl
  next owner hdecision =>
    rw [hkind] at hdecision
    contradiction

theorem transition_jointFor
    [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (state : Stage diagram topological)
    (hterminal : ¬ state.IsTerminal topological)
    (hpending : state.path.length < topological.order.length)
    {owner : Player}
    (hkind :
      diagram.kind (state.pendingNode topological hpending) =
        .decision owner)
    (value : diagram.Value (state.pendingNode topological hpending)) :
    transition topological semantics state
        ⟨jointFor topological state hpending hkind value,
          hterminal,
          jointFor_legal topological state hpending hkind value⟩ =
      FinDist.pure (state.advance topological hpending value) := by
  have hpendingEq :
      hpending =
        (state.not_terminal_iff topological).mp hterminal :=
    Subsingleton.elim _ _
  subst hpending
  unfold transition transitionAt
  dsimp only
  split
  next hchance =>
    rw [hkind] at hchance
    contradiction
  next activeOwner hdecision =>
    have howner : activeOwner = owner :=
      GameTheory.Languages.MAID.NodeKind.decision.inj
        (hdecision.symm.trans hkind)
    subst activeOwner
    let activeProof : Active topological state owner :=
      ⟨state.pendingNode topological _, pending_eq_some topological _,
        hdecision⟩
    have hselected :=
      selectedAction_spec topological
        (jointFor topological state _ hdecision value)
        (jointFor_legal topological state _ hdecision value)
        owner activeProof
    have hjoint :
        jointFor topological state _ hdecision value owner =
          some ⟨
            ⟨state.pendingNode topological _, hdecision⟩,
            value⟩ := by
      simp [jointFor]
    rw [hjoint] at hselected
    have haction := Option.some.inj hselected
    apply congrArg FinDist.pure
    apply Stage.eq_of_path_eq
    simp only [Stage.advanceTagged, Stage.advance]
    exact congrArg (fun entry => state.path ++ [entry])
      (congrArg eraseAction haction).symm

/-- Drawing the source joint law and taking the compiled EFG transition is
exactly one source-level serialized node step. -/
theorem serialJointLaw_bind_transition
    [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram)
    (state : Stage diagram topological)
    (hterminal : ¬ (execution topological semantics).terminal state) :
    (serialJointLaw topological semantics policy state hterminal).bind
        (fun draw =>
          (execution topological semantics).step state draw) =
      serialStep topological semantics policy state
        ((state.not_terminal_iff topological).mp hterminal) := by
  let hpending :=
    (state.not_terminal_iff topological).mp hterminal
  unfold serialJointLaw
  dsimp only
  split
  next hkind =>
    rw [FinDist.pure_bind,
      transition_of_chance topological semantics state _
        hpending hkind]
    unfold serialStep
    rw [serialNodeLaw_of_chance topological semantics policy
      state hpending hkind]
  next owner hkind =>
    rw [FinDist.bind_map]
    unfold serialStep
    rw [serialNodeLaw_of_decision topological semantics policy
      state hpending hkind, FinDist.map_eq_bind]
    exact FinDist.bind_congr fun value _ =>
      transition_jointFor topological semantics state hterminal
        hpending hkind value

/-- For a one-owner typed MAID, one actual behavioral step of the compiled EFG
is exactly the corresponding serialized source step. This is the semantic
bridge used by the history-runner induction; neither side mentions the
intermediate legality witnesses. -/
theorem behavioralJoint_bind_transition_unit
    {Vertex : Type uNode}
    {unitDiagram : GameTheory.Languages.MAID.Structure Unit Vertex}
    (unitTopological :
      GameTheoryMath.DAG.TopologicalOrder unitDiagram.parents)
    [DecidableEq Vertex]
    (semantics : GameTheory.Languages.MAID.Semantics unitDiagram)
    (policy : GameTheory.Languages.MAID.Policy unitDiagram)
    (state : Stage unitDiagram unitTopological)
    (trace : (execution unitTopological semantics).Trace state)
    (hterminal :
      ¬ (execution unitTopological semantics).terminal state) :
    ((information unitTopological semantics).behavioralJoint
        (behavioralProfile unitTopological semantics policy)
        trace hterminal).bind
          (fun draw =>
            (execution unitTopological semantics).step state draw) =
      serialStep unitTopological semantics policy state
        ((state.not_terminal_iff unitTopological).mp hterminal) := by
  rw [behavioralJoint_eq_serialJointLaw_unit unitTopological
    semantics policy state trace hterminal]
  exact serialJointLaw_bind_transition unitTopological semantics
    policy state hterminal

def serialRun [DecidableEq Player] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram) :
    Nat → Stage diagram topological →
      FinDist (Stage diagram topological)
  | 0, state => FinDist.pure state
  | fuel + 1, state =>
      if hterminal :
          state.path.length = topological.order.length then
        FinDist.pure state
      else
        (serialStep topological semantics policy state
          (Nat.lt_of_le_of_ne state.length_le hterminal)).bind
            (serialRun semantics policy fuel)

/-- Forgetting histories from the compiled one-owner EFG runner yields exactly
the native serialized stage runner. The EFG may retain a richer trace, but its
state law is neither an approximation nor merely payoff-equivalent. -/
theorem map_state_runBehavioralFrom_eq_serialRun_unit
    {Vertex : Type uNode}
    {unitDiagram : GameTheory.Languages.MAID.Structure Unit Vertex}
    (unitTopological :
      GameTheoryMath.DAG.TopologicalOrder unitDiagram.parents)
    [DecidableEq Vertex]
    (semantics : GameTheory.Languages.MAID.Semantics unitDiagram)
    (policy : GameTheory.Languages.MAID.Policy unitDiagram) :
    ∀ (fuel : ℕ)
      (history : (execution unitTopological semantics).History),
      FinDist.map ExecutionProtocol.History.state
          ((information unitTopological semantics).runBehavioralFrom
            (behavioralProfile unitTopological semantics policy)
            fuel history) =
        serialRun unitTopological semantics policy fuel history.state := by
  intro fuel
  induction fuel with
  | zero =>
      intro history
      rw [InformationModel.runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_zero, serialRun,
        FinDist.map_pure]
  | succ fuel ih =>
      intro history
      by_cases hterminal :
          (execution unitTopological semantics).terminal history.state
      · have hpath :
            history.state.path.length =
              unitTopological.order.length := hterminal
        rw [InformationModel.runBehavioralFrom,
          ExecutionProtocol.runRandomizedFor_of_terminal _ _ hterminal,
          FinDist.map_pure, serialRun, dif_pos hpath]
      · have hpath :
            history.state.path.length ≠
              unitTopological.order.length := hterminal
        rw [InformationModel.runBehavioralFrom,
          ExecutionProtocol.runRandomizedFor_succ_of_not_terminal
            _ fuel hterminal,
          FinDist.map_bind, serialRun, dif_neg hpath]
        unfold InformationModel.randomizedChooser
        calc
          _ =
              ((information unitTopological semantics).behavioralJoint
                (behavioralProfile unitTopological semantics policy)
                history.trace hterminal).bind
                (fun draw =>
                  ((execution unitTopological semantics).step
                    history.state draw).bind
                    (serialRun unitTopological semantics policy fuel)) := by
              apply FinDist.bind_congr
              intro draw _
              rw [FinDist.map_bindOnSupport]
              exact FinDist.bindOnSupport_eq_bind_of_eq_on_support
                fun _ realized => ih (history.extend draw.2 realized)
          _ =
              (((information unitTopological semantics).behavioralJoint
                (behavioralProfile unitTopological semantics policy)
                history.trace hterminal).bind
                  (fun draw =>
                    (execution unitTopological semantics).step
                      history.state draw)).bind
                (serialRun unitTopological semantics policy fuel) := by
              rw [FinDist.bind_bind]
          _ =
              (serialStep unitTopological semantics policy history.state
                ((history.state.not_terminal_iff unitTopological).mp
                  hterminal)).bind
                (serialRun unitTopological semantics policy fuel) := by
              rw [behavioralJoint_bind_transition_unit unitTopological
                semantics policy history.state history.trace hterminal]

end GameTheory.Languages.MAID.ToEFG
