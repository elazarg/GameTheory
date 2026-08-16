/-
# EXP-107: graphical data for a MAID pruning fixpoint

This experiment keeps the stable MAID syntax unchanged.  It evaluates the
existing exact `UtilityView` against an explicit map of decision-factor
parents.  The edge-addition test restores all original observations at the
queried site at once while leaving every other decision at the candidate
pruning.  This is the hybrid graph used by the addition algorithm, not the
final reduced graph and not a one-edge restoration.

Strategic relevance is separate from requisite observation.  Its graph adds
one local dummy mechanism parent to the source decision and performs the
s-reachability query in the original graph.  The source-to-target orientation
means that the target decision can strategically rely on the source.  No
semantic coverage or equilibrium theorem is claimed here.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation
import GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
import GameTheory.Languages.MAID.ObservationPruning

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph

open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open MAIDRequisiteObservation

universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}
variable {semantics : Semantics diagram}

/-- Candidate parent sets for decision factors.  Values at chance nodes are
ignored by `effectiveParentsUnder`. -/
abbrev DecisionParentMap (Node : Type uNode) := Node → Finset Node

/-- Original observations absent from a candidate pruning at one site. -/
def Pruning.missingAt [DecidableEq Node] (pruning : Pruning diagram)
    {owner : Player} (site : DecisionSite diagram owner) : Finset Node :=
  diagram.observedParents site.1 \ pruning.kept site.1

/-- The decision-parent candidate represented by a pruning. -/
def Pruning.candidateDecisionParents (pruning : Pruning diagram) :
    DecisionParentMap Node :=
  pruning.kept

/-- Factor parents under an explicit decision-parent candidate.  Chance nodes
retain their original causal parents. -/
def effectiveParentsUnder (diagram : Structure Player Node)
    (decisionParents : DecisionParentMap Node) (node : Node) : Finset Node :=
  match diagram.kind node with
  | .chance => diagram.parents node
  | .decision _ => decisionParents node

namespace UtilityView

/-- The exact utility-leaf graph under an explicit decision-parent map. -/
def graphParentsUnder (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (decisionParents : DecisionParentMap Node) :
    view.GraphNode owner → Finset (view.GraphNode owner)
  | .base node =>
      (effectiveParentsUnder diagram decisionParents node).image
        UtilityView.GraphNode.base
  | .utility term =>
      (view.term term).parents.image UtilityView.GraphNode.base

/-- Directed relevance of one exact utility term under the supplied graph. -/
def IsRelevantUtilityTermUnder (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (decisionParents : DecisionParentMap Node)
    (site : DecisionSite diagram owner) (term : view.UtilitySite owner) : Prop :=
  Relation.TransGen (FiniteBNMoralSeparation.DirectedEdge
    (graphParentsUnder view decisionParents))
    (UtilityView.GraphNode.base site.1)
    (UtilityView.GraphNode.utility term)

/-- Condition on the decision and on every current parent outside the removed
set.  The removed set remains set-valued. -/
def conditioningUnder (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (decisionParents : DecisionParentMap Node)
    (site : DecisionSite diagram owner) (removed : Finset Node) :
    Finset (view.GraphNode owner) :=
  insert (.base site.1)
    ((decisionParents site.1 \ removed).image UtilityView.GraphNode.base)

/-- D-connection in the exact utility graph selected by `decisionParents`. -/
def DConnectedUnder (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (decisionParents : DecisionParentMap Node)
    (source target : view.GraphNode owner)
    (evidence : Finset (view.GraphNode owner)) : Prop :=
  FiniteBNMoralSeparation.Connected
    (graphParentsUnder view decisionParents)
    {source} {target} evidence source target

/-- Graphical ignorability in one explicitly selected graph. -/
def AreGraphicallyIgnorableUnder (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (decisionParents : DecisionParentMap Node)
    (site : DecisionSite diagram owner) (removed : Finset Node) : Prop :=
  removed ⊆ decisionParents site.1 ∧
    ∀ term : view.UtilitySite owner,
      IsRelevantUtilityTermUnder view decisionParents site term →
        ∀ observation ∈ removed,
          ¬ DConnectedUnder view decisionParents (.base observation)
            (.utility term)
            (conditioningUnder view decisionParents site removed)

end UtilityView

/-- Restore all original observations at the queried decision, leaving every
other decision at the candidate pruning. -/
def Pruning.restoreAllAt [DecidableEq Node] (pruning : Pruning diagram)
    {owner : Player} (site : DecisionSite diagram owner) :
    DecisionParentMap Node :=
  fun node =>
    if node = site.1 then diagram.observedParents node else pruning.kept node

/-- One site is stable for edge addition exactly when every currently missing
original parent is jointly ignorable in the restore-all-at-site hybrid graph. -/
def UtilityView.IsEdgeAdditionStableAt (view : UtilityView semantics)
    [DecidableEq Node] (pruning : Pruning diagram)
    {owner : Player} (site : DecisionSite diagram owner) : Prop :=
  UtilityView.AreGraphicallyIgnorableUnder view
    (Pruning.restoreAllAt pruning site) site
    (Pruning.missingAt pruning site)

/-- A candidate pruning is a graph-level edge-addition fixpoint at every
decision site. -/
def UtilityView.IsEdgeAdditionFixpoint (view : UtilityView semantics)
    [DecidableEq Node] (pruning : Pruning diagram) : Prop :=
  ∀ owner (site : DecisionSite diagram owner),
    UtilityView.IsEdgeAdditionStableAt view pruning site

namespace UtilityView

/-- Graph nodes for one s-reachability query.  The local mechanism node is a
new root whose sole child is the queried source decision. -/
inductive MechanismGraphNode (view : UtilityView semantics) (owner : Player)
  | object (node : view.GraphNode owner)
  | mechanism

instance [DecidableEq Node] (view : UtilityView semantics) (owner : Player) :
    DecidableEq (MechanismGraphNode view owner) := by
  intro first second
  cases first with
  | mechanism =>
      cases second with
      | mechanism => exact isTrue rfl
      | object _ => exact isFalse (by intro equality; cases equality)
  | object first =>
      cases second with
      | mechanism => exact isFalse (by intro equality; cases equality)
      | object second =>
          if h : first = second then
            exact isTrue (by cases h; rfl)
          else
            exact isFalse (fun equality =>
              h (MechanismGraphNode.object.inj equality))

/-- Original utility graph with one dummy mechanism parent attached to the
source decision.  Candidate pruning parents never enter this definition. -/
def mechanismGraphParents (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (source : DecisionSite diagram owner) :
    MechanismGraphNode view owner →
      Finset (MechanismGraphNode view owner)
  | .mechanism => ∅
  | .object (.utility term) =>
      (view.term term).parents.image
        (fun node => .object (.base node))
  | .object (.base node) =>
      let original := (effectiveParents diagram node).image
        (fun parent => .object (.base parent))
      if node = source.1 then insert .mechanism original else original

/-- Evidence for whether the target rule can rely on the source rule: the
target decision together with all its original observations. -/
def sReachConditioning (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (target : DecisionSite diagram owner) :
    Finset (MechanismGraphNode view owner) :=
  insert (.object (.base target.1))
    ((diagram.observedParents target.1).image
      (fun node => .object (.base node)))

/-- `source` is s-reachable from `target` when the dummy mechanism parent of the
source is d-connected, in the original graph, to an owner utility descendant
of the target conditional on the target and its original observations. -/
def SReachable (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (source target : DecisionSite diagram owner) : Prop :=
  ∃ term : view.UtilitySite owner,
    view.IsRelevantUtilityTerm target term ∧
      FiniteBNMoralSeparation.Connected
        (mechanismGraphParents view source)
        {.mechanism} {.object (.utility term)}
        (sReachConditioning view target)
        .mechanism (.object (.utility term))

/-- Same-owner oriented strategic relevance.  An edge `source → target`
means that optimizing `target` can rely on the mechanism at `source`. -/
def OrientedRelevance (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (source target : DecisionSite diagram owner) : Prop :=
  SReachable view source target

/-- Sufficient recall's graph-only premise: each owner's induced relevance
graph over the original MAID is acyclic. -/
def SReachAcyclic (view : UtilityView semantics)
    [DecidableEq Node] : Prop :=
  ∀ owner, GameTheory.Math.DAG.Acyclic
    (fun source target : DecisionSite diagram owner =>
      OrientedRelevance view source target)

end UtilityView

/-! ## Two-decision graph controls -/

namespace TwoDecision

inductive ExampleNode
  | signal
  | early
  | late
  deriving DecidableEq, Fintype

def parents : ExampleNode → Finset ExampleNode
  | .signal => ∅
  | .early => {.signal}
  | .late => {.signal}

def topologicalParents :
    GameTheory.Math.DAG.TopologicalOrder parents where
  order := [.signal, .early, .late]
  nodup := by decide
  complete node := by cases node <;> simp
  respects := by
    intro index parent hparent
    fin_cases index
    · simp [parents] at hparent
    · have hsignal : parent = .signal := by
        simpa [parents] using hparent
      subst parent
      exact ⟨0, by decide, rfl⟩
    · have hsignal : parent = .signal := by
        simpa [parents] using hparent
      subst parent
      exact ⟨0, by decide, rfl⟩

@[reducible]
def exampleDiagram : Structure Unit ExampleNode where
  kind
    | .signal => .chance
    | .early => .decision ()
    | .late => .decision ()
  parents := parents
  observedParents := parents
  Value _ := Bool
  observed_sub _ := fun _ => id
  observed_eq_of_chance node hchance := by
    cases node <;> simp [parents] at hchance ⊢
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder
    topologicalParents

@[reducible]
def exampleSemantics : Semantics exampleDiagram where
  defaultValue _ := false
  chanceLaw node hchance _ := by
    cases node with
    | signal => exact GameTheory.Math.Probability.FinDist.pure false
    | early => simp at hchance
    | late => simp at hchance
  utility _ _ := 0

def emptyView : UtilityView (diagram := exampleDiagram) exampleSemantics where
  terms _ := []
  utility_eq_sum _ _ := by simp

/-- The candidate removes the common signal from both decisions. -/
def emptyPruning : Pruning exampleDiagram where
  kept _ := ∅
  kept_sub_observed _ := by simp

def earlySite : DecisionSite exampleDiagram () := ⟨.early, rfl⟩

def lateSite : DecisionSite exampleDiagram () := ⟨.late, rfl⟩

/-- With no owned utility term, restoring the signal at either decision still
leaves the whole missing set graphically ignorable.  This is the degenerate
safe boundary that a later nonconstant hostile consumer must strengthen. -/
theorem emptyView_fixpoint :
    UtilityView.IsEdgeAdditionFixpoint emptyView emptyPruning := by
  intro owner site
  cases owner
  rcases site with ⟨node, hkind⟩
  cases node with
  | signal => simp at hkind
  | early =>
      constructor
      · simp [Pruning.restoreAllAt, Pruning.missingAt,
          emptyPruning, exampleDiagram, parents]
      · intro term
        exact Fin.elim0 term
  | late =>
      constructor
      · simp [Pruning.restoreAllAt, Pruning.missingAt,
          emptyPruning, exampleDiagram, parents]
      · intro term
        exact Fin.elim0 term

/-- The empty utility view has no strategic-relevance edge. -/
theorem emptyView_not_oriented
    (source target : DecisionSite exampleDiagram ()) :
    ¬ UtilityView.OrientedRelevance emptyView source target := by
  rintro ⟨term, _⟩
  exact Fin.elim0 term

/-- Consequently the same-owner s-reachability graph is acyclic. -/
theorem emptyView_sReachAcyclic :
    UtilityView.SReachAcyclic emptyView := by
  intro owner vertex path
  cases owner
  obtain ⟨next, edge, _⟩ := Relation.TransGen.head'_iff.mp path
  exact emptyView_not_oriented vertex next edge

def jointTerm : UtilityTerm exampleDiagram where
  parents := {.early, .late}
  payoff _ := 0

def cycleView : UtilityView (diagram := exampleDiagram) exampleSemantics where
  terms _ := [jointTerm]
  utility_eq_sum _ _ := by
    simp [jointTerm, UtilityTerm.value]

def jointSite : cycleView.UtilitySite () :=
  ⟨0, by simp [cycleView]⟩

theorem early_relevant :
    cycleView.IsRelevantUtilityTerm earlySite jointSite := by
  apply Relation.TransGen.single
  simp [MAIDRequisiteObservation.UtilityView.DirectedEdge,
    MAIDRequisiteObservation.UtilityView.graphParents,
    MAIDRequisiteObservation.UtilityView.term,
    cycleView, jointSite, jointTerm, earlySite]
  exact Finset.mem_insert_self _ _

theorem late_relevant :
    cycleView.IsRelevantUtilityTerm lateSite jointSite := by
  apply Relation.TransGen.single
  simp [MAIDRequisiteObservation.UtilityView.DirectedEdge,
    MAIDRequisiteObservation.UtilityView.graphParents,
    MAIDRequisiteObservation.UtilityView.term,
    cycleView, jointSite, jointTerm, lateSite]
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))

/-- In the shared-utility skeleton, the late decision's mechanism is
s-reachable to the early decision. -/
theorem late_oriented_early :
    UtilityView.OrientedRelevance cycleView lateSite earlySite := by
  refine ⟨jointSite, early_relevant, ?_⟩
  let graphParents :=
    UtilityView.mechanismGraphParents cycleView lateSite
  let evidence := UtilityView.sReachConditioning cycleView earlySite
  let mechanismNode : UtilityView.MechanismGraphNode cycleView () :=
    .mechanism
  let late : UtilityView.MechanismGraphNode cycleView () :=
    .object (.base .late)
  let utility : UtilityView.MechanismGraphNode cycleView () :=
    .object (.utility jointSite)
  have mechanismLate :
      FiniteBNMoralSeparation.DirectedEdge graphParents
        mechanismNode late := by
    simp [FiniteBNMoralSeparation.DirectedEdge, graphParents,
      mechanismNode, late, UtilityView.mechanismGraphParents, lateSite]
  have lateUtility :
      FiniteBNMoralSeparation.DirectedEdge graphParents late utility := by
    simp [FiniteBNMoralSeparation.DirectedEdge, graphParents, late,
      utility, UtilityView.mechanismGraphParents,
      MAIDRequisiteObservation.UtilityView.term,
      cycleView, jointSite, jointTerm]
    exact Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr rfl))
  have mechanismOpen : mechanismNode ∉ evidence := by
    simp [mechanismNode, evidence, UtilityView.sReachConditioning]
  have lateOpen : late ∉ evidence := by
    simp [late, evidence, UtilityView.sReachConditioning,
      earlySite, exampleDiagram, parents]
  have utilityOpen : utility ∉ evidence := by
    simp [utility, evidence, UtilityView.sReachConditioning]
  have mechanismAncestor :
      FiniteBNMoralSeparation.InAncestralClosure graphParents
        {mechanismNode} {utility} evidence mechanismNode := by
    refine ⟨mechanismNode, ?_, Relation.ReflTransGen.refl⟩
    simp [FiniteBNMoralSeparation.queryRoots]
  have lateAncestor :
      FiniteBNMoralSeparation.InAncestralClosure graphParents
        {mechanismNode} {utility} evidence late := by
    refine ⟨utility, ?_, Relation.ReflTransGen.single lateUtility⟩
    simp [FiniteBNMoralSeparation.queryRoots]
  have utilityAncestor :
      FiniteBNMoralSeparation.InAncestralClosure graphParents
        {mechanismNode} {utility} evidence utility := by
    refine ⟨utility, ?_, Relation.ReflTransGen.refl⟩
    simp [FiniteBNMoralSeparation.queryRoots]
  have firstStep : FiniteBNMoralSeparation.MoralAdjacent graphParents
      {mechanismNode} {utility} evidence mechanismNode late :=
    ⟨by simp [mechanismNode, late], mechanismOpen, lateOpen,
      mechanismAncestor, lateAncestor, Or.inl mechanismLate⟩
  have secondStep : FiniteBNMoralSeparation.MoralAdjacent graphParents
      {mechanismNode} {utility} evidence late utility :=
    ⟨by simp [late, utility], lateOpen, utilityOpen,
      lateAncestor, utilityAncestor, Or.inl lateUtility⟩
  refine ⟨mechanismOpen, utilityOpen, ?_⟩
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single firstStep) secondStep

/-- Symmetrically, the early decision's mechanism is s-reachable to the late
decision through the same owned utility term. -/
theorem early_oriented_late :
    UtilityView.OrientedRelevance cycleView earlySite lateSite := by
  refine ⟨jointSite, late_relevant, ?_⟩
  let graphParents :=
    UtilityView.mechanismGraphParents cycleView earlySite
  let evidence := UtilityView.sReachConditioning cycleView lateSite
  let mechanismNode : UtilityView.MechanismGraphNode cycleView () :=
    .mechanism
  let early : UtilityView.MechanismGraphNode cycleView () :=
    .object (.base .early)
  let utility : UtilityView.MechanismGraphNode cycleView () :=
    .object (.utility jointSite)
  have mechanismEarly :
      FiniteBNMoralSeparation.DirectedEdge graphParents
        mechanismNode early := by
    simp [FiniteBNMoralSeparation.DirectedEdge, graphParents,
      mechanismNode, early, UtilityView.mechanismGraphParents, earlySite]
  have earlyUtility :
      FiniteBNMoralSeparation.DirectedEdge graphParents early utility := by
    simp [FiniteBNMoralSeparation.DirectedEdge, graphParents, early,
      utility, UtilityView.mechanismGraphParents,
      MAIDRequisiteObservation.UtilityView.term,
      cycleView, jointSite, jointTerm]
    exact Finset.mem_insert_self _ _
  have mechanismOpen : mechanismNode ∉ evidence := by
    simp [mechanismNode, evidence, UtilityView.sReachConditioning]
  have earlyOpen : early ∉ evidence := by
    simp [early, evidence, UtilityView.sReachConditioning,
      lateSite, exampleDiagram, parents]
  have utilityOpen : utility ∉ evidence := by
    simp [utility, evidence, UtilityView.sReachConditioning]
  have mechanismAncestor :
      FiniteBNMoralSeparation.InAncestralClosure graphParents
        {mechanismNode} {utility} evidence mechanismNode := by
    refine ⟨mechanismNode, ?_, Relation.ReflTransGen.refl⟩
    simp [FiniteBNMoralSeparation.queryRoots]
  have earlyAncestor :
      FiniteBNMoralSeparation.InAncestralClosure graphParents
        {mechanismNode} {utility} evidence early := by
    refine ⟨utility, ?_, Relation.ReflTransGen.single earlyUtility⟩
    simp [FiniteBNMoralSeparation.queryRoots]
  have utilityAncestor :
      FiniteBNMoralSeparation.InAncestralClosure graphParents
        {mechanismNode} {utility} evidence utility := by
    refine ⟨utility, ?_, Relation.ReflTransGen.refl⟩
    simp [FiniteBNMoralSeparation.queryRoots]
  have firstStep : FiniteBNMoralSeparation.MoralAdjacent graphParents
      {mechanismNode} {utility} evidence mechanismNode early :=
    ⟨by simp [mechanismNode, early], mechanismOpen, earlyOpen,
      mechanismAncestor, earlyAncestor, Or.inl mechanismEarly⟩
  have secondStep : FiniteBNMoralSeparation.MoralAdjacent graphParents
      {mechanismNode} {utility} evidence early utility :=
    ⟨by simp [early, utility], earlyOpen, utilityOpen,
      earlyAncestor, utilityAncestor, Or.inl earlyUtility⟩
  refine ⟨mechanismOpen, utilityOpen, ?_⟩
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single firstStep) secondStep

/-- The two opposite same-owner reliance edges form the sufficient-recall
counterexample, despite the object-level MAID itself remaining a DAG. -/
theorem cycleView_not_sReachAcyclic :
    ¬ UtilityView.SReachAcyclic cycleView := by
  intro hacyclic
  have cycle : Relation.TransGen
      (fun source target : DecisionSite exampleDiagram () =>
        UtilityView.OrientedRelevance cycleView source target)
      earlySite earlySite :=
    Relation.TransGen.tail
      (Relation.TransGen.single early_oriented_late)
      late_oriented_early
  exact hacyclic () earlySite cycle

end TwoDecision

end GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
