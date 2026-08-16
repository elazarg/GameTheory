/-
# EXP-109: bounded graph-node enumeration and one-step deciders

This module supplies the executable boundary for the pruning checker.  A
caller provides a topological order of the causal nodes; utility sites are
enumerated from their owner-indexed list.  No finite-carrier instance is
stored or synthesized.  Directed reachability is deliberately left as a
parameter: a later module can provide its bounded path decider without
changing these one-step definitions.
-/

import GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph

open GameTheory.Languages.MAID
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
open MAIDRequisiteObservation

universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}
variable {semantics : Semantics diagram}

namespace UtilityView

variable (view : MAIDRequisiteObservation.UtilityView semantics)
variable (owner : Player)

/-! ## Explicit graph-node enumeration -/

/-- All graph nodes for one owner, in causal topological order followed by
the owner's utility sites.  The topological order is supplied by the caller,
so this definition does not require a stored finite-carrier instance. -/
def graphNodeList [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    List (view.GraphNode owner) :=
  topological.order.map
      (fun node =>
        (.base node : view.GraphNode owner)) ++
    (List.finRange (view.terms owner).length).map
      (fun term =>
        (.utility term : view.GraphNode owner))

private theorem graphNodeList_base_mem
    [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (node : Node) :
    (.base node : view.GraphNode owner) ∈ graphNodeList view owner topological := by
  apply List.mem_append.mpr
  left
  apply List.mem_map.mpr
  exact ⟨node, topological.complete node, rfl⟩

private theorem graphNodeList_utility_mem
    [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (term : view.UtilitySite owner) :
    (.utility term : view.GraphNode owner) ∈ graphNodeList view owner topological := by
  apply List.mem_append.mpr
  right
  apply List.mem_map.mpr
  exact ⟨term, List.mem_finRange term, rfl⟩

/-- Every graph node occurs in the explicit enumeration. -/
theorem graphNode_mem_graphNodeList [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (node : view.GraphNode owner) :
    node ∈ graphNodeList view owner topological := by
  cases node with
  | base node => exact graphNodeList_base_mem (view := view) (owner := owner) topological node
  | utility term => exact graphNodeList_utility_mem (view := view) (owner := owner) topological term

private theorem graphNodeList_base_nodup
    [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    (topological.order.map
      (fun node => (.base node : view.GraphNode owner))).Nodup := by
  apply List.Nodup.map
  intro first second equality
  exact MAIDRequisiteObservation.UtilityView.GraphNode.base.inj equality
  exact topological.nodup

private theorem graphNodeList_utility_nodup
    [DecidableEq Node] :
    ((List.finRange (view.terms owner).length).map
      (fun term => (.utility term : view.GraphNode owner))).Nodup := by
  apply List.Nodup.map
  intro first second equality
  exact MAIDRequisiteObservation.UtilityView.GraphNode.utility.inj equality
  exact List.nodup_finRange _

private theorem graphNodeList_disjoint
    [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    (topological.order.map
      (fun node => (.base node : view.GraphNode owner))).Disjoint
      ((List.finRange (view.terms owner).length).map
        (fun term => (.utility term : view.GraphNode owner))) := by
  intro node hbase hutility
  rw [List.mem_map] at hbase hutility
  obtain ⟨base, _, hbase⟩ := hbase
  obtain ⟨term, _, hutility⟩ := hutility
  cases hbase.trans hutility.symm

/-- The explicit graph-node enumeration has no duplicate nodes. -/
theorem graphNodeList_nodup [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    (graphNodeList view owner topological).Nodup := by
  unfold graphNodeList
  apply List.Nodup.append
  · exact graphNodeList_base_nodup (view := view) (owner := owner) topological
  · exact graphNodeList_utility_nodup (view := view) (owner := owner)
  · exact graphNodeList_disjoint (view := view) (owner := owner) topological

/-- Membership in the explicit enumeration is exactly membership in its
base-node or utility-site summand. -/
theorem mem_graphNodeList_iff [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (node : view.GraphNode owner) :
    node ∈ graphNodeList view owner topological ↔
      (∃ base, base ∈ topological.order ∧
        node = .base base) ∨
      (∃ term : view.UtilitySite owner, node = .utility term) := by
  constructor
  · intro hnode
    rw [graphNodeList, List.mem_append, List.mem_map, List.mem_map] at hnode
    rcases hnode with hnode | hnode
    · obtain ⟨base, hbase, equality⟩ := hnode
      exact Or.inl ⟨base, hbase, equality.symm⟩
    · obtain ⟨term, hterm, equality⟩ := hnode
      exact Or.inr ⟨term, equality.symm⟩
  · rintro (⟨base, hbase, rfl⟩ | ⟨term, rfl⟩)
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨base, hbase, rfl⟩)
    · exact List.mem_append_right _
        (List.mem_map.mpr ⟨term, List.mem_finRange term, rfl⟩)

/-! ## One-step directed-edge seam -/

/-- A directed edge in the graph selected by an arbitrary decision-parent
candidate. -/
def DirectedEdgeUnder [DecidableEq Node]
    (decisionParents : DecisionParentMap Node)
    (parent child : view.GraphNode owner) : Prop :=
  parent ∈ graphParentsUnder view decisionParents child

instance directedEdgeUnderDecidable [DecidableEq Node]
    (decisionParents : DecisionParentMap Node)
    (parent child : view.GraphNode owner) :
    Decidable (DirectedEdgeUnder view owner decisionParents parent child) := by
  unfold DirectedEdgeUnder
  infer_instance

/-- Boolean test for one directed edge. -/
def directedEdgeUnder? [DecidableEq Node]
    (decisionParents : DecisionParentMap Node)
    (parent child : view.GraphNode owner) : Bool :=
  decide (DirectedEdgeUnder view owner decisionParents parent child)

theorem directedEdgeUnder?_eq_true_iff [DecidableEq Node]
    (decisionParents : DecisionParentMap Node)
    (parent child : view.GraphNode owner) :
    directedEdgeUnder? view owner decisionParents parent child = true ↔
      DirectedEdgeUnder view owner decisionParents parent child := by
  simp only [directedEdgeUnder?, decide_eq_true_eq]

/-- Relation-valued edge seam consumed by a later bounded reachability
decider. -/
def ancestryEdgeUnder [DecidableEq Node]
    (decisionParents : DecisionParentMap Node) :
    view.GraphNode owner → view.GraphNode owner → Prop :=
  DirectedEdgeUnder view owner decisionParents

instance ancestryEdgeUnderDecidable [DecidableEq Node]
    (decisionParents : DecisionParentMap Node)
    (parent child : view.GraphNode owner) :
    Decidable (ancestryEdgeUnder view owner decisionParents parent child) :=
  directedEdgeUnderDecidable view owner decisionParents parent child

/-! ## Ancestral-moral one-step seam -/

/-- The local ancestral-moral adjacency predicate with ancestry supplied by a
caller.  The coparent witness is bounded by the explicit graph-node list. -/
def AncestralMoralAdjacentUnder [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (ancestral : view.GraphNode owner → Prop)
    (evidence : Finset (view.GraphNode owner))
    (first second : view.GraphNode owner) : Prop :=
  first ≠ second ∧
    first ∉ evidence ∧
    second ∉ evidence ∧
    ancestral first ∧
    ancestral second ∧
    (DirectedEdgeUnder view owner decisionParents first second ∨
      DirectedEdgeUnder view owner decisionParents second first ∨
      ∃ child ∈ graphNodeList view owner topological,
        ancestral child ∧
          DirectedEdgeUnder view owner decisionParents first child ∧
          DirectedEdgeUnder view owner decisionParents second child)

instance ancestralMoralAdjacentUnderDecidable [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (ancestral : view.GraphNode owner → Prop)
    [DecidablePred ancestral]
    (evidence : Finset (view.GraphNode owner))
    (first second : view.GraphNode owner) :
    Decidable (AncestralMoralAdjacentUnder view owner topological
      decisionParents ancestral evidence first second) := by
  unfold AncestralMoralAdjacentUnder
  infer_instance

/-- Boolean test for ancestral-moral adjacency.  Reachability is supplied by
the `ancestral` predicate and is not implemented in this module. -/
def ancestralMoralAdjacentUnder? [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (ancestral : view.GraphNode owner → Prop)
    [DecidablePred ancestral]
    (evidence : Finset (view.GraphNode owner))
    (first second : view.GraphNode owner) : Bool :=
  decide (AncestralMoralAdjacentUnder view owner topological decisionParents
    ancestral evidence first second)

theorem ancestralMoralAdjacentUnder?_eq_true_iff [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (ancestral : view.GraphNode owner → Prop)
    [DecidablePred ancestral]
    (evidence : Finset (view.GraphNode owner))
    (first second : view.GraphNode owner) :
    ancestralMoralAdjacentUnder? view owner topological decisionParents
        ancestral evidence first second = true ↔
      AncestralMoralAdjacentUnder view owner topological decisionParents
        ancestral evidence first second := by
  simp only [ancestralMoralAdjacentUnder?, decide_eq_true_eq]

end UtilityView

end GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
