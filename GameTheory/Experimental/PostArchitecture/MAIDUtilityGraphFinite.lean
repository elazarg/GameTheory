/-
# EXP-105: finite utility-augmented MAID graphs

This module supplies the finite structural and local-kernel layer for the
proof-side utility augmentation.  It adds deterministic utility sinks without
defining another evaluator or joint law.
-/

import GameTheory.Experimental.PostArchitecture.MAIDFiniteBNBridge
import GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDUtilityGraphFinite

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.MAIDFactorization
open GameTheory.Experimental.PostArchitecture.MAIDFiniteBNBridge
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node} {semantics : Semantics diagram}

/-- Augmented graph nodes are exactly base nodes or one owner's finite utility
sites. -/
def graphNodeEquiv (view : UtilityView semantics) (owner : Player) :
    UtilityView.GraphNode view owner ≃ Node ⊕ view.UtilitySite owner where
  toFun
    | .base node => Sum.inl node
    | .utility site => Sum.inr site
  invFun
    | Sum.inl node => .base node
    | Sum.inr site => .utility site
  left_inv node := by cases node <;> rfl
  right_inv node := by cases node <;> rfl

instance graphNodeFintype [Fintype Node]
    (view : UtilityView semantics) (owner : Player) :
    Fintype (UtilityView.GraphNode view owner) :=
  Fintype.ofEquiv (Node ⊕ view.UtilitySite owner) (graphNodeEquiv view owner).symm

instance graphValueFintype
    [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    (view : UtilityView semantics) {owner : Player}
    (node : UtilityView.GraphNode view owner) :
    Fintype (graphValue view node) := by
  cases node with
  | base baseNode => exact inferInstanceAs (Fintype (diagram.Value baseNode))
  | utility site =>
      unfold graphValue Config
      infer_instance

instance graphValueDecidableEq
    [DecidableEq Node]
    [∀ node, DecidableEq (diagram.Value node)]
    (view : UtilityView semantics) {owner : Player}
    (node : UtilityView.GraphNode view owner) :
    DecidableEq (graphValue view node) := by
  cases node with
  | base baseNode =>
      exact inferInstanceAs (DecidableEq (diagram.Value baseNode))
  | utility site =>
      unfold graphValue Config
      infer_instance

private theorem baseParent_mem [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (node : Node) (parent : {parent // parent ∈ effectiveParents diagram node}) :
    (.base parent.1 : UtilityView.GraphNode view owner) ∈
      view.graphParents (.base node) := by
  simp [UtilityView.graphParents, parent.2]

/-- Read a base node's effective-parent configuration from the corresponding
augmented base-parent coordinates. -/
def baseParentConfiguration [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player} (node : Node)
    (configuration :
      ParentConfiguration (graphValue view (owner := owner))
        (view.graphParents (owner := owner))
        (.base node : UtilityView.GraphNode view owner)) :
    ParentConfiguration diagram.Value (effectiveParents diagram) node :=
  fun parent => configuration
    ⟨.base parent.1, baseParent_mem view node parent⟩

@[simp]
theorem baseParentConfiguration_apply [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player} (node : Node)
    (configuration :
      ParentConfiguration (graphValue view (owner := owner))
        (view.graphParents (owner := owner))
        (.base node : UtilityView.GraphNode view owner))
    (parent : {parent // parent ∈ effectiveParents diagram node}) :
    baseParentConfiguration view node configuration parent =
      configuration ⟨.base parent.1, baseParent_mem view node parent⟩ :=
  rfl

private theorem utilityParent_mem [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (site : view.UtilitySite owner)
    (parent : {parent // parent ∈ (view.term site).parents}) :
    (.base parent.1 : UtilityView.GraphNode view owner) ∈
      view.graphParents (.utility site) := by
  simp [UtilityView.graphParents, parent.2]

/-- Read a utility leaf's exact term-parent configuration from its augmented
base parents. -/
def utilityParentConfiguration [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (site : view.UtilitySite owner)
    (configuration :
      ParentConfiguration (graphValue view (owner := owner))
        (view.graphParents (owner := owner)) (.utility site)) :
    Config diagram (view.term site).parents :=
  fun parent => configuration
    ⟨.base parent.1, utilityParent_mem view site parent⟩

@[simp]
theorem utilityParentConfiguration_apply [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (site : view.UtilitySite owner)
    (configuration :
      ParentConfiguration (graphValue view (owner := owner))
        (view.graphParents (owner := owner)) (.utility site))
    (parent : {parent // parent ∈ (view.term site).parents}) :
    utilityParentConfiguration view site configuration parent =
      configuration ⟨.base parent.1, utilityParent_mem view site parent⟩ :=
  rfl

@[simp]
theorem baseParentConfiguration_augmentAssignment [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (assignment : Assignment diagram) (node : Node) :
    baseParentConfiguration view (owner := owner) node
        (parentConfiguration (graphValue view (owner := owner))
          (view.graphParents (owner := owner))
          (augmentAssignment view (owner := owner) assignment)
          (.base node : UtilityView.GraphNode view owner)) =
      parentConfiguration diagram.Value (effectiveParents diagram)
        assignment node := by
  funext parent
  rfl

@[simp]
theorem utilityParentConfiguration_augmentAssignment [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (assignment : Assignment diagram) (site : view.UtilitySite owner) :
    utilityParentConfiguration view (owner := owner) site
        (parentConfiguration (graphValue view (owner := owner))
          (view.graphParents (owner := owner))
          (augmentAssignment view (owner := owner) assignment)
          (.utility site : UtilityView.GraphNode view owner)) =
      Assignment.restrict diagram assignment (view.term site).parents := by
  funext parent
  rfl

/-- Base nodes retain their canonical effective kernels; utility leaves
deterministically copy their exact parent configurations. -/
def augmentedKernels [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (policy : Policy diagram) :
    LocalKernels (graphValue view (owner := owner))
      (view.graphParents (owner := owner))
  | .base node, configuration =>
      effectiveKernels semantics policy node
        (baseParentConfiguration view node configuration)
  | .utility site, configuration =>
      FinDist.pure (utilityParentConfiguration view site configuration)

@[simp]
theorem augmentedKernels_base [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (policy : Policy diagram)
    (node : Node)
    (configuration :
      ParentConfiguration (graphValue view (owner := owner))
        (view.graphParents (owner := owner))
        (.base node : UtilityView.GraphNode view owner)) :
    augmentedKernels view policy (.base node) configuration =
      effectiveKernels semantics policy node
        (baseParentConfiguration view node configuration) :=
  rfl

@[simp]
theorem augmentedKernels_utility [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (policy : Policy diagram)
    (site : view.UtilitySite owner)
    (configuration :
      ParentConfiguration (graphValue view (owner := owner))
        (view.graphParents (owner := owner)) (.utility site)) :
    augmentedKernels view policy (.utility site) configuration =
      FinDist.pure (utilityParentConfiguration view site configuration) :=
  rfl

/-- Base nodes in effective topological order, followed by every utility
site. -/
def augmentedOrder (view : UtilityView semantics) (owner : Player)
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    List (UtilityView.GraphNode view owner) :=
  topological.order.map UtilityView.GraphNode.base ++
    (List.finRange (view.terms owner).length).map
      UtilityView.GraphNode.utility

@[simp]
theorem augmentedOrder_length (view : UtilityView semantics) (owner : Player)
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    (augmentedOrder view owner topological).length =
      topological.order.length + (view.terms owner).length := by
  simp [augmentedOrder]

@[simp]
theorem mem_augmentedOrder_base
    (view : UtilityView semantics) (owner : Player)
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (node : Node) :
    (.base node : UtilityView.GraphNode view owner) ∈
      augmentedOrder view owner topological := by
  simp [augmentedOrder, topological.complete node]

@[simp]
theorem mem_augmentedOrder_utility
    (view : UtilityView semantics) (owner : Player)
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (site : view.UtilitySite owner) :
    (.utility site : UtilityView.GraphNode view owner) ∈
      augmentedOrder view owner topological := by
  simp [augmentedOrder]

/-- Appending utility sinks preserves the effective base topological order. -/
def augmentedTopologicalOrder [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    GameTheory.Math.DAG.TopologicalOrder
      (view.graphParents (owner := owner)) where
  order := augmentedOrder view owner topological
  nodup := by
    unfold augmentedOrder
    apply List.Nodup.append
    · exact topological.nodup.map fun _ _ hequal =>
        UtilityView.GraphNode.base.inj hequal
    · exact (List.nodup_finRange _).map fun _ _ hequal =>
        UtilityView.GraphNode.utility.inj hequal
    · rw [List.disjoint_left]
      intro graphNode hbase hutility
      obtain ⟨_, _, hbaseEq⟩ := List.mem_map.mp hbase
      obtain ⟨_, _, hutilityEq⟩ := List.mem_map.mp hutility
      rw [← hbaseEq] at hutilityEq
      cases hutilityEq
  complete node := by
    cases node with
    | base baseNode => exact mem_augmentedOrder_base view owner topological baseNode
    | utility site => exact mem_augmentedOrder_utility view owner topological site
  respects := by
    intro index parent hparent
    generalize hchildEq :
      (augmentedOrder view owner topological)[index] = child at hparent
    cases child with
    | base child =>
        have hindexBase : index.val < topological.order.length := by
          by_contra hnot
          have hbaseLength : topological.order.length ≤ index.val :=
            Nat.le_of_not_gt hnot
          have hbaseLengthMapped :
              (topological.order.map fun node =>
                (.base node : UtilityView.GraphNode view owner)).length ≤
                index.val := by
            simpa using hbaseLength
          have hchildEq' :
              (augmentedOrder view owner topological)[index.val] =
                (.base child : UtilityView.GraphNode view owner) := by
            simpa using hchildEq
          unfold augmentedOrder at hchildEq'
          rw [List.getElem_append_right hbaseLengthMapped,
            List.getElem_map] at hchildEq'
          cases hchildEq'
        let childIndex : Fin topological.order.length :=
          ⟨index.val, hindexBase⟩
        have hchild : topological.order[childIndex] = child := by
          have hindexMapped :
              index.val <
                (topological.order.map fun node =>
                  (.base node : UtilityView.GraphNode view owner)).length := by
            simpa using hindexBase
          have hchildEq' :
              (augmentedOrder view owner topological)[index.val] =
                (.base child : UtilityView.GraphNode view owner) := by
            simpa using hchildEq
          unfold augmentedOrder at hchildEq'
          rw [List.getElem_append_left hindexMapped,
            List.getElem_map] at hchildEq'
          exact UtilityView.GraphNode.base.inj hchildEq'
        obtain ⟨baseParent, hbaseParent, hparentEq⟩ :=
          Finset.mem_image.mp hparent
        obtain ⟨earlier, hearlier, hvalue⟩ :=
          topological.respects childIndex baseParent
            (by
              simpa only [hchild] using
                effectiveParents_subset child hbaseParent)
        let augmentedEarlier : Fin (augmentedOrder view owner topological).length :=
          ⟨earlier.val, by
            rw [augmentedOrder_length]
            omega⟩
        refine ⟨augmentedEarlier, hearlier, ?_⟩
        have hearlierMapped :
            earlier.val <
              (topological.order.map fun node =>
                (.base node : UtilityView.GraphNode view owner)).length := by
          rw [List.length_map]
          exact earlier.isLt
        have hget :
            (augmentedOrder view owner topological)[earlier.val] =
              (.base baseParent : UtilityView.GraphNode view owner) := by
          unfold augmentedOrder
          rw [List.getElem_append_left hearlierMapped,
            List.getElem_map]
          exact congrArg
            (fun node => (.base node : UtilityView.GraphNode view owner)) hvalue
        simpa [augmentedEarlier] using hget.trans hparentEq
    | utility site =>
        have hbaseLength : topological.order.length ≤ index.val := by
          by_contra hnot
          have hindexBase : index.val < topological.order.length :=
            Nat.lt_of_not_ge hnot
          have hindexMapped :
              index.val <
                (topological.order.map fun node =>
                  (.base node : UtilityView.GraphNode view owner)).length := by
            simpa using hindexBase
          have hchildEq' :
              (augmentedOrder view owner topological)[index.val] =
                (.utility site : UtilityView.GraphNode view owner) := by
            simpa using hchildEq
          unfold augmentedOrder at hchildEq'
          rw [List.getElem_append_left hindexMapped,
            List.getElem_map] at hchildEq'
          cases hchildEq'
        obtain ⟨baseParent, _, hparentEq⟩ := Finset.mem_image.mp hparent
        obtain ⟨parentIndex, hparentBound, hvalue⟩ :=
          List.mem_iff_getElem.mp (topological.complete baseParent)
        let augmentedEarlier : Fin (augmentedOrder view owner topological).length :=
          ⟨parentIndex, by
            rw [augmentedOrder_length]
            omega⟩
        refine ⟨augmentedEarlier, ?_, ?_⟩
        · calc
            augmentedEarlier.val = parentIndex := rfl
            _ < topological.order.length := hparentBound
            _ ≤ index.val := hbaseLength
        have hparentMapped :
            parentIndex <
              (topological.order.map fun node =>
                (.base node : UtilityView.GraphNode view owner)).length := by
          simpa using hparentBound
        have hget :
            (augmentedOrder view owner topological)[parentIndex] =
              (.base baseParent : UtilityView.GraphNode view owner) := by
          unfold augmentedOrder
          rw [List.getElem_append_left hparentMapped,
            List.getElem_map, hvalue]
        simpa [augmentedEarlier] using hget.trans hparentEq

end GameTheory.Experimental.PostArchitecture.MAIDUtilityGraphFinite
