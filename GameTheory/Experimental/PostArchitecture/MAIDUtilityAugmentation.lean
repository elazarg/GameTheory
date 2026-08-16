/-
# EXP-105: proof-side MAID utility augmentation

Utility leaves carry their exact typed parent configurations.  Augmentation is
a deterministic view of a canonical MAID assignment, not another evaluator or
probability semantics.

The transparent-fiber experiment keeps the node universe below the value
family universe, expressed by `Structure.{uPlayer, uNode, max uNode uValue}`.
Supporting a lower value universe would require lifting base fibers and is
outside this transport-free slice.
-/

import GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation

open GameTheory.Languages.MAID
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
variable {semantics : Semantics diagram}

/-- The typed value stored at a proof-side augmented graph node.  A utility
leaf stores exactly the configuration read by its utility term, never `ℝ`. -/
def graphValue (view : UtilityView semantics) {owner : Player} :
    UtilityView.GraphNode view owner → Type (max uNode uValue)
  | .base node => diagram.Value node
  | .utility site => Config diagram (view.term site).parents

/-- A dependent assignment on the base and utility-leaf graph. -/
abbrev AugmentedAssignment (view : UtilityView semantics) (owner : Player) :=
  (node : UtilityView.GraphNode view owner) → graphValue view node

/-- Deterministically augment a canonical assignment with every utility
term's exact parent restriction. -/
def augmentAssignment (view : UtilityView semantics) {owner : Player}
    (assignment : Assignment diagram) : AugmentedAssignment view owner
  | .base node => assignment node
  | .utility site =>
      Assignment.restrict diagram assignment (view.term site).parents

/-- Forget utility leaves and retain the canonical base assignment. -/
def projectBase (view : UtilityView semantics) {owner : Player}
    (assignment : AugmentedAssignment view owner) : Assignment diagram :=
  fun node => assignment (.base node)

@[simp]
theorem augmentAssignment_base (view : UtilityView semantics) {owner : Player}
    (assignment : Assignment diagram) (node : Node) :
    augmentAssignment view (owner := owner) assignment
        (.base node : UtilityView.GraphNode view owner) = assignment node :=
  rfl

@[simp]
theorem augmentAssignment_utility
    (view : UtilityView semantics) {owner : Player}
    (assignment : Assignment diagram) (site : view.UtilitySite owner) :
    augmentAssignment view (owner := owner) assignment (.utility site) =
      Assignment.restrict diagram assignment (view.term site).parents :=
  rfl

@[simp]
theorem projectBase_augmentAssignment
    (view : UtilityView semantics) {owner : Player}
    (assignment : Assignment diagram) :
    projectBase view (owner := owner)
      (augmentAssignment view (owner := owner) assignment) = assignment :=
  rfl

/-- Proof-side augmentation loses no base information. -/
theorem augmentAssignment_injective
    (view : UtilityView semantics) {owner : Player} :
    Function.Injective (augmentAssignment view (owner := owner)) := by
  intro first second hequal
  funext node
  exact congrFun hequal (.base node : UtilityView.GraphNode view owner)

/-- Evaluate an owner's utility leaves from their stored typed
configurations. -/
def ownerPayoff (view : UtilityView semantics) (owner : Player)
    (assignment : AugmentedAssignment view owner) : ℝ :=
  ∑ site : view.UtilitySite owner,
    (view.term site).payoff (assignment (.utility site))

/-- Augmented leaf payoff is exactly the canonical semantic utility certified
by the utility view. -/
theorem ownerPayoff_augmentAssignment
    (view : UtilityView semantics) (owner : Player)
    (assignment : Assignment diagram) :
    ownerPayoff view owner (augmentAssignment view assignment) =
      semantics.utility owner assignment := by
  rw [view.utility_eq_sum]
  apply Finset.sum_congr rfl
  intro site _
  rfl

/-! ## Split-term control -/

namespace SplitTermControl

open MAIDRequisiteObservation.SplitMerged

/-- Distinct reward and signal leaves consume the generic augmentation without
merging their typed configurations. -/
theorem split_ownerPayoff_agrees
    (assignment : Assignment Nonrequisite.model) :
    ownerPayoff splitView () (augmentAssignment splitView assignment) =
      SplitMerged.semantics.utility () assignment :=
  ownerPayoff_augmentAssignment splitView () assignment

end SplitTermControl

end GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
