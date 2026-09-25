/-
# EXP-105: utility-augmented MAID factorization

The augmented law is only the injective image of canonical native play.
Canonical augmented assignments retain the native factor product and every
utility factor has mass one.  An assignment outside that image disagrees at a
utility leaf, whose deterministic kernel gives both sides point mass zero.
-/

import GameTheory.Experimental.PostArchitecture.MAIDUtilityGraphFinite
import GameTheory.Math.Probability.Support

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.MAIDFactorization
open GameTheory.Experimental.PostArchitecture.MAIDFiniteBNBridge
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityGraphFinite

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node} {semantics : Semantics diagram}

/-- The proof-side augmented law is an injective image of canonical native
play, not another evaluator. -/
def augmentedLaw [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (policy : Policy diagram) : PMF (AugmentedAssignment view owner) :=
  ((nativeBehavioralGameForm semantics).play policy).map
    (augmentAssignment view (owner := owner))

private theorem utilityParentConfiguration_projectBase
    [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (assignment : AugmentedAssignment view owner)
    (site : view.UtilitySite owner) :
    utilityParentConfiguration view (owner := owner) site
        (parentConfiguration (graphValue view (owner := owner))
          (view.graphParents (owner := owner))
          assignment (.utility site)) =
      Assignment.restrict diagram (projectBase view (owner := owner) assignment)
        (view.term site).parents := by
  funext parent
  rfl

private theorem localFactor_base_augmentAssignment
    [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (policy : Policy diagram) (assignment : Assignment diagram)
    (node : Node) :
    localFactor (graphValue view (owner := owner))
        (view.graphParents (owner := owner))
        (augmentedKernels view (owner := owner) policy)
        (augmentAssignment view (owner := owner) assignment)
        (.base node : UtilityView.GraphNode view owner) =
      localFactor diagram.Value (effectiveParents diagram)
        (effectiveKernels semantics policy) assignment node := by
  unfold localFactor
  rw [augmentedKernels_base,
    baseParentConfiguration_augmentAssignment]
  rfl

private theorem localFactor_utility_augmentAssignment
    [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (policy : Policy diagram) (assignment : Assignment diagram)
    (site : view.UtilitySite owner) :
    localFactor (graphValue view (owner := owner))
        (view.graphParents (owner := owner))
        (augmentedKernels view (owner := owner) policy)
        (augmentAssignment view (owner := owner) assignment)
        (.utility site : UtilityView.GraphNode view owner) = 1 := by
  classical
  simp only [localFactor, augmentedKernels_utility,
    utilityParentConfiguration_augmentAssignment, augmentAssignment_utility]
  simp [DFunLike.coe, PMF.pure]
/-- Augmenting a canonical assignment adds only unit-mass deterministic
utility factors. -/
theorem factorProduct_augmentAssignment
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (policy : Policy diagram) (assignment : Assignment diagram) :
    factorProduct (graphValue view (owner := owner))
        (view.graphParents (owner := owner))
        (augmentedKernels view (owner := owner) policy) Finset.univ
        (augmentAssignment view (owner := owner) assignment) =
      factorProduct diagram.Value (effectiveParents diagram)
        (effectiveKernels semantics policy) Finset.univ assignment := by
  simp only [factorProduct]
  calc
    _ = ∏ node : Node ⊕ view.UtilitySite owner,
        Sum.elim
          (fun base =>
            localFactor (graphValue view (owner := owner))
              (view.graphParents (owner := owner))
              (augmentedKernels view (owner := owner) policy)
              (augmentAssignment view (owner := owner) assignment)
              (.base base : UtilityView.GraphNode view owner))
          (fun site =>
            localFactor (graphValue view (owner := owner))
              (view.graphParents (owner := owner))
              (augmentedKernels view (owner := owner) policy)
              (augmentAssignment view (owner := owner) assignment)
              (.utility site : UtilityView.GraphNode view owner)) node := by
      apply Fintype.prod_equiv (graphNodeEquiv view owner)
      intro node
      cases node <;> rfl
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp_rw [localFactor_base_augmentAssignment,
        localFactor_utility_augmentAssignment]
      simp

private theorem exists_utility_mismatch_of_inconsistent
    (view : UtilityView semantics) {owner : Player}
    (assignment : AugmentedAssignment view owner)
    (hinconsistent :
      assignment ≠ augmentAssignment view (owner := owner)
        (projectBase view (owner := owner) assignment)) :
    ∃ site : view.UtilitySite owner,
      assignment (.utility site) ≠
        augmentAssignment view (owner := owner)
          (projectBase view (owner := owner) assignment) (.utility site) := by
  by_contra hnone
  apply hinconsistent
  funext node
  cases node with
  | base _ => rfl
  | utility site =>
      by_contra hne
      exact hnone ⟨site, hne⟩

private theorem localFactor_utility_eq_zero_of_mismatch
    [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (policy : Policy diagram) (assignment : AugmentedAssignment view owner)
    (site : view.UtilitySite owner)
    (hmismatch :
      assignment (.utility site) ≠
        augmentAssignment view (owner := owner)
          (projectBase view (owner := owner) assignment) (.utility site)) :
    localFactor (graphValue view (owner := owner))
      (view.graphParents (owner := owner))
      (augmentedKernels view (owner := owner) policy) assignment
        (.utility site : UtilityView.GraphNode view owner) = 0 := by
  classical
  simp only [augmentAssignment_utility] at hmismatch
  simp only [localFactor, augmentedKernels_utility,
    utilityParentConfiguration_projectBase]
  simp only [DFunLike.coe, PMF.pure]
  split_ifs with hequal
  · exact (hmismatch hequal).elim
  · rfl
/-- An augmented assignment outside the canonical image has a zero utility
factor and therefore zero total local-factor product. -/
theorem factorProduct_eq_zero_of_inconsistent
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (policy : Policy diagram) (assignment : AugmentedAssignment view owner)
    (hinconsistent :
      assignment ≠ augmentAssignment view (owner := owner)
        (projectBase view (owner := owner) assignment)) :
    factorProduct (graphValue view (owner := owner))
      (view.graphParents (owner := owner))
      (augmentedKernels view (owner := owner) policy) Finset.univ assignment = 0 := by
  obtain ⟨site, hmismatch⟩ :=
    exists_utility_mismatch_of_inconsistent view assignment hinconsistent
  unfold factorProduct
  apply Finset.prod_eq_zero (Finset.mem_univ (.utility site))
  exact localFactor_utility_eq_zero_of_mismatch
    view policy assignment site hmismatch

/-- The mapped canonical law also assigns zero mass to every inconsistent
augmented target. -/
theorem augmentedLaw_prob_eq_zero_of_inconsistent
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (policy : Policy diagram) (assignment : AugmentedAssignment view owner)
    (hinconsistent :
      assignment ≠ augmentAssignment view (owner := owner)
        (projectBase view (owner := owner) assignment)) :
    (augmentedLaw view owner policy) assignment = 0 := by
  apply ((augmentedLaw view owner policy).apply_eq_zero_iff assignment).mpr
  rw [augmentedLaw, PMF.support_map]
  rintro ⟨base, _, rfl⟩
  exact hinconsistent (by simp)

/-- The mapped canonical law factorizes over effective base kernels and
deterministic configuration-valued utility leaves at every augmented target.
-/
theorem augmentedLaw_factorizes
    [Fintype Node] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (policy : Policy diagram) :
    Factorizes (graphValue view (owner := owner))
      (augmentedLaw view owner policy) (view.graphParents (owner := owner))
      (augmentedKernels view (owner := owner) policy) := by
  classical
  intro assignment
  by_cases hconsistent :
      assignment = augmentAssignment view (owner := owner)
        (projectBase view (owner := owner) assignment)
  · let base := projectBase view (owner := owner) assignment
    have hassignment : assignment =
        augmentAssignment view (owner := owner) base := hconsistent
    rw [hassignment]
    calc
      ((augmentedLaw view owner policy)
          (augmentAssignment view (owner := owner) base)).toReal =
          (((nativeBehavioralGameForm semantics).play policy) base).toReal :=
        congrArg ENNReal.toReal <|
          pmf_map_apply_of_injective _
            (augmentAssignment_injective view) base
      _ = factorProduct diagram.Value (effectiveParents diagram)
          (effectiveKernels semantics policy) Finset.univ base :=
        native_play_factorizes topological semantics policy base
      _ = factorProduct (graphValue view (owner := owner))
          (view.graphParents (owner := owner))
          (augmentedKernels view (owner := owner) policy) Finset.univ
            (augmentAssignment view (owner := owner) base) :=
        (factorProduct_augmentAssignment view owner policy base).symm
  · rw [augmentedLaw_prob_eq_zero_of_inconsistent
        view owner policy assignment hconsistent,
      factorProduct_eq_zero_of_inconsistent
        view owner policy assignment hconsistent]
    simp

/-! ## Split-term consumer -/

namespace SplitTermControl

open MAIDRequisiteObservation.SplitMerged

/-- The two distinct utility leaves of the split-term model consume the
generic mapped-law factorization without being merged into one sink. -/
theorem split_factorizes :
    Factorizes (graphValue splitView)
      (augmentedLaw splitView () MAIDFactorization.ThreeNodeControl.policy)
      splitView.graphParents
      (augmentedKernels splitView MAIDFactorization.ThreeNodeControl.policy) :=
  augmentedLaw_factorizes Nonrequisite.topologicalParents splitView ()
    MAIDFactorization.ThreeNodeControl.policy

end SplitTermControl

end GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization
