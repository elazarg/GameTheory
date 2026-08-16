/-
# EXP-107: relevant utility continuation under restore-at-target pruning

For one edge-addition-stable target, this module first recodes the generic
under-graph coordinate conditional independence result into the exact target
context, action, and utility-term observables.  It then selects continuations
from constant-action hybrid laws.  Site-local execution surgery makes those
continuations valid uniformly for every target rule while all other rules of
the owner remain fixed at an arbitrary reduced owner policy.

The construction is division-free, including at zero-mass contexts and
actions.  It makes no claim about nonrelevant terms, total utility, reduction,
coverage, or equilibrium.
-/

import GameTheory.Experimental.PostArchitecture.FiniteConditionalContinuation
import GameTheory.Experimental.PostArchitecture.MAIDPruningConditionalIndependence
import GameTheory.Experimental.PostArchitecture.MAIDSiteReplacementContext
import GameTheory.Experimental.PostArchitecture.MAIDTargetSurgery
import GameTheory.Experimental.PostArchitecture.MAIDUtilityContinuationFromCI

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDPruningRelevantContinuation

open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.FrontierEquivalence
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence
open GameTheory.Experimental.PostArchitecture.FiniteConditionalContinuation
open GameTheory.Experimental.PostArchitecture.FiniteConditionalIndependence
open GameTheory.Experimental.PostArchitecture.MAIDPruningConditionalIndependence
open GameTheory.Experimental.PostArchitecture.MAIDPruningFactorizationBridge
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
open GameTheory.Experimental.PostArchitecture.MAIDPruningHybridFactorization
open GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDFactorization
open GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
open GameTheory.Experimental.PostArchitecture.MAIDSiteReplacementContext
open GameTheory.Experimental.PostArchitecture.MAIDTargetSurgery
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityContinuationFromCI
open GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization
open GameTheory.Experimental.PostArchitecture.MAIDUtilityGraphFinite
open GameTheory.Experimental.PostArchitecture.MAIDUtilitySeparationBridge

universe uΩ uX uY uZ uX' uY' uZ'
universe uPlayer uNode uValue

private theorem conditionallyIndependent_map_equiv
    {Ω : Type uΩ} {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
    {law : GameTheory.Math.Probability.FinDist Ω}
    {first : Ω → X} {second : Ω → Y} {evidence : Ω → Z}
    (hindependent : IsConditionallyIndependent law first second evidence)
    (firstEquiv : X ≃ X') (secondEquiv : Y ≃ Y')
    (evidenceEquiv : Z ≃ Z') :
    IsConditionallyIndependent law
      (firstEquiv ∘ first) (secondEquiv ∘ second)
      (evidenceEquiv ∘ evidence) := by
  intro firstValue secondValue evidenceValue
  have htriple :
      tripleAtom (firstEquiv ∘ first) (secondEquiv ∘ second)
          (evidenceEquiv ∘ evidence) firstValue secondValue evidenceValue =
        tripleAtom first second evidence (firstEquiv.symm firstValue)
          (secondEquiv.symm secondValue)
          (evidenceEquiv.symm evidenceValue) := by
    ext omega
    simp only [tripleAtom, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · rintro ⟨hfirst, hsecond, hevidence⟩
      exact ⟨by simpa using congrArg firstEquiv.symm hfirst,
        by simpa using congrArg secondEquiv.symm hsecond,
        by simpa using congrArg evidenceEquiv.symm hevidence⟩
    · rintro ⟨hfirst, hsecond, hevidence⟩
      exact ⟨by simpa using congrArg firstEquiv hfirst,
        by simpa using congrArg secondEquiv hsecond,
        by simpa using congrArg evidenceEquiv hevidence⟩
  have hatom :
      atom (evidenceEquiv ∘ evidence) evidenceValue =
        atom evidence (evidenceEquiv.symm evidenceValue) := by
    ext omega
    simp only [atom, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · exact fun heq => by simpa using congrArg evidenceEquiv.symm heq
    · exact fun heq => by simpa using congrArg evidenceEquiv heq
  have hfirstPair :
      pairAtom (firstEquiv ∘ first) (evidenceEquiv ∘ evidence)
          firstValue evidenceValue =
        pairAtom first evidence (firstEquiv.symm firstValue)
          (evidenceEquiv.symm evidenceValue) := by
    ext omega
    simp only [pairAtom, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · rintro ⟨hfirst, hevidence⟩
      exact ⟨by simpa using congrArg firstEquiv.symm hfirst,
        by simpa using congrArg evidenceEquiv.symm hevidence⟩
    · rintro ⟨hfirst, hevidence⟩
      exact ⟨by simpa using congrArg firstEquiv hfirst,
        by simpa using congrArg evidenceEquiv hevidence⟩
  have hsecondPair :
      pairAtom (secondEquiv ∘ second) (evidenceEquiv ∘ evidence)
          secondValue evidenceValue =
        pairAtom second evidence (secondEquiv.symm secondValue)
          (evidenceEquiv.symm evidenceValue) := by
    ext omega
    simp only [pairAtom, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · rintro ⟨hsecond, hevidence⟩
      exact ⟨by simpa using congrArg secondEquiv.symm hsecond,
        by simpa using congrArg evidenceEquiv.symm hevidence⟩
    · rintro ⟨hsecond, hevidence⟩
      exact ⟨by simpa using congrArg secondEquiv hsecond,
        by simpa using congrArg evidenceEquiv hevidence⟩
  rw [htriple, hatom, hfirstPair, hsecondPair]
  exact hindependent (firstEquiv.symm firstValue)
    (secondEquiv.symm secondValue) (evidenceEquiv.symm evidenceValue)

private theorem conditionallyIndependent_adjoin_evidence
    {Ω : Type uΩ} {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {law : GameTheory.Math.Probability.FinDist Ω}
    {first : Ω → X} {second : Ω → Y} {evidence : Ω → Z}
    (hindependent : IsConditionallyIndependent law first second evidence) :
    IsConditionallyIndependent law
      (fun omega => (first omega, evidence omega)) second evidence := by
  rintro ⟨firstValue, carriedEvidence⟩ secondValue evidenceValue
  classical
  by_cases hevidence : carriedEvidence = evidenceValue
  · subst carriedEvidence
    have htriple :
        tripleAtom (fun omega => (first omega, evidence omega)) second evidence
            (firstValue, evidenceValue) secondValue evidenceValue =
          tripleAtom first second evidence firstValue secondValue
            evidenceValue := by
      ext omega
      simp only [tripleAtom, Set.mem_setOf_eq, Prod.mk.injEq]
      tauto
    have hpair :
        pairAtom (fun omega => (first omega, evidence omega)) evidence
            (firstValue, evidenceValue) evidenceValue =
          pairAtom first evidence firstValue evidenceValue := by
      ext omega
      simp only [pairAtom, Set.mem_setOf_eq, Prod.mk.injEq]
      tauto
    rw [htriple, hpair]
    exact hindependent firstValue secondValue evidenceValue
  · have htriple :
        tripleAtom (fun omega => (first omega, evidence omega)) second evidence
            (firstValue, carriedEvidence) secondValue evidenceValue = ∅ := by
      ext omega
      simp only [tripleAtom, Set.mem_setOf_eq, Prod.mk.injEq,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hcarried⟩, _, hactual⟩
      exact hevidence (hcarried.symm.trans hactual)
    have hpair :
        pairAtom (fun omega => (first omega, evidence omega)) evidence
            (firstValue, carriedEvidence) evidenceValue = ∅ := by
      ext omega
      simp only [pairAtom, Set.mem_setOf_eq, Prod.mk.injEq,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hcarried⟩, hactual⟩
      exact hevidence (hcarried.symm.trans hactual)
    have hempty : law.probOf (∅ : Set Ω) = 0 := by
      rw [← GameTheory.Math.Probability.FinDist.expect_indicator_eq_probOf]
      simp
    rw [htriple, hpair, hempty]
    simp

variable {Player : Type uPlayer} {Node : Type uNode}
variable
  {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
  {semantics : Semantics diagram}

private def removedConfigurationEquivUnder
    [DecidableEq Node] (view : UtilityView semantics) (owner : Player)
    (decisionParents : DecisionParentMap Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := owner) view decisionParents))
    (removed : Finset Node) :
    Config (utilityGraphStructureUnder view owner decisionParents topological)
        (removedGraphNodes view owner removed) ≃
      Config diagram removed where
  toFun configuration node :=
    configuration ⟨.base node.1, by
      simp [removedGraphNodes, node.2]⟩
  invFun configuration graphNode := by
    rcases graphNode with ⟨graphNode, hgraphNode⟩
    cases graphNode with
    | base node =>
        exact configuration ⟨node, by
          simpa [removedGraphNodes] using hgraphNode⟩
    | utility term =>
        simp [removedGraphNodes] at hgraphNode
  left_inv configuration := by
    funext graphNode
    rcases graphNode with ⟨graphNode, hgraphNode⟩
    cases graphNode with
    | base node => rfl
    | utility term =>
        simp [removedGraphNodes] at hgraphNode
  right_inv configuration := by
    funext node
    rfl

private def utilityConfigurationEquivUnder
    [DecidableEq Node] (view : UtilityView semantics) (owner : Player)
    (decisionParents : DecisionParentMap Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := owner) view decisionParents))
    (term : view.UtilitySite owner) :
    Config (utilityGraphStructureUnder view owner decisionParents topological)
        {.utility term} ≃
      MAIDUtilityContinuationFromCI.TermConfig view term where
  toFun configuration :=
    configuration ⟨.utility term, Finset.mem_singleton_self _⟩
  invFun configuration graphNode := by
    rcases graphNode with ⟨graphNode, hgraphNode⟩
    have heq : graphNode = .utility term := by simpa using hgraphNode
    subst graphNode
    exact configuration
  left_inv configuration := by
    funext graphNode
    rcases graphNode with ⟨graphNode, hgraphNode⟩
    have heq : graphNode = .utility term := by simpa using hgraphNode
    subst graphNode
    rfl
  right_inv _ := rfl

private theorem site_not_observed [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner) :
    site.1 ∉ diagram.observedParents site.1 := by
  intro hsite
  apply diagram.acyclic site.1
  exact Relation.TransGen.single (diagram.observed_sub site.1 hsite)

private def hybridConditioningConfigurationEquiv
    [DecidableEq Node] (view : UtilityView semantics) (owner : Player)
    (pruning : Pruning diagram) (target : DecisionSite diagram owner)
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    Config (utilityGraphStructureUnder view owner
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        (hybridAugmentedTopologicalOrder topological view owner pruning target))
        (MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
          (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target) target
          (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)) ≃
      KeptAction target
        (MAIDPruningFixpointGraph.Pruning.missingAt pruning target) where
  toFun configuration :=
    (fun node => configuration ⟨.base node.1, by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨node.1, ?_, rfl⟩
      simp [MAIDPruningFixpointGraph.Pruning.restoreAllAt, node.2]⟩,
    configuration ⟨.base target.1, by
      simp [MAIDPruningFixpointGraph.UtilityView.conditioningUnder]⟩)
  invFun keptAction graphNode := by
    rcases graphNode with ⟨graphNode, hgraphNode⟩
    cases graphNode with
    | utility term =>
        simp [MAIDPruningFixpointGraph.UtilityView.conditioningUnder]
          at hgraphNode
    | base node =>
        by_cases htarget : node = target.1
        · subst node
          exact keptAction.2
        · have hkept : node ∈
              KeptNodes target
                (MAIDPruningFixpointGraph.Pruning.missingAt pruning target) := by
            simpa [MAIDPruningFixpointGraph.UtilityView.conditioningUnder,
              MAIDPruningFixpointGraph.Pruning.restoreAllAt, htarget]
              using hgraphNode
          exact keptAction.1 ⟨node, hkept⟩
  left_inv configuration := by
    funext graphNode
    rcases graphNode with ⟨graphNode, hgraphNode⟩
    cases graphNode with
    | utility term =>
        simp [MAIDPruningFixpointGraph.UtilityView.conditioningUnder]
          at hgraphNode
    | base node =>
        by_cases htarget : node = target.1
        · subst node
          simp
        · simp [htarget]
  right_inv keptAction := by
    apply Prod.ext
    · funext node
      have hne : node.1 ≠ target.1 := by
        intro heq
        have hobserved := (Finset.mem_sdiff.mp node.2).1
        apply site_not_observed target
        simpa only [heq] using hobserved
      simp [hne]
    · simp

private def fullActionSplitEquiv
    [DecidableEq Node] {owner : Player}
    (target : DecisionSite diagram owner) (removed : Finset Node)
    (hremoved : removed ⊆ diagram.observedParents target.1) :
    FullAction target ≃ Config diagram removed × KeptAction target removed where
  toFun full :=
    (Config.restrict hremoved full.1, keepFullAction target removed full)
  invFun parts :=
    ((fun node => if hnode : node.1 ∈ removed
      then parts.1 ⟨node.1, hnode⟩
      else parts.2.1 ⟨node.1,
        Finset.mem_sdiff.mpr ⟨node.2, hnode⟩⟩),
      parts.2.2)
  left_inv full := by
    apply Prod.ext
    · funext node
      by_cases hnode : node.1 ∈ removed <;>
        simp [hnode, Config.restrict, keepFullAction]
    · rfl
  right_inv parts := by
    apply Prod.ext
    · funext node
      simp [Config.restrict, node.2]
    · apply Prod.ext
      · funext node
        have hnot : node.1 ∉ removed := (Finset.mem_sdiff.mp node.2).2
        simp [keepFullAction, Config.restrict, hnot]
      · rfl

private theorem fullActionSplitEquiv_symm_parts
    [DecidableEq Node] {owner : Player}
    (target : DecisionSite diagram owner) (removed : Finset Node)
    (hremoved : removed ⊆ diagram.observedParents target.1)
    (full : FullAction target) :
    (fullActionSplitEquiv target removed hremoved).symm
        (Config.restrict hremoved full.1,
          keepFullAction target removed full) = full :=
  (fullActionSplitEquiv target removed hremoved).symm_apply_apply full

private theorem removedConfigurationEquivUnder_restrict
    [DecidableEq Node] (view : UtilityView semantics) (owner : Player)
    (pruning : Pruning diagram) (target : DecisionSite diagram owner)
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (assignment : AugmentedAssignment view owner) :
    removedConfigurationEquivUnder view owner
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        (hybridAugmentedTopologicalOrder topological view owner pruning target)
        (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)
        (Assignment.restrict
          (utilityGraphStructureUnder view owner
            (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
            (hybridAugmentedTopologicalOrder topological view owner pruning
              target))
          assignment
          (removedGraphNodes view owner
            (MAIDPruningFixpointGraph.Pruning.missingAt pruning target))) =
      Config.restrict (Finset.sdiff_subset)
        (fullAction view target assignment).1 := by
  funext node
  rfl

private theorem utilityConfigurationEquivUnder_restrict
    [DecidableEq Node] (view : UtilityView semantics) (owner : Player)
    (pruning : Pruning diagram) (target : DecisionSite diagram owner)
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (term : view.UtilitySite owner)
    (assignment : AugmentedAssignment view owner) :
    utilityConfigurationEquivUnder view owner
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        (hybridAugmentedTopologicalOrder topological view owner pruning target)
        term
        (Assignment.restrict
          (utilityGraphStructureUnder view owner
            (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
            (hybridAugmentedTopologicalOrder topological view owner pruning
              target)) assignment {.utility term}) =
      termConfig view term assignment := by
  rfl

private theorem hybridConditioningConfigurationEquiv_restrict
    [DecidableEq Node] (view : UtilityView semantics) (owner : Player)
    (pruning : Pruning diagram) (target : DecisionSite diagram owner)
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (assignment : AugmentedAssignment view owner) :
    hybridConditioningConfigurationEquiv view owner pruning target topological
        (Assignment.restrict
          (utilityGraphStructureUnder view owner
            (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
            (hybridAugmentedTopologicalOrder topological view owner pruning
              target))
          assignment
          (MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
            (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
            target
            (MAIDPruningFixpointGraph.Pruning.missingAt pruning target))) =
      keepFullAction target
        (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)
        (fullAction view target assignment) := by
  apply Prod.ext <;> rfl

/-- Fixed-rule hybrid graphical ignorability recodes to the exact observable
conditional independence used by finite conditional continuation. -/
theorem hybrid_fullAction_conditionallyIndependent
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : FullContext target →
      GameTheory.Math.Probability.FinDist (diagram.Value target.1))
    (hstable :
      MAIDPruningFixpointGraph.UtilityView.IsEdgeAdditionStableAt view
        pruning target)
    (term : view.UtilitySite owner)
    (hrelevant :
      MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        target term) :
    IsConditionallyIndependent
      (augmentedLaw view owner
        (hybridPolicy pruning policy owner fixedOwner target rule))
      (fullAction view target) (termConfig view term)
      (keepFullAction target
        (MAIDPruningFixpointGraph.Pruning.missingAt pruning target) ∘
          fullAction view target) := by
  let underTopological :=
    hybridAugmentedTopologicalOrder topological view owner pruning target
  have hcoordinates :=
    hybrid_removed_conditionallyIndependent_of_edgeAdditionStableAt
      topological view pruning policy owner fixedOwner target rule hstable term
      hrelevant
  have hrecoded := conditionallyIndependent_map_equiv hcoordinates
    (removedConfigurationEquivUnder view owner
      (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
      underTopological
      (MAIDPruningFixpointGraph.Pruning.missingAt pruning target))
    (utilityConfigurationEquivUnder view owner
      (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
      underTopological term)
    (hybridConditioningConfigurationEquiv view owner pruning target
      topological)
  have hremovedEq :
      (removedConfigurationEquivUnder view owner
          (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
          underTopological
          (MAIDPruningFixpointGraph.Pruning.missingAt pruning target) :
          _ → Config diagram
            (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)) ∘
          (fun assignment => Assignment.restrict
            (utilityGraphStructureUnder view owner
              (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
              underTopological)
            assignment (removedGraphNodes view owner
              (MAIDPruningFixpointGraph.Pruning.missingAt pruning target))) =
        fun assignment => Config.restrict Finset.sdiff_subset
          (fullAction view target assignment).1 := by
    funext assignment
    exact removedConfigurationEquivUnder_restrict view owner pruning target
      topological assignment
  have htermEq :
      (utilityConfigurationEquivUnder view owner
          (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
          underTopological term : _ →
            MAIDUtilityContinuationFromCI.TermConfig view term) ∘
          (fun assignment => Assignment.restrict
            (utilityGraphStructureUnder view owner
              (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
              underTopological) assignment {.utility term}) =
        termConfig view term := by
    funext assignment
    exact utilityConfigurationEquivUnder_restrict view owner pruning target
      topological term assignment
  have hconditioningEq :
      (hybridConditioningConfigurationEquiv view owner pruning target
          topological : _ → KeptAction target
            (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)) ∘
          (fun assignment => Assignment.restrict
            (utilityGraphStructureUnder view owner
              (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
              underTopological) assignment
            (MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
              (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
              target
              (MAIDPruningFixpointGraph.Pruning.missingAt pruning target))) =
        keepFullAction target
          (MAIDPruningFixpointGraph.Pruning.missingAt pruning target) ∘
            fullAction view target := by
    funext assignment
    exact hybridConditioningConfigurationEquiv_restrict view owner pruning
      target topological assignment
  rw [hremovedEq, htermEq, hconditioningEq] at hrecoded
  have hparts :
      IsConditionallyIndependent
        (augmentedLaw view owner
          (hybridPolicy pruning policy owner fixedOwner target rule))
        (fun assignment => Config.restrict Finset.sdiff_subset
          (fullAction view target assignment).1)
        (termConfig view term)
        (keepFullAction target
          (MAIDPruningFixpointGraph.Pruning.missingAt pruning target) ∘
            fullAction view target) :=
    hrecoded
  have hadjoined := conditionallyIndependent_adjoin_evidence hparts
  have hremovedObserved :
      MAIDPruningFixpointGraph.Pruning.missingAt pruning target ⊆
        diagram.observedParents target.1 :=
    Finset.sdiff_subset
  have hfull := conditionallyIndependent_map_equiv hadjoined
    (fullActionSplitEquiv target
      (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)
      hremovedObserved).symm
    (Equiv.refl (MAIDUtilityContinuationFromCI.TermConfig view term))
    (Equiv.refl (KeptAction target
      (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)))
  convert hfull using 1
  · funext assignment
    exact (fullActionSplitEquiv_symm_parts target
      (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)
      hremovedObserved (fullAction view target assignment)).symm
  · rfl
  · rfl

/-- Fixed-rule hybrid CI yields the exact joint-law bind through the canonical
finite conditional continuation. -/
theorem hybrid_fixedRule_jointLaw_eq_bind_continuation
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : FullContext target →
      GameTheory.Math.Probability.FinDist (diagram.Value target.1))
    (hstable :
      MAIDPruningFixpointGraph.UtilityView.IsEdgeAdditionStableAt view
        pruning target)
    (term : view.UtilitySite owner)
    (hrelevant :
      MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        target term) :
    (augmentedLaw view owner
        (hybridPolicy pruning policy owner fixedOwner target rule)).map
        (fun assignment =>
          (fullAction view target assignment, termConfig view term assignment)) =
      ((augmentedLaw view owner
        (hybridPolicy pruning policy owner fixedOwner target rule)).map
        (fullAction view target)).bind fun full =>
          (continuation
            (augmentedLaw view owner
              (hybridPolicy pruning policy owner fixedOwner target rule))
            (fullAction view target) (termConfig view term)
            (keepFullAction target
              (MAIDPruningFixpointGraph.Pruning.missingAt pruning target))
            (keepFullAction target
              (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)
              full)).map fun termValue => (full, termValue) := by
  exact contextTermLaw_eq_bind_continuation
    (augmentedLaw view owner
      (hybridPolicy pruning policy owner fixedOwner target rule))
    (fullAction view target) (termConfig view term)
    (keepFullAction target
      (MAIDPruningFixpointGraph.Pruning.missingAt pruning target))
    (hybrid_fullAction_conditionallyIndependent topological view pruning policy
      owner fixedOwner target rule hstable term hrelevant)

/-- A deterministic target rule used only to select the continuation at one
action. -/
def constantSiteRule {owner : Player}
    (target : DecisionSite diagram owner) (action : diagram.Value target.1) :
    FullContext target → FinDist (diagram.Value target.1) :=
  fun _ => FinDist.pure action

/-- Read the target full action and one exact term configuration from a base
assignment, with the same association as the augmented-law observable. -/
def siteFullActionTermProjection (view : UtilityView semantics)
    {owner : Player} (target : DecisionSite diagram owner)
    (term : view.UtilitySite owner) (assignment : Assignment diagram) :
    FullAction target × MAIDUtilityContinuationFromCI.TermConfig view term :=
  ((Assignment.restrict diagram assignment
      (diagram.observedParents target.1), assignment target.1),
    Assignment.restrict diagram assignment (view.term term).parents)

private theorem prob_bind_eq_chosen_mul
    {Action Output : Type*} (law : FinDist Action)
    (next : Action → FinDist Output) (chosen : Action) (output : Output)
    (hoffTarget : ∀ action ∈ law.support, action ≠ chosen →
      (next action).prob output = 0) :
    (law.bind next).prob output =
      law.prob chosen * (next chosen).prob output := by
  classical
  rw [FinDist.prob_bind, FinDist.expect_eq_sum_support]
  by_cases hchosen : chosen ∈ law.support
  · rw [Finset.sum_eq_single chosen]
    · intro action haction hne
      rw [hoffTarget action (FinDist.mem_supportFinset.mp haction) hne,
        mul_zero]
    · intro hnot
      exact absurd (FinDist.mem_supportFinset.mpr hchosen) hnot
  · rw [FinDist.prob_eq_zero_iff.mpr hchosen, zero_mul]
    apply Finset.sum_eq_zero
    intro action haction
    have hsupport := FinDist.mem_supportFinset.mp haction
    have hne : action ≠ chosen := by
      intro heq
      subst action
      exact hchosen hsupport
    rw [hoffTarget action hsupport hne, mul_zero]

private theorem suffix_prob_eq_zero_of_action_ne
    [DecidableEq Node] (semantics : Semantics diagram)
    (base : Policy diagram) {owner : Player}
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    (term : view.UtilitySite owner) (after : List Node)
    (htargetAfter : target.1 ∉ after) (state : Assignment diagram)
    (chosen queried : diagram.Value target.1)
    (context : FullContext target)
    (termValue : MAIDUtilityContinuationFromCI.TermConfig view term)
    (hne : chosen ≠ queried) :
    ((assignmentRun semantics base after
        (ToEFG.Stage.Assignment.setOne state ⟨target.1, chosen⟩)).map
      (siteFullActionTermProjection view target term)).prob
        ((context, queried), termValue) = 0 := by
  apply FinDist.prob_eq_zero_iff.mpr
  intro houtput
  rw [FinDist.support_map] at houtput
  obtain ⟨result, hresult, hprojection⟩ := houtput
  have hpreserved := assignmentRun_support_preserves_of_not_mem
    semantics base after
    (ToEFG.Stage.Assignment.setOne state ⟨target.1, chosen⟩)
    result target.1 htargetAfter hresult
  have hchosen : result target.1 = chosen := by
    simpa [ToEFG.Stage.Assignment.setOne, Assignment.resolve] using hpreserved
  have hqueried : result target.1 = queried :=
    congrArg (fun output => output.1.2) hprojection
  exact hne (hchosen.symm.trans hqueried)

private theorem suffix_prob_eq_zero_of_context_ne
    [DecidableEq Node] (semantics : Semantics diagram)
    (base : Policy diagram) {owner : Player}
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    (term : view.UtilitySite owner) (after : List Node)
    (hobservedAfter : ∀ node ∈ diagram.observedParents target.1,
      node ∉ after)
    (state : Assignment diagram)
    (chosen queried : diagram.Value target.1)
    (context : FullContext target)
    (termValue : MAIDUtilityContinuationFromCI.TermConfig view term)
    (hne : Assignment.restrict diagram state
      (diagram.observedParents target.1) ≠ context) :
    ((assignmentRun semantics base after
        (ToEFG.Stage.Assignment.setOne state ⟨target.1, chosen⟩)).map
      (siteFullActionTermProjection view target term)).prob
        ((context, queried), termValue) = 0 := by
  apply FinDist.prob_eq_zero_iff.mpr
  intro houtput
  rw [FinDist.support_map] at houtput
  obtain ⟨result, hresult, hprojection⟩ := houtput
  have hsuffix :
      Assignment.restrict diagram result
          (diagram.observedParents target.1) =
        Assignment.restrict diagram
          (ToEFG.Stage.Assignment.setOne state ⟨target.1, chosen⟩)
          (diagram.observedParents target.1) := by
    funext node
    exact assignmentRun_support_preserves_of_not_mem semantics base after
      (ToEFG.Stage.Assignment.setOne state ⟨target.1, chosen⟩)
      result node.1 (hobservedAfter node.1 node.2) hresult
  have htargetNotObserved :
      target.1 ∉ diagram.observedParents target.1 :=
    site_not_observed target
  have hset := restrict_setOne_of_not_mem state
    (diagram.observedParents target.1) chosen htargetNotObserved
  have hresultContext :
      Assignment.restrict diagram state
          (diagram.observedParents target.1) =
        Assignment.restrict diagram result
          (diagram.observedParents target.1) :=
    hset.symm.trans hsuffix.symm
  have hprojected :
      Assignment.restrict diagram result
          (diagram.observedParents target.1) = context :=
    congrArg (fun output => output.1.1) hprojection
  exact hne (hresultContext.trans hprojected)

/-- At an exact full-action/term point, an arbitrary target rule contributes
only its probability of the queried action.  The remaining factor is the
canonical law under the corresponding constant target rule. -/
theorem siteReplacementLaw_prob_eq_rule_mul_constant
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    (term : view.UtilitySite owner)
    (rule : FullContext target → FinDist (diagram.Value target.1))
    (context : FullContext target) (action : diagram.Value target.1)
    (termValue : MAIDUtilityContinuationFromCI.TermConfig view term) :
    ((siteReplacementLaw semantics base owner replacement target rule).map
      (siteFullActionTermProjection view target term)).prob
        ((context, action), termValue) =
      (rule context).prob action *
        ((siteReplacementLaw semantics base owner replacement target
          (constantSiteRule target action)).map
          (siteFullActionTermProjection view target term)).prob
            ((context, action), termValue) := by
  obtain ⟨before, after, horder⟩ :=
    List.mem_iff_append.mp (topological.complete target.1)
  have hnodup : (before ++ target.1 :: after).Nodup := by
    rw [← horder]
    exact topological.nodup
  have htargetBefore : target.1 ∉ before := by
    intro htarget
    exact (List.nodup_append.mp hnodup).2.2 target.1 htarget
      target.1 (by simp) rfl
  have htargetAfter : target.1 ∉ after :=
    (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).1
  have hordered :
      (before ++ target.1 :: after).Pairwise
        (fun earlier later => later ∉ diagram.parents earlier) := by
    rw [← horder]
    exact topological_pairwise topological
  have htargetOrder : ∀ node ∈ after,
      node ∉ diagram.parents target.1 :=
    (List.pairwise_cons.mp
      (List.pairwise_append.mp hordered).2.1).1
  have hobservedAfter : ∀ node ∈ diagram.observedParents target.1,
      node ∉ after := by
    intro node hobserved hafter
    exact htargetOrder node hafter
      (diagram.observed_sub target.1 hobserved)
  let fixedPolicy :=
    Profile.update (sig := nativeBehavioralSignature diagram)
      base owner replacement
  have hrule :
      (siteReplacementLaw semantics base owner replacement target rule).map
          (siteFullActionTermProjection view target term) =
        (assignmentRun semantics fixedPolicy before
          semantics.defaultValue).bind fun state =>
            (rule (Assignment.restrict diagram state
              (diagram.observedParents target.1))).bind fun chosen =>
              (assignmentRun semantics fixedPolicy after
                (ToEFG.Stage.Assignment.setOne state
                  ⟨target.1, chosen⟩)).map
                (siteFullActionTermProjection view target term) := by
    unfold siteReplacementLaw
    rw [nativeBehavioralGameForm_play,
      map_values_nativeRun_eq_assignmentRun topological semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner (replaceSiteRule replacement target rule)), horder]
    rw [assignmentRun_site_surgery_eq semantics base owner replacement target
      rule before after htargetBefore htargetAfter semantics.defaultValue]
    simp only [FinDist.map_bind, fixedPolicy]
  have hconstant :
      (siteReplacementLaw semantics base owner replacement target
          (constantSiteRule target action)).map
          (siteFullActionTermProjection view target term) =
        (assignmentRun semantics fixedPolicy before
          semantics.defaultValue).bind fun state =>
            (assignmentRun semantics fixedPolicy after
              (ToEFG.Stage.Assignment.setOne state
                ⟨target.1, action⟩)).map
              (siteFullActionTermProjection view target term) := by
    unfold siteReplacementLaw
    rw [nativeBehavioralGameForm_play,
      map_values_nativeRun_eq_assignmentRun topological semantics
        (Profile.update (sig := nativeBehavioralSignature diagram) base owner
          (replaceSiteRule replacement target
            (constantSiteRule target action))), horder]
    rw [assignmentRun_site_surgery_eq semantics base owner replacement target
      (constantSiteRule target action) before after htargetBefore htargetAfter
      semantics.defaultValue]
    simp only [FinDist.map_bind, constantSiteRule, FinDist.pure_bind,
      fixedPolicy]
  rw [hrule, hconstant]
  rw [FinDist.prob_bind]
  rw [FinDist.prob_bind
    (assignmentRun semantics fixedPolicy before semantics.defaultValue)]
  rw [← FinDist.expect_smul]
  apply FinDist.expect_congr
  intro state _
  by_cases hcontext : Assignment.restrict diagram state
      (diagram.observedParents target.1) = context
  · have hfactor := prob_bind_eq_chosen_mul
      (rule (Assignment.restrict diagram state
        (diagram.observedParents target.1)))
      (fun chosen =>
        (assignmentRun semantics fixedPolicy after
          (ToEFG.Stage.Assignment.setOne state ⟨target.1, chosen⟩)).map
            (siteFullActionTermProjection view target term))
      action ((context, action), termValue) (by
        intro chosen _ hne
        exact suffix_prob_eq_zero_of_action_ne semantics fixedPolicy target
          view term after htargetAfter state chosen action context termValue
            hne)
    simpa only [hcontext] using hfactor
  · have hconstantZero := suffix_prob_eq_zero_of_context_ne semantics
      fixedPolicy target view term after hobservedAfter state action action
      context termValue hcontext
    have harbitraryZero :
        ((rule (Assignment.restrict diagram state
          (diagram.observedParents target.1))).bind fun chosen =>
            (assignmentRun semantics fixedPolicy after
              (ToEFG.Stage.Assignment.setOne state
                ⟨target.1, chosen⟩)).map
              (siteFullActionTermProjection view target term)).prob
            ((context, action), termValue) = 0 := by
      rw [FinDist.prob_bind]
      have hbranches :
          (fun chosen =>
            ((assignmentRun semantics fixedPolicy after
              (ToEFG.Stage.Assignment.setOne state
                ⟨target.1, chosen⟩)).map
              (siteFullActionTermProjection view target term)).prob
                ((context, action), termValue)) = fun _ => 0 := by
        funext chosen
        exact suffix_prob_eq_zero_of_context_ne semantics fixedPolicy target
          view term after hobservedAfter state chosen action context termValue
            hcontext
      rw [hbranches, FinDist.expect_const]
    rw [harbitraryZero, hconstantZero, mul_zero]

private theorem augmented_joint_eq_site_joint
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    (rule : FullContext target → FinDist (diagram.Value target.1)) :
    (augmentedLaw view owner
        (hybridPolicy pruning policy owner fixedOwner target rule)).map
        (fun assignment =>
          (fullAction view target assignment, termConfig view term assignment)) =
      (siteReplacementLaw semantics (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target rule).map
        (siteFullActionTermProjection view target term) := by
  rw [hybridPolicy_eq_update_replaceSiteRule]
  unfold augmentedLaw siteReplacementLaw
  rw [FinDist.map_comp]
  rfl

private theorem augmented_fullAction_eq_site_contextAction
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : FullContext target → FinDist (diagram.Value target.1)) :
    (augmentedLaw view owner
        (hybridPolicy pruning policy owner fixedOwner target rule)).map
        (fullAction view target) =
      (siteReplacementLaw semantics (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target rule).map
        (fun assignment =>
          (Assignment.restrict diagram assignment
            (diagram.observedParents target.1), assignment target.1)) := by
  rw [hybridPolicy_eq_update_replaceSiteRule]
  unfold augmentedLaw siteReplacementLaw
  rw [FinDist.map_comp]
  rfl

private theorem bind_tagged_prob
    {First Second : Type*} (outer : FinDist First)
    (kernel : First → FinDist Second) (first : First) (second : Second) :
    (outer.bind fun candidate =>
      (kernel candidate).map fun value => (candidate, value)).prob
        (first, second) =
      outer.prob first * (kernel first).prob second := by
  exact FinDist.prob_bind_map_prod outer kernel first second

private theorem nested_bind_tagged_prob
    {Full Action Term Kept : Type*} (outer : FinDist Full)
    (rule : Full → FinDist Action) (keep : Full → Kept)
    (kernel : Kept → Action → FinDist Term)
    (full : Full) (action : Action) (term : Term) :
    (outer.bind fun candidate =>
      (rule candidate).bind fun chosen =>
        (kernel (keep candidate) chosen).map fun termValue =>
          ((candidate, chosen), termValue)).prob ((full, action), term) =
      outer.prob full * (rule full).prob action *
        (kernel (keep full) action).prob term := by
  classical
  have hrepacked :
      outer.bind (fun candidate =>
          (rule candidate).bind fun chosen =>
            (kernel (keep candidate) chosen).map fun termValue =>
              ((candidate, chosen), termValue)) =
        outer.bind fun candidate =>
          ((rule candidate).bind fun chosen =>
            (kernel (keep candidate) chosen).map fun termValue =>
              (chosen, termValue)).map fun pair =>
                ((candidate, pair.1), pair.2) := by
    apply FinDist.bind_congr
    intro candidate _
    rw [FinDist.map_bind]
    apply FinDist.bind_congr
    intro chosen _
    rw [FinDist.map_comp]
    rfl
  rw [hrepacked, FinDist.prob_bind]
  calc
    outer.expect (fun candidate =>
        (((rule candidate).bind fun chosen =>
          (kernel (keep candidate) chosen).map fun termValue =>
            (chosen, termValue)).map fun pair =>
              ((candidate, pair.1), pair.2)).prob ((full, action), term)) =
      outer.expect (fun candidate =>
        if full = candidate then
          ((rule full).bind fun chosen =>
            (kernel (keep full) chosen).map fun termValue =>
              (chosen, termValue)).prob (action, term)
        else 0) := by
      apply FinDist.expect_congr
      intro candidate _
      by_cases heq : full = candidate
      · subst candidate
        rw [if_pos rfl]
        exact FinDist.prob_map_of_injective
          (fun pair => ((full, pair.1), pair.2)) (by
            intro first second hequal
            apply Prod.ext
            · exact congrArg (fun output => output.1.2) hequal
            · exact congrArg (fun output => output.2) hequal)
          ((rule full).bind fun chosen =>
            (kernel (keep full) chosen).map fun termValue =>
              (chosen, termValue)) (action, term)
      · rw [if_neg heq, FinDist.prob_eq_zero_iff]
        intro hsupport
        rw [FinDist.support_map] at hsupport
        obtain ⟨pair, _, hpair⟩ := hsupport
        exact heq (congrArg (fun output => output.1.1) hpair).symm
    _ = outer.prob full *
        ((rule full).bind fun chosen =>
          (kernel (keep full) chosen).map fun termValue =>
            (chosen, termValue)).prob (action, term) := by
      rw [FinDist.expect_ite_eq]
    _ = outer.prob full * (rule full).prob action *
        (kernel (keep full) action).prob term := by
      rw [bind_tagged_prob]
      ring

/-- Recode a pruning-kept context and target action into the fixed-rule
conditional-continuation key. -/
def hybridKeptAction [DecidableEq Node]
    (pruning : Pruning diagram) {owner : Player}
    (target : DecisionSite diagram owner) (kept : KeptContext pruning target)
    (action : diagram.Value target.1) :
    KeptAction target
      (MAIDPruningFixpointGraph.Pruning.missingAt pruning target) :=
  ((fun node => kept ⟨node.1, by
      have hobserved := (Finset.mem_sdiff.mp node.2).1
      have hnotRemoved := (Finset.mem_sdiff.mp node.2).2
      by_contra hnotKept
      apply hnotRemoved
      unfold MAIDPruningFixpointGraph.Pruning.missingAt
      exact Finset.mem_sdiff.mpr ⟨hobserved, hnotKept⟩⟩),
    action)

private theorem hybridKeptAction_restrict
    [DecidableEq Node] (pruning : Pruning diagram) {owner : Player}
    (target : DecisionSite diagram owner) (full : FullContext target)
    (action : diagram.Value target.1) :
    hybridKeptAction pruning target
        (Config.restrict (pruning.kept_sub_observed target.1) full) action =
      keepFullAction target
        (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)
        (full, action) := by
  apply Prod.ext
  · funext node
    rfl
  · rfl

/-- A relevant term's continuation selected from the hybrid law under the
constant target action. -/
def hybridConstantActionContinuation
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    (kept : KeptContext pruning target) (action : diagram.Value target.1) :
    FinDist (MAIDReplacementInvariantUtility.TermConfig view term) :=
  continuation
    (augmentedLaw view owner
      (hybridPolicy pruning policy owner fixedOwner target
        (constantSiteRule target action)))
    (fullAction view target) (termConfig view term)
    (keepFullAction target
      (MAIDPruningFixpointGraph.Pruning.missingAt pruning target))
    (hybridKeptAction pruning target kept action)

/-- Site-local analogue of `TermContinuationLawAt`: only the target rule
varies, while all other rules of a possibly multi-site owner remain fixed. -/
structure SiteTermContinuationLawAt
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    (context : SiteReplacementContextLawAt semantics
      (pruning.expandPolicy policy) owner
      (pruning.expandOwnerPolicy owner fixedOwner) target)
    (term : view.UtilitySite owner) where
  continuationLaw : KeptContext pruning target →
    diagram.Value target.1 →
      FinDist (MAIDReplacementInvariantUtility.TermConfig view term)
  joint_eq : ∀ rule : FullContext target →
      FinDist (diagram.Value target.1),
    (siteReplacementLaw semantics (pruning.expandPolicy policy) owner
      (pruning.expandOwnerPolicy owner fixedOwner) target rule).map
        (siteFullActionTermProjection view target term) =
      context.contextLaw.bind fun full =>
        (rule full).bind fun action =>
          (continuationLaw
            (Config.restrict (pruning.kept_sub_observed target.1) full)
            action).map fun termValue => ((full, action), termValue)

/-- Edge-addition stability constructs one relevant-term continuation that is
uniform over every target rule and does not require a unique owner site. -/
def relevantTermContinuationLawAt_of_edgeAdditionStableAt
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    (hstable :
      MAIDPruningFixpointGraph.UtilityView.IsEdgeAdditionStableAt view
        pruning target)
    (term : view.UtilitySite owner)
    (hrelevant :
      MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        target term) :
    SiteTermContinuationLawAt pruning semantics policy owner fixedOwner target
      view
      (siteReplacementContextLawAt topological semantics
        (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target)
      term := by
  let context := siteReplacementContextLawAt topological semantics
    (pruning.expandPolicy policy) owner
    (pruning.expandOwnerPolicy owner fixedOwner) target
  refine {
    continuationLaw := hybridConstantActionContinuation view pruning policy
      owner fixedOwner target term
    joint_eq := ?_ }
  intro rule
  apply FinDist.ext_of_prob
  rintro ⟨⟨full, action⟩, termValue⟩
  let constantRule := constantSiteRule target action
  have hfixed := hybrid_fixedRule_jointLaw_eq_bind_continuation topological
    view pruning policy owner fixedOwner target constantRule hstable term
      hrelevant
  have hfixedPoint := congrArg
    (fun law => law.prob ((full, action), termValue)) hfixed
  rw [bind_tagged_prob] at hfixedPoint
  have hfixedSite :
      ((siteReplacementLaw semantics (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target constantRule).map
        (siteFullActionTermProjection view target term)).prob
          ((full, action), termValue) =
        ((siteReplacementLaw semantics (pruning.expandPolicy policy) owner
          (pruning.expandOwnerPolicy owner fixedOwner) target constantRule).map
          (fun assignment =>
            (Assignment.restrict diagram assignment
              (diagram.observedParents target.1), assignment target.1))).prob
            (full, action) *
          (continuation
            (augmentedLaw view owner
              (hybridPolicy pruning policy owner fixedOwner target
                constantRule))
            (fullAction view target) (termConfig view term)
            (keepFullAction target
              (MAIDPruningFixpointGraph.Pruning.missingAt pruning target))
            (keepFullAction target
              (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)
              (full, action))).prob termValue := by
    rw [← augmented_joint_eq_site_joint view pruning policy owner fixedOwner
      target term constantRule]
    rw [← augmented_fullAction_eq_site_contextAction view pruning policy owner
      fixedOwner target constantRule]
    exact hfixedPoint
  have hcontextPoint := congrArg (fun law => law.prob (full, action))
    (context.contextAction_eq constantRule)
  rw [bind_tagged_prob] at hcontextPoint
  have hconstantContext :
      ((siteReplacementLaw semantics (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target constantRule).map
        (fun assignment =>
          (Assignment.restrict diagram assignment
            (diagram.observedParents target.1), assignment target.1))).prob
          (full, action) = context.contextLaw.prob full := by
    simpa [constantRule, constantSiteRule] using hcontextPoint
  have hcontinuation :
      hybridConstantActionContinuation view pruning policy owner fixedOwner
          target term
          (Config.restrict (pruning.kept_sub_observed target.1) full) action =
        continuation
          (augmentedLaw view owner
            (hybridPolicy pruning policy owner fixedOwner target constantRule))
          (fullAction view target) (termConfig view term)
          (keepFullAction target
            (MAIDPruningFixpointGraph.Pruning.missingAt pruning target))
          (keepFullAction target
            (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)
            (full, action)) := by
    unfold hybridConstantActionContinuation
    rw [hybridKeptAction_restrict]
  have hright := nested_bind_tagged_prob context.contextLaw rule
    (fun full =>
      Config.restrict (pruning.kept_sub_observed target.1) full)
    (hybridConstantActionContinuation view pruning policy owner fixedOwner
      target term) full action termValue
  show
    ((siteReplacementLaw semantics (pruning.expandPolicy policy) owner
      (pruning.expandOwnerPolicy owner fixedOwner) target rule).map
      (siteFullActionTermProjection view target term)).prob
        ((full, action), termValue) = _
  rw [siteReplacementLaw_prob_eq_rule_mul_constant topological semantics
    (pruning.expandPolicy policy) owner
    (pruning.expandOwnerPolicy owner fixedOwner) target view term rule full
      action termValue]
  rw [hfixedSite, hconstantContext, ← hcontinuation]
  rw [hright]
  ring

end GameTheory.Experimental.PostArchitecture.MAIDPruningRelevantContinuation
