/-
# EXP-107: conditional independence under explicit pruning parent maps

This module connects graphical ignorability under an explicit decision-parent
map to finite conditional independence for any law factorizing over the same
exact utility graph.  A final corollary instantiates the generic statement with
the canonical restore-at-target hybrid law.

No comparison between target mechanisms, observation-reduction theorem, or
equilibrium claim is made here.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness
import GameTheory.Experimental.PostArchitecture.MAIDPruningHybridFactorization
import GameTheory.Experimental.PostArchitecture.MAIDUtilitySeparationBridge

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDPruningConditionalIndependence

open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation
open GameTheory.Experimental.PostArchitecture.MAIDPruningFactorizationBridge
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
open GameTheory.Experimental.PostArchitecture.MAIDPruningHybridFactorization
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization
open GameTheory.Experimental.PostArchitecture.MAIDUtilityGraphFinite
open GameTheory.Experimental.PostArchitecture.MAIDUtilitySeparationBridge

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable
  {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
  {semantics : Semantics diagram}

/-- Proof-only all-chance presentation of one exact utility graph under an
explicit map of decision parents. -/
@[reducible]
def utilityGraphStructureUnder [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (decisionParents : DecisionParentMap Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := owner) view decisionParents)) :
    Structure.{0, uNode, max uNode uValue} Unit (view.GraphNode owner) where
  kind _ := .chance
  parents := MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
    (owner := owner) view decisionParents
  observedParents := MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
    (owner := owner) view decisionParents
  Value := graphValue view
  observed_sub _ := Finset.Subset.rfl
  observed_eq_of_chance _ _ := rfl
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder topological

private theorem removedBase_ancestor_decisionUnder
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (decisionParents : DecisionParentMap Node)
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (hsubset : removed ⊆ decisionParents site.1)
    (observation : Node) (hremoved : observation ∈ removed) :
    AncestorOrSelf
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := owner) view decisionParents)
      (.base observation : view.GraphNode owner) (.base site.1) := by
  apply Relation.ReflTransGen.single
  simp [DirectedEdge,
    MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
    effectiveParentsUnder, site.2, hsubset hremoved]

private theorem inAncestralClosure_under_iff_singleton
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (decisionParents : DecisionParentMap Node)
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (hsubset : removed ⊆ decisionParents site.1)
    (observation : Node) (hremoved : observation ∈ removed)
    (term : view.UtilitySite owner)
    (evidence : Finset (view.GraphNode owner))
    (hdecision : (.base site.1 : view.GraphNode owner) ∈ evidence)
    (node : view.GraphNode owner) :
    InAncestralClosure
        (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
          (owner := owner) view decisionParents)
        (removedGraphNodes view owner removed) {.utility term} evidence node ↔
      InAncestralClosure
        (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
          (owner := owner) view decisionParents)
        {.base observation} {.utility term} evidence node := by
  constructor
  · rintro ⟨root, hroot, path⟩
    have hcases : root = .utility term ∨
        root ∈ removedGraphNodes view owner removed ∨ root ∈ evidence := by
      simpa [queryRoots] using hroot
    rcases hcases with htarget | hremovedRoot | hevidence
    · exact ⟨root, by simp [queryRoots, htarget], path⟩
    · obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp hremovedRoot
      refine ⟨.base site.1, ?_, path.trans ?_⟩
      · simp [queryRoots, hdecision]
      · exact removedBase_ancestor_decisionUnder view decisionParents site
          removed hsubset other hother
    · exact ⟨root, by simp [queryRoots, hevidence], path⟩
  · rintro ⟨root, hroot, path⟩
    refine ⟨root, ?_, path⟩
    have hcases : root = .base observation ∨
        root = .utility term ∨ root ∈ evidence := by
      simpa [queryRoots] using hroot
    rcases hcases with hsource | htarget | hevidence
    · subst root
      simp [queryRoots, removedGraphNodes, hremoved]
    · simp [queryRoots, htarget]
    · simp [queryRoots, hevidence]

private theorem moralAdjacent_removed_under_relation_eq
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (decisionParents : DecisionParentMap Node)
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (hsubset : removed ⊆ decisionParents site.1)
    (observation : Node) (hremoved : observation ∈ removed)
    (term : view.UtilitySite owner)
    (evidence : Finset (view.GraphNode owner))
    (hdecision : (.base site.1 : view.GraphNode owner) ∈ evidence) :
    MoralAdjacent
        (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
          (owner := owner) view decisionParents)
        (removedGraphNodes view owner removed) {.utility term} evidence =
      MoralAdjacent
        (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
          (owner := owner) view decisionParents)
        {.base observation} {.utility term} evidence := by
  funext left right
  apply propext
  simp only [MoralAdjacent,
    inAncestralClosure_under_iff_singleton view decisionParents site removed
      hsubset observation hremoved term evidence hdecision]

/-- Set-valued ignorability under an explicit decision-parent map is exact
ancestral-moral separation for all removed base nodes and one relevant utility
leaf. -/
theorem separates_removedGraphNodes_of_areGraphicallyIgnorableUnder
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (decisionParents : DecisionParentMap Node)
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (hignore :
      MAIDPruningFixpointGraph.UtilityView.AreGraphicallyIgnorableUnder view
        decisionParents site removed)
    (term : view.UtilitySite owner)
    (hrelevant :
      MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
        decisionParents site term) :
    Separates
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := owner) view decisionParents)
      (removedGraphNodes view owner removed) {.utility term}
      (MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
        decisionParents site removed) := by
  intro source hsource target htarget
  obtain ⟨observation, hremoved, rfl⟩ := Finset.mem_image.mp hsource
  have htargetEq : target = .utility term := by simpa using htarget
  subst target
  rintro ⟨hsourceOpen, htargetOpen, path⟩
  have hdecision :
      (.base site.1 : view.GraphNode owner) ∈
        MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
          decisionParents site removed := by
    simp [MAIDPruningFixpointGraph.UtilityView.conditioningUnder]
  rw [moralAdjacent_removed_under_relation_eq view decisionParents site
    removed hignore.1 observation hremoved term _ hdecision] at path
  exact hignore.2 term hrelevant observation hremoved
    ⟨hsourceOpen, htargetOpen, path⟩

private theorem removedGraphNodes_conditioningUnder_disjoint
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (decisionParents : DecisionParentMap Node)
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (hsubset : removed ⊆ decisionParents site.1)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := owner) view decisionParents)) :
    Disjoint (removedGraphNodes view owner removed)
      (MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
        decisionParents site removed) := by
  rw [Finset.disjoint_left]
  intro graphNode hremovedNode hconditioned
  obtain ⟨observation, hremoved, rfl⟩ :=
    Finset.mem_image.mp hremovedNode
  have hparent :
      (.base observation : view.GraphNode owner) ∈
        MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
          (owner := owner) view decisionParents (.base site.1) := by
    simp [MAIDPruningFixpointGraph.UtilityView.graphParentsUnder,
      effectiveParentsUnder, site.2,
      hsubset hremoved]
  have hne : observation ≠ site.1 := by
    intro hequal
    subst observation
    exact (GameTheory.Math.DAG.acyclic_of_topologicalOrder topological
      (.base site.1)) (Relation.TransGen.single hparent)
  unfold MAIDPruningFixpointGraph.UtilityView.conditioningUnder at hconditioned
  rcases Finset.mem_insert.mp hconditioned with hequal | hcurrent
  · exact hne (UtilityView.GraphNode.base.inj hequal)
  · obtain ⟨parent, hparentCurrent, hparentEq⟩ :=
      Finset.mem_image.mp hcurrent
    have hparentValue : parent = observation :=
      UtilityView.GraphNode.base.inj hparentEq
    subst parent
    exact (Finset.mem_sdiff.mp hparentCurrent).2 hremoved

private theorem utility_conditioningUnder_disjoint
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (decisionParents : DecisionParentMap Node)
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (term : view.UtilitySite owner) :
    Disjoint ({.utility term} : Finset (view.GraphNode owner))
      (MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
        decisionParents site removed) := by
  simp [MAIDPruningFixpointGraph.UtilityView.conditioningUnder]

/-- The under-graph query has the three disjoint coordinate sets required by
finite global Markov soundness. -/
theorem under_query_disjointness
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (decisionParents : DecisionParentMap Node)
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (term : view.UtilitySite owner)
    (hsubset : removed ⊆ decisionParents site.1)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := owner) view decisionParents)) :
    Disjoint (removedGraphNodes view owner removed)
        ({.utility term} : Finset (view.GraphNode owner)) ∧
      Disjoint (removedGraphNodes view owner removed)
        (MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
          decisionParents site removed) ∧
      Disjoint ({.utility term} : Finset (view.GraphNode owner))
        (MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
          decisionParents site removed) :=
  ⟨removedGraphNodes_utility_disjoint view removed term,
    removedGraphNodes_conditioningUnder_disjoint view decisionParents site
      removed hsubset topological,
    utility_conditioningUnder_disjoint view decisionParents site removed term⟩

/-- Any finite law factorizing over the selected under-graph satisfies the
coordinate conditional independence certified by graphical ignorability in
that same graph. -/
theorem removed_conditionallyIndependent_of_factorizes_of_ignorableUnder
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (view : UtilityView semantics) (owner : Player)
    (decisionParents : DecisionParentMap Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := owner) view decisionParents))
    (law : GameTheory.Math.Probability.FinDist
      (AugmentedAssignment view owner))
    (kernels : LocalKernels (graphValue view)
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := owner) view decisionParents))
    (hfactor : Factorizes (graphValue view) law
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := owner) view decisionParents) kernels)
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (hignore :
      MAIDPruningFixpointGraph.UtilityView.AreGraphicallyIgnorableUnder view
        decisionParents site removed)
    (term : view.UtilitySite owner)
    (hrelevant :
      MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
        decisionParents site term) :
    CoordinatesConditionallyIndependent
      (diagram := utilityGraphStructureUnder view owner decisionParents
        topological)
      law (removedGraphNodes view owner removed) {.utility term}
      (MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
        decisionParents site removed) := by
  obtain ⟨hfirstSecond, hfirstEvidence, hsecondEvidence⟩ :=
    under_query_disjointness view decisionParents site removed term hignore.1
      topological
  exact coordinatesConditionallyIndependent_of_factorizes_of_separates
    (diagram := utilityGraphStructureUnder view owner decisionParents
      topological)
    law (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
      (owner := owner) view decisionParents) topological kernels hfactor
    (removedGraphNodes view owner removed) {.utility term}
    (MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
      decisionParents site removed)
    hfirstSecond hfirstEvidence hsecondEvidence
    (separates_removedGraphNodes_of_areGraphicallyIgnorableUnder view
      decisionParents site removed hignore term hrelevant)

/-- The canonical restore-at-target hybrid law is the first consumer of the
generic under-graph theorem.  This remains a fixed-rule statement. -/
theorem hybrid_removed_conditionallyIndependent_of_edgeAdditionStableAt
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      GameTheory.Math.Probability.FinDist (diagram.Value target.1))
    (hstable :
      MAIDPruningFixpointGraph.UtilityView.IsEdgeAdditionStableAt view
        pruning target)
    (term : view.UtilitySite owner)
    (hrelevant :
      MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        target term) :
    CoordinatesConditionallyIndependent
      (diagram := utilityGraphStructureUnder view owner
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        (hybridAugmentedTopologicalOrder topological view owner pruning target))
      (augmentedLaw view owner
        (hybridPolicy pruning policy owner fixedOwner target rule))
      (removedGraphNodes view owner
        (MAIDPruningFixpointGraph.Pruning.missingAt pruning target))
      {.utility term}
      (MAIDPruningFixpointGraph.UtilityView.conditioningUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target) target
        (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)) := by
  exact removed_conditionallyIndependent_of_factorizes_of_ignorableUnder view
    owner (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
    (hybridAugmentedTopologicalOrder topological view owner pruning target)
    (augmentedLaw view owner
      (hybridPolicy pruning policy owner fixedOwner target rule))
    (hybridAugmentedKernels view pruning policy owner fixedOwner target rule)
    (augmentedLaw_factorizes_hybrid topological view owner pruning policy owner
      fixedOwner target rule)
    target (MAIDPruningFixpointGraph.Pruning.missingAt pruning target)
    hstable term hrelevant

end GameTheory.Experimental.PostArchitecture.MAIDPruningConditionalIndependence
