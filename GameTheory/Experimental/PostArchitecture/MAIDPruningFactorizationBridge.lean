/-
# EXP-107: pruning-parent factorization bridge

Candidate and restore-at-site decision-parent maps only delete original
observations.  Hence the original causal order remains valid for their
effective base graphs and, after appending the exact utility leaves, for their
augmented graphs.  This file contains no optimality or coverage claim.
-/

import GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
import GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDPruningFactorizationBridge

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.MAIDFactorization
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization
open GameTheory.Experimental.PostArchitecture.MAIDUtilityGraphFinite



universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}
variable {semantics : Semantics diagram}

/-- A candidate pruning retains only original observations. -/
theorem candidateDecisionParents_subset_observed
    (pruning : Pruning diagram) (node : Node) :
    MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning node ⊆
      diagram.observedParents node :=
  pruning.kept_sub_observed node

/-- Restoring all observations at one site and retaining candidate parents
elsewhere still never introduces a non-original observation. -/
theorem restoreAllAt_subset_observed [DecidableEq Node]
    (pruning : Pruning diagram) {owner : Player}
    (site : DecisionSite diagram owner) (node : Node) :
    MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning site node ⊆
      diagram.observedParents node := by
  intro parent hparent
  unfold MAIDPruningFixpointGraph.Pruning.restoreAllAt at hparent
  split at hparent
  · exact hparent
  · exact pruning.kept_sub_observed node hparent

/-- A topological list for a parent map is also topological for every pointwise
sub-parent map. -/
def topologicalOrderOfSubset
    {parents subparents : Node → Finset Node}
    (topological : GameTheory.Math.DAG.TopologicalOrder parents)
    (hsubset : ∀ node, subparents node ⊆ parents node) :
    GameTheory.Math.DAG.TopologicalOrder subparents where
  order := topological.order
  nodup := topological.nodup
  complete := topological.complete
  respects index parent hparent :=
    topological.respects index parent
      (hsubset topological.order[index] hparent)

/-- Effective candidate parents are a subgraph of the original causal DAG. -/
theorem effectiveParentsUnder_subset_effective
    (decisionParents : MAIDPruningFixpointGraph.DecisionParentMap Node)
    (hsubset : ∀ node,
      decisionParents node ⊆ diagram.observedParents node)
    (node : Node) :
    MAIDPruningFixpointGraph.effectiveParentsUnder diagram decisionParents node ⊆
      effectiveParents diagram node := by
  unfold MAIDPruningFixpointGraph.effectiveParentsUnder
  split <;> rename_i hkind
  · simp [effectiveParents, hkind]
  · simpa [effectiveParents, hkind] using hsubset node

/-- Effective candidate parents are in particular a subgraph of the original
causal DAG. -/
theorem effectiveParentsUnder_subset_parents
    (decisionParents : MAIDPruningFixpointGraph.DecisionParentMap Node)
    (hsubset : ∀ node,
      decisionParents node ⊆ diagram.observedParents node)
    (node : Node) :
    MAIDPruningFixpointGraph.effectiveParentsUnder diagram decisionParents node ⊆
      diagram.parents node := by
  unfold MAIDPruningFixpointGraph.effectiveParentsUnder
  split
  · exact fun _ => id
  · exact (hsubset node).trans (diagram.observed_sub node)

/-- The original causal order remains valid under any sub-observation
decision-parent map. -/
def effectiveTopologicalOrderUnder
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : MAIDPruningFixpointGraph.DecisionParentMap Node)
    (hsubset : ∀ node,
      decisionParents node ⊆ diagram.observedParents node) :
    GameTheory.Math.DAG.TopologicalOrder
      (MAIDPruningFixpointGraph.effectiveParentsUnder diagram decisionParents) :=
  topologicalOrderOfSubset topological
    (effectiveParentsUnder_subset_parents decisionParents hsubset)

/-- Candidate effective parents inherit the original causal order. -/
def candidateEffectiveTopologicalOrder
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (pruning : Pruning diagram) :
    GameTheory.Math.DAG.TopologicalOrder
      (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
        (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning)) :=
  effectiveTopologicalOrderUnder topological _
    (candidateDecisionParents_subset_observed pruning)

/-- The restore-all-at-site hybrid also inherits the original causal order. -/
def hybridEffectiveTopologicalOrder [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (pruning : Pruning diagram) {owner : Player}
    (site : DecisionSite diagram owner) :
    GameTheory.Math.DAG.TopologicalOrder
      (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning site)) :=
  effectiveTopologicalOrderUnder topological _
    (restoreAllAt_subset_observed pruning site)

/-- The graph under a sub-observation decision-parent map is pointwise a
subgraph of the original exact utility graph. -/
theorem graphParentsUnder_subset_graphParents [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (decisionParents : MAIDPruningFixpointGraph.DecisionParentMap Node)
    (hsubset : ∀ node,
      decisionParents node ⊆ diagram.observedParents node)
    (node : view.GraphNode owner) :
    MAIDPruningFixpointGraph.UtilityView.graphParentsUnder view decisionParents node ⊆
      view.graphParents node := by
  cases node with
  | base baseNode =>
      exact Finset.image_mono UtilityView.GraphNode.base
        (effectiveParentsUnder_subset_effective decisionParents hsubset baseNode)
  | utility _ => exact fun _ => id

/-- Base nodes remain in original causal order and every exact utility leaf is
still appended last under an arbitrary sub-observation parent map. -/
def augmentedTopologicalOrderUnder [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (decisionParents : MAIDPruningFixpointGraph.DecisionParentMap Node)
    (hsubset : ∀ node,
      decisionParents node ⊆ diagram.observedParents node) :
    GameTheory.Math.DAG.TopologicalOrder
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := owner) view decisionParents) :=
  topologicalOrderOfSubset
    (MAIDUtilityGraphFinite.augmentedTopologicalOrder
      view owner topological)
    (graphParentsUnder_subset_graphParents view decisionParents hsubset)

/-- Utility-leaves-last order for a pruning candidate. -/
def candidateAugmentedTopologicalOrder [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (pruning : Pruning diagram) :
    GameTheory.Math.DAG.TopologicalOrder
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := owner) view
        (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning)) :=
  augmentedTopologicalOrderUnder topological view owner _
    (candidateDecisionParents_subset_observed pruning)

/-- Utility-leaves-last order for a restore-all-at-site hybrid. -/
def hybridAugmentedTopologicalOrder [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (graphOwner : Player)
    (pruning : Pruning diagram) {siteOwner : Player}
    (site : DecisionSite diagram siteOwner) :
    GameTheory.Math.DAG.TopologicalOrder
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := graphOwner) view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning site)) :=
  augmentedTopologicalOrderUnder topological view graphOwner _
    (restoreAllAt_subset_observed pruning site)

/-! ## Candidate-respecting canonical kernels -/

/-- A full policy respects a sub-observation parent map when its decision law
depends only on the restricted configuration.  This certificate mentions no
factor kernel or target joint law. -/
def PolicyRespects (decisionParents : MAIDPruningFixpointGraph.DecisionParentMap Node)
    (hsubset : ∀ node,
      decisionParents node ⊆ diagram.observedParents node)
    (policy : Policy diagram) : Prop :=
  ∀ owner (site : DecisionSite diagram owner)
    (first second : Config diagram (diagram.observedParents site.1)),
    Config.restrict (hsubset site.1) first =
        Config.restrict (hsubset site.1) second →
      policy owner site first = policy owner site second

/-- Expanding a reduced policy is definitionally insensitive to all omitted
observations. -/
theorem expandPolicy_respects_candidate (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) :
    PolicyRespects
      (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning)
      (candidateDecisionParents_subset_observed pruning)
      (pruning.expandPolicy policy) := by
  intro owner site first second hagree
  exact congrArg (policy owner site) hagree

/-- Canonical chance kernels and the actual reduced decision kernels, indexed
by the candidate effective-parent map. -/
def reducedEffectiveKernels (semantics : Semantics diagram)
    (pruning : Pruning diagram) (policy : pruning.ReducedPolicy) :
    LocalKernels diagram.Value
      (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
        (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning)) :=
  fun node configuration => by
    match hkind : diagram.kind node with
    | .chance =>
        exact semantics.chanceLaw node hkind
          (fun parent => configuration
            ⟨parent.1, by
              simp [MAIDPruningFixpointGraph.effectiveParentsUnder,
                hkind] at parent ⊢⟩)
    | .decision owner =>
        exact policy owner ⟨node, hkind⟩
          (fun parent => configuration
            ⟨parent.1, by
              simp [MAIDPruningFixpointGraph.effectiveParentsUnder,
                MAIDPruningFixpointGraph.Pruning.candidateDecisionParents,
                hkind] at parent ⊢⟩)

/-- Reading a candidate kernel from a full assignment gives the same node law
as canonical execution of the expanded reduced policy. -/
theorem reducedEffectiveKernels_parentConfiguration
    (semantics : Semantics diagram) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (assignment : Assignment diagram)
    (node : Node) :
    reducedEffectiveKernels semantics pruning policy node
        (parentConfiguration diagram.Value
          (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
            (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning))
          assignment node) =
      effectiveKernels semantics (pruning.expandPolicy policy) node
        (parentConfiguration diagram.Value (effectiveParents diagram)
          assignment node) := by
  unfold reducedEffectiveKernels effectiveKernels
  split <;> split
  · rename_i hfirst hsecond
    apply congrArg (semantics.chanceLaw node hfirst)
    funext parent
    rfl
  · rename_i hchance owner hdecision
    rw [hchance] at hdecision
    contradiction
  · rename_i owner hdecision hchance
    rw [hdecision] at hchance
    contradiction
  · rename_i firstOwner hfirst secondOwner hsecond
    have howner : firstOwner = secondOwner :=
      NodeKind.decision.inj (hfirst.symm.trans hsecond)
    subst secondOwner
    rfl

/-- Canonical play of an expanded reduced policy factorizes directly over the
candidate effective-parent graph. -/
theorem native_play_factorizes_candidate
    [Fintype Node] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) :
    Factorizes diagram.Value
      ((nativeBehavioralGameForm semantics).play
        (pruning.expandPolicy policy))
      (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
        (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning))
      (reducedEffectiveKernels semantics pruning policy) := by
  intro assignment
  calc
    ((nativeBehavioralGameForm semantics).play
        (pruning.expandPolicy policy)).prob assignment =
        factorProduct diagram.Value (effectiveParents diagram)
          (effectiveKernels semantics (pruning.expandPolicy policy))
          Finset.univ assignment :=
      native_play_prob_eq_factorProduct_univ topological semantics
        (pruning.expandPolicy policy) assignment
    _ = _ := by
      unfold factorProduct localFactor
      apply Finset.prod_congr rfl
      intro node _
      rw [reducedEffectiveKernels_parentConfiguration]

/-- Read a base candidate-parent configuration from the corresponding
augmented coordinates. -/
def candidateBaseParentConfiguration [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (pruning : Pruning diagram) (node : Node)
    (configuration : ParentConfiguration
      (graphValue view (owner := owner))
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder view
        (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning))
      (.base node)) :
    ParentConfiguration diagram.Value
      (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
        (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning))
      node :=
  fun parent => configuration
    ⟨.base parent.1, by
      simp [MAIDPruningFixpointGraph.UtilityView.graphParentsUnder]⟩

/-- Utility-term parent scopes remain fixed under decision pruning. -/
def candidateUtilityParentConfiguration [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (pruning : Pruning diagram) (site : view.UtilitySite owner)
    (configuration : ParentConfiguration
      (graphValue view (owner := owner))
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder view
        (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning))
      (.utility site)) :
    Config diagram (view.term site).parents :=
  fun parent => configuration
    ⟨.base parent.1, by
      simp [MAIDPruningFixpointGraph.UtilityView.graphParentsUnder]⟩

/-- Candidate augmented kernels use the actual reduced decision rules and the
same deterministic exact utility leaves. -/
def candidateAugmentedKernels [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (pruning : Pruning diagram) (policy : pruning.ReducedPolicy) :
    LocalKernels (graphValue view (owner := owner))
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder view
        (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning))
  | .base node, configuration =>
      reducedEffectiveKernels semantics pruning policy node
        (candidateBaseParentConfiguration view pruning node configuration)
  | .utility site, configuration =>
      FinDist.pure
        (candidateUtilityParentConfiguration view pruning site configuration)

/-- Candidate and original augmented local factors agree pointwise for an
expanded reduced policy. -/
theorem candidateLocalFactor_eq_original
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (pruning : Pruning diagram) (policy : pruning.ReducedPolicy)
    (assignment : AugmentedAssignment view owner)
    (node : view.GraphNode owner) :
    localFactor (graphValue view (owner := owner))
        (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder view
          (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning))
        (candidateAugmentedKernels view pruning policy) assignment node =
      localFactor (graphValue view (owner := owner)) view.graphParents
        (augmentedKernels view (pruning.expandPolicy policy))
        assignment node := by
  cases node with
  | base baseNode =>
      unfold localFactor candidateAugmentedKernels augmentedKernels
      apply congrArg
        (fun law : FinDist (diagram.Value baseNode) =>
          law.prob (assignment (.base baseNode)))
      exact reducedEffectiveKernels_parentConfiguration semantics pruning
        policy (projectBase view assignment) baseNode
  | utility _ => rfl

/-- The canonical augmented law of an expanded reduced policy factorizes over
the pruning candidate graph, with no alternate evaluator or joint law. -/
theorem augmentedLaw_factorizes_candidate
    [Fintype Node] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (pruning : Pruning diagram) (policy : pruning.ReducedPolicy) :
    Factorizes (graphValue view (owner := owner))
      (augmentedLaw view owner (pruning.expandPolicy policy))
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder view
        (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning))
      (candidateAugmentedKernels view pruning policy) := by
  intro assignment
  calc
    (augmentedLaw view owner
        (pruning.expandPolicy policy)).prob assignment =
        factorProduct (graphValue view (owner := owner))
          view.graphParents
          (augmentedKernels view (pruning.expandPolicy policy))
          Finset.univ assignment :=
      MAIDUtilityFactorization.augmentedLaw_factorizes topological
        view owner (pruning.expandPolicy policy) assignment
    _ = _ := by
      unfold factorProduct
      apply Finset.prod_congr rfl
      intro node _
      exact (candidateLocalFactor_eq_original
        view pruning policy assignment node).symm

end GameTheory.Experimental.PostArchitecture.MAIDPruningFactorizationBridge
