/-
# EXP-107: nonrelevant utility invariance under restore-at-target pruning

Changing one target rule changes only the target base-node kernel in the exact
restore-at-target augmented graph.  If a utility term is not a directed
descendant of that target in the same graph, its ancestral coordinates exclude
the changed kernel.  Parent-closed finite-BN kernel invariance therefore makes
the term's exact parent-configuration marginal independent of the target rule.

The result supports owners with multiple fixed reduced sites and makes no
conditional-independence, utility-factorization, coverage, or equilibrium
claim.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNKernelInvariance
import GameTheory.Experimental.PostArchitecture.MAIDPruningConditionalIndependence
import GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
import GameTheory.Experimental.PostArchitecture.MAIDSiteReplacementContext

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDPruningNonrelevantInvariance

open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNKernelInvariance
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralComponents
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation
open GameTheory.Experimental.PostArchitecture.MAIDPruningConditionalIndependence
open GameTheory.Experimental.PostArchitecture.MAIDPruningFactorizationBridge
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
open GameTheory.Experimental.PostArchitecture.MAIDPruningHybridFactorization
open GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDSiteReplacementContext
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable
  {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
  {semantics : Semantics diagram}

/-- The parent-closed ancestral coordinates of one utility leaf in the exact
restore-at-target graph. -/
def hybridUtilityAncestors [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (pruning : Pruning diagram) (target : DecisionSite diagram owner)
    (term : view.UtilitySite owner) : Finset (view.GraphNode owner) :=
  ancestralFactors
    (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
      (owner := owner) view
      (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target))
    {.utility term} ∅ ∅

/-- The dependent configuration on a hybrid utility leaf's ancestors. -/
def HybridUtilityAncestorConfig [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (pruning : Pruning diagram) (target : DecisionSite diagram owner)
    (term : view.UtilitySite owner) :=
  (node : {node // node ∈
    hybridUtilityAncestors view pruning target term}) → graphValue view node.1

private def hybridUtilityAncestorRestriction
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (pruning : Pruning diagram) (target : DecisionSite diagram owner)
    (term : view.UtilitySite owner)
    (assignment : AugmentedAssignment view owner) :
    HybridUtilityAncestorConfig view pruning target term :=
  fun node => assignment node.1

private theorem target_not_mem_hybridUtilityAncestors
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (pruning : Pruning diagram) (target : DecisionSite diagram owner)
    (term : view.UtilitySite owner)
    (hnonrelevant :
      ¬ MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        target term) :
    (.base target.1 : view.GraphNode owner) ∉
      hybridUtilityAncestors view pruning target term := by
  intro hmem
  rw [hybridUtilityAncestors, mem_ancestralFactors_iff] at hmem
  obtain ⟨root, hroot, path⟩ := hmem
  have hrootEq : root = .utility term := by
    simpa [queryRoots] using hroot
  subst root
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with hequal | path
  · cases hequal
  · exact hnonrelevant path

private theorem hybridAugmentedKernels_eq_of_ne_target
    [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (first second : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1))
    (node : view.GraphNode owner)
    (hne : node ≠ (.base target.1 : view.GraphNode owner)) :
    hybridAugmentedKernels view pruning policy owner fixedOwner target first
        node =
      hybridAugmentedKernels view pruning policy owner fixedOwner target second
        node := by
  cases node with
  | utility _ => rfl
  | base baseNode =>
      have hbase : baseNode ≠ target.1 := by
        intro hequal
        subst baseNode
        exact hne rfl
      funext configuration
      simp only [hybridAugmentedKernels]
      rw [hybridEffectiveKernels_of_ne semantics pruning policy owner
        fixedOwner target first baseNode hbase]
      rw [hybridEffectiveKernels_of_ne semantics pruning policy owner
        fixedOwner target second baseNode hbase]

private theorem hybridAugmentedKernels_eqOn_utilityAncestors
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    (hnonrelevant :
      ¬ MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        target term)
    (first second : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    ∀ node ∈ hybridUtilityAncestors view pruning target term,
      hybridAugmentedKernels view pruning policy owner fixedOwner target first
          node =
        hybridAugmentedKernels view pruning policy owner fixedOwner target
          second node := by
  intro node hnode
  apply hybridAugmentedKernels_eq_of_ne_target view pruning policy owner
    fixedOwner target first second node
  intro hequal
  subst node
  exact target_not_mem_hybridUtilityAncestors view pruning target term
    hnonrelevant hnode

private def hybridAugmentedUtilityAncestorLaw
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :=
  (augmentedLaw view owner
    (hybridPolicy pruning policy owner fixedOwner target rule)).map
    (hybridUtilityAncestorRestriction view pruning target term)

private theorem hybridAugmentedUtilityAncestorsLaw_eq
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    (hnonrelevant :
      ¬ MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        target term)
    (first second : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    hybridAugmentedUtilityAncestorLaw view pruning policy owner fixedOwner
        target term first =
      hybridAugmentedUtilityAncestorLaw view pruning policy owner fixedOwner
        target term second := by
  let parents := MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
    (owner := owner) view
    (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
  let underTopological :=
    hybridAugmentedTopologicalOrder topological view owner pruning target
  unfold hybridAugmentedUtilityAncestorLaw
    hybridUtilityAncestorRestriction
  apply restrictLaw_eq_of_factorizes_of_kernels_eqOn
    (diagram := utilityGraphStructureUnder view owner
      (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
      underTopological)
    (parents := parents) (topological := underTopological)
    (firstKernels := hybridAugmentedKernels view pruning policy owner
      fixedOwner target first)
    (secondKernels := hybridAugmentedKernels view pruning policy owner
      fixedOwner target second)
    (hfirst := augmentedLaw_factorizes_hybrid topological view owner pruning
      policy owner fixedOwner target first)
    (hsecond := augmentedLaw_factorizes_hybrid topological view owner pruning
      policy owner fixedOwner target second)
    (retained := hybridUtilityAncestors view pruning target term)
  · intro child hchild parent hparent
    rw [hybridUtilityAncestors, mem_ancestralFactors_iff] at hchild ⊢
    exact parent_mem_ancestralClosure hchild hparent
  · exact hybridAugmentedKernels_eqOn_utilityAncestors view pruning policy
      owner fixedOwner target term hnonrelevant first second

private theorem baseParent_mem_hybridUtilityAncestors
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (pruning : Pruning diagram) (target : DecisionSite diagram owner)
    (term : view.UtilitySite owner)
    (parent : {node // node ∈ (view.term term).parents}) :
    (.base parent.1 : view.GraphNode owner) ∈
      hybridUtilityAncestors view pruning target term := by
  rw [hybridUtilityAncestors, mem_ancestralFactors_iff]
  refine ⟨.utility term, by simp [queryRoots], ?_⟩
  apply Relation.ReflTransGen.single
  unfold MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
  exact Finset.mem_image.mpr ⟨parent.1, parent.2, rfl⟩

private def hybridTermParentProjection
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) {owner : Player}
    (pruning : Pruning diagram) (target : DecisionSite diagram owner)
    (term : view.UtilitySite owner)
    (configuration : HybridUtilityAncestorConfig view pruning target term) :
    MAIDReplacementInvariantUtility.TermConfig view term :=
  fun parent => configuration
    ⟨.base parent.1,
      baseParent_mem_hybridUtilityAncestors view pruning target term parent⟩

private def hybridAugmentedTermMarginalLaw
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :=
  (hybridAugmentedUtilityAncestorLaw view pruning policy owner fixedOwner
    target term rule).map
      (hybridTermParentProjection view pruning target term)

private theorem hybridAugmentedTermMarginalLaw_eq
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    (hnonrelevant :
      ¬ MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        target term)
    (first second : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    hybridAugmentedTermMarginalLaw view pruning policy owner fixedOwner target
        term first =
      hybridAugmentedTermMarginalLaw view pruning policy owner fixedOwner
        target term second := by
  have hrestricted := hybridAugmentedUtilityAncestorsLaw_eq topological view
    pruning policy owner fixedOwner target term hnonrelevant first second
  exact congrArg
    (FinDist.map (hybridTermParentProjection view pruning target term))
    hrestricted

private theorem hybridAugmentedTermMarginalLaw_eq_siteTermMarginal
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    hybridAugmentedTermMarginalLaw view pruning policy owner fixedOwner target
        term rule =
      (siteReplacementLaw semantics (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target rule).map
        (fun assignment => Assignment.restrict diagram assignment
          (view.term term).parents) := by
  unfold hybridAugmentedTermMarginalLaw
    hybridAugmentedUtilityAncestorLaw
  rw [hybridPolicy_eq_update_replaceSiteRule]
  unfold augmentedLaw siteReplacementLaw
  let nativeLaw := (Strategic.nativeBehavioralGameForm semantics).play
    (Profile.update (sig := Strategic.nativeBehavioralSignature diagram)
      (pruning.expandPolicy policy) owner
      (MAIDSitePolicySurgery.replaceSiteRule
        (pruning.expandOwnerPolicy owner fixedOwner) target rule))
  let graphRestriction := hybridUtilityAncestorRestriction view pruning target
    term
  let projection := hybridTermParentProjection view pruning target term
  let baseRestriction := fun assignment : Assignment diagram =>
    Assignment.restrict diagram assignment (view.term term).parents
  show ((nativeLaw.map (augmentAssignment view)).map graphRestriction).map
      projection = nativeLaw.map baseRestriction
  rw [FinDist.map_comp projection graphRestriction
    (nativeLaw.map (augmentAssignment view))]
  rw [FinDist.map_comp (projection ∘ graphRestriction)
    (augmentAssignment view) nativeLaw]
  apply congrArg (fun observable => nativeLaw.map observable)
  funext assignment parent
  rfl

/-- Any two target rules induce the same exact typed parent-configuration
marginal for a term that is nonrelevant in the restore-at-target graph. -/
theorem nonrelevantTerm_marginal_eq
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    (hnonrelevant :
      ¬ MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        target term)
    (first second : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    (siteReplacementLaw semantics (pruning.expandPolicy policy) owner
      (pruning.expandOwnerPolicy owner fixedOwner) target first).map
        (fun assignment => Assignment.restrict diagram assignment
          (view.term term).parents) =
      (siteReplacementLaw semantics (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target second).map
          (fun assignment => Assignment.restrict diagram assignment
            (view.term term).parents) := by
  rw [← hybridAugmentedTermMarginalLaw_eq_siteTermMarginal view pruning policy owner
    fixedOwner target term first]
  rw [← hybridAugmentedTermMarginalLaw_eq_siteTermMarginal view pruning policy owner
    fixedOwner target term second]
  exact hybridAugmentedTermMarginalLaw_eq topological view pruning policy owner
    fixedOwner target term hnonrelevant first second

/-- A site-local nonrelevant-term certificate, uniform over every target rule
while all other owner sites remain fixed. -/
structure SiteInvariantTermMarginalAt
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    (term : view.UtilitySite owner) where
  marginalLaw : FinDist (MAIDReplacementInvariantUtility.TermConfig view term)
  marginal_eq : ∀ rule : Config diagram
      (diagram.observedParents target.1) → FinDist (diagram.Value target.1),
    (siteReplacementLaw semantics (pruning.expandPolicy policy) owner
      (pruning.expandOwnerPolicy owner fixedOwner) target rule).map
        (fun assignment => Assignment.restrict diagram assignment
          (view.term term).parents) = marginalLaw

/-- A nonrelevant hybrid term has one canonical site-rule-invariant marginal.
The fixed owner's current target rule supplies the reference law, requiring no
extra inhabitance choice. -/
def nonrelevantTermMarginalCertificate
    (pruning : Pruning diagram)
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    (term : view.UtilitySite owner)
    (hnonrelevant :
      ¬ MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
        target term) :
    SiteInvariantTermMarginalAt pruning semantics policy owner fixedOwner
      target view term where
  marginalLaw :=
    (siteReplacementLaw semantics (pruning.expandPolicy policy) owner
      (pruning.expandOwnerPolicy owner fixedOwner) target
      (pruning.expandOwnerPolicy owner fixedOwner target)).map
      (fun assignment => Assignment.restrict diagram assignment
        (view.term term).parents)
  marginal_eq rule :=
    nonrelevantTerm_marginal_eq topological view pruning policy owner
      fixedOwner target term hnonrelevant rule
        (pruning.expandOwnerPolicy owner fixedOwner target)

end GameTheory.Experimental.PostArchitecture.MAIDPruningNonrelevantInvariance
