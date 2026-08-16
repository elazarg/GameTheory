/-
# EXP-105: nonrelevant utility-term invariance

Changing the unique target decision mechanism cannot change the marginal of a
utility term outside that decision's directed descendants.  The proof compares
the two mapped canonical augmented laws through parent-closed kernel
invariance; it does not define another evaluator.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNKernelInvariance
import GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
import GameTheory.Experimental.PostArchitecture.MAIDUtilityConditionalIndependence

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDNonrelevantUtilityInvariance

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNKernelInvariance
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralComponents
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation
open GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
open GameTheory.Experimental.PostArchitecture.MAIDFactorization
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityConditionalIndependence
open GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization
open GameTheory.Experimental.PostArchitecture.MAIDUtilityGraphFinite

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
variable {semantics : Semantics diagram}

/-- The parent-closed ancestral set needed to read one utility leaf. -/
def utilityAncestors [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (term : view.UtilitySite owner) : Finset (view.GraphNode owner) :=
  ancestralFactors view.graphParents {.utility term} ∅ ∅

/-- The transparent dependent configuration on one utility leaf's ancestral
coordinates. -/
def UtilityAncestorConfig [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (term : view.UtilitySite owner) :=
  (node : {node // node ∈ utilityAncestors view owner term}) →
    graphValue view node.1

private def utilityAncestorRestriction
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (term : view.UtilitySite owner)
    (assignment : AugmentedAssignment view owner) :
    UtilityAncestorConfig view owner term :=
  fun node => assignment node.1

private def updatedPolicy
    [DecidableEq Player] (owner : Player) (policy : Policy diagram)
    (replacement : OwnerPolicy diagram owner) : Policy diagram :=
  Profile.update (sig := nativeBehavioralSignature diagram)
    policy owner replacement

private def replacementAugmentedLaw
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player) (policy : Policy diagram)
    (replacement : OwnerPolicy diagram owner) :=
  augmentedLaw view owner (updatedPolicy owner policy replacement)

private def replacementAugmentedKernels
    [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player) (policy : Policy diagram)
    (replacement : OwnerPolicy diagram owner) :=
  augmentedKernels view (owner := owner)
    (updatedPolicy owner policy replacement)

/-- The canonical updated augmented law, restricted to one utility leaf's
ancestral coordinates. -/
private def augmentedUtilityAncestorLaw
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (term : view.UtilitySite owner) (policy : Policy diagram)
    (replacement : OwnerPolicy diagram owner) :=
  (augmentedLaw view owner
    (updatedPolicy owner policy replacement)).map
    (utilityAncestorRestriction view owner term)

/-- The canonical marginal of one utility term's typed parent
configuration. -/
def termMarginalLaw
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (term : view.UtilitySite owner) (policy : Policy diagram) :=
  ((nativeBehavioralGameForm semantics).play policy).map
    (fun assignment : Assignment diagram =>
      Assignment.restrict diagram assignment (view.term term).parents)

private theorem target_not_mem_utilityAncestors
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    (hnonrelevant : ¬ view.IsRelevantUtilityTerm target term) :
    (.base target.1 : view.GraphNode owner) ∉
      utilityAncestors view owner term := by
  intro hmem
  rw [utilityAncestors, mem_ancestralFactors_iff] at hmem
  obtain ⟨root, hroot, path⟩ := hmem
  have hrootEq : root = .utility term := by
    simpa [queryRoots] using hroot
  subst root
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with hequal | path
  · cases hequal
  · exact hnonrelevant path

private theorem effectiveKernels_update_eq_of_ne_target
    [DecidableEq Player] [DecidableEq Node]
    (owner : Player)
    (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (policy : Policy diagram) (first second : OwnerPolicy diagram owner)
    (node : Node) (hne : node ≠ target.1) :
    effectiveKernels semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          policy owner first) node =
      effectiveKernels semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          policy owner second) node := by
  funext configuration
  unfold effectiveKernels
  split
  · rfl
  · rename_i decisionOwner hkind
    by_cases howner : decisionOwner = owner
    · subst decisionOwner
      have hsite := hunique ⟨node, hkind⟩
      exact (hne (congrArg Subtype.val hsite)).elim
    · simp [Profile.update, howner]

private theorem augmentedKernels_update_eq_of_ne_target
    [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (policy : Policy diagram) (first second : OwnerPolicy diagram owner)
    (node : view.GraphNode owner)
    (hne : node ≠ (.base target.1 : view.GraphNode owner)) :
    augmentedKernels view
        (Profile.update (sig := nativeBehavioralSignature diagram)
          policy owner first) node =
      augmentedKernels view
        (Profile.update (sig := nativeBehavioralSignature diagram)
          policy owner second) node := by
  cases node with
  | utility _ => rfl
  | base baseNode =>
      funext configuration
      rw [augmentedKernels_base, augmentedKernels_base]
      rw [effectiveKernels_update_eq_of_ne_target owner target hunique
        policy first second baseNode]
      intro hequal
      subst baseNode
      exact hne rfl

private theorem augmentedKernels_update_eqOn_utilityAncestors
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (term : view.UtilitySite owner)
    (hnonrelevant : ¬ view.IsRelevantUtilityTerm target term)
    (policy : Policy diagram) (first second : OwnerPolicy diagram owner) :
    ∀ node ∈ utilityAncestors view owner term,
      augmentedKernels view
          (Profile.update (sig := nativeBehavioralSignature diagram)
            policy owner first) node =
        augmentedKernels view
          (Profile.update (sig := nativeBehavioralSignature diagram)
            policy owner second) node := by
  intro node hnode
  apply augmentedKernels_update_eq_of_ne_target view owner target hunique
    policy first second node
  intro hequal
  subst node
  exact target_not_mem_utilityAncestors view owner target term hnonrelevant
    hnode

private theorem replacementAugmentedLaw_factorizes
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player) (policy : Policy diagram)
    (replacement : OwnerPolicy diagram owner) :
    Factorizes (graphValue view)
      (replacementAugmentedLaw view owner policy replacement)
      view.graphParents
      (replacementAugmentedKernels view owner policy replacement) :=
  augmentedLaw_factorizes topological view owner
    (updatedPolicy owner policy replacement)

private theorem augmentedUtilityAncestorsLaw_eq
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (term : view.UtilitySite owner)
    (hnonrelevant : ¬ view.IsRelevantUtilityTerm target term)
    (policy : Policy diagram) (first second : OwnerPolicy diagram owner) :
    augmentedUtilityAncestorLaw view owner term policy first =
      augmentedUtilityAncestorLaw view owner term policy second := by
  unfold augmentedUtilityAncestorLaw utilityAncestorRestriction
  apply restrictLaw_eq_of_factorizes_of_kernels_eqOn
    (diagram := utilityGraphStructure topological view owner)
    (parents := view.graphParents)
    (topological := augmentedTopologicalOrder view owner topological)
    (firstKernels := replacementAugmentedKernels view owner policy first)
    (secondKernels := replacementAugmentedKernels view owner policy second)
    (hfirst := replacementAugmentedLaw_factorizes topological view owner
      policy first)
    (hsecond := replacementAugmentedLaw_factorizes topological view owner
      policy second)
    (retained := ancestralFactors view.graphParents {.utility term} ∅ ∅)
  · intro child hchild parent hparent
    rw [mem_ancestralFactors_iff] at hchild ⊢
    exact parent_mem_ancestralClosure hchild hparent
  · exact augmentedKernels_update_eqOn_utilityAncestors view owner target
      hunique term hnonrelevant policy first second

private theorem baseParent_mem_utilityAncestors
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (term : view.UtilitySite owner)
    (parent : {node // node ∈ (view.term term).parents}) :
    (.base parent.1 : view.GraphNode owner) ∈
      ancestralFactors view.graphParents {.utility term} ∅ ∅ := by
  rw [mem_ancestralFactors_iff]
  refine ⟨.utility term, by simp [queryRoots], ?_⟩
  apply Relation.ReflTransGen.single
  unfold UtilityView.graphParents
  exact Finset.mem_image.mpr ⟨parent.1, parent.2, rfl⟩

private def termParentProjection
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (term : view.UtilitySite owner)
    (configuration : UtilityAncestorConfig view owner term) :
    Config diagram (view.term term).parents :=
  fun parent => configuration
    ⟨.base parent.1, baseParent_mem_utilityAncestors view owner term parent⟩

private def augmentedTermMarginalLaw
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (term : view.UtilitySite owner) (policy : Policy diagram)
    (replacement : OwnerPolicy diagram owner) :=
  (augmentedUtilityAncestorLaw view owner term policy
    replacement).map (termParentProjection view owner term)

private theorem augmentedTermMarginalLaw_eq_termMarginalLaw
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (term : view.UtilitySite owner) (policy : Policy diagram)
    (replacement : OwnerPolicy diagram owner) :
    augmentedTermMarginalLaw view owner term policy replacement =
      termMarginalLaw view owner term
        (updatedPolicy owner policy replacement) := by
  unfold augmentedTermMarginalLaw augmentedUtilityAncestorLaw
    augmentedLaw termMarginalLaw
  let nativeLaw := (nativeBehavioralGameForm semantics).play
    (updatedPolicy owner policy replacement)
  let graphRestriction := fun assignment =>
    utilityAncestorRestriction view owner term assignment
  let projection := termParentProjection view owner term
  let baseRestriction := fun assignment : Assignment diagram =>
    Assignment.restrict diagram assignment (view.term term).parents
  show ((nativeLaw.map (augmentAssignment view)).map graphRestriction).map
      projection = nativeLaw.map baseRestriction
  rw [FinDist.map_comp projection graphRestriction
    (nativeLaw.map (augmentAssignment view))]
  rw [FinDist.map_comp (projection ∘ graphRestriction)
    (augmentAssignment view) nativeLaw]
  apply congrArg
    (fun observable => nativeLaw.map observable)
  funext assignment parent
  rfl

/-- Any two replacements at the unique target owner induce the same exact
typed parent-configuration marginal for a nonrelevant utility term. -/
theorem nonrelevantTerm_marginal_eq
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (term : view.UtilitySite owner)
    (hnonrelevant : ¬ view.IsRelevantUtilityTerm target term)
    (policy : Policy diagram) (first second : OwnerPolicy diagram owner) :
    termMarginalLaw view owner term
        (Profile.update (sig := nativeBehavioralSignature diagram)
          policy owner first) =
      termMarginalLaw view owner term
        (Profile.update (sig := nativeBehavioralSignature diagram)
          policy owner second) := by
  have hrestricted := augmentedUtilityAncestorsLaw_eq topological view owner
    target hunique term hnonrelevant policy first second
  have hmarginals := congrArg
    (FinDist.map (termParentProjection view owner term))
    hrestricted
  have hpair :
      termMarginalLaw view owner term (updatedPolicy owner policy first) =
        termMarginalLaw view owner term
          (updatedPolicy owner policy second) := by
    rw [← augmentedTermMarginalLaw_eq_termMarginalLaw view owner
      term policy first]
    rw [← augmentedTermMarginalLaw_eq_termMarginalLaw view owner
      term policy second]
    exact hmarginals
  simpa only [updatedPolicy] using hpair

/-- The expanded baseline policy supplies a canonical reference marginal, so
the graph-free nonrelevant-term certificate needs no inhabitance choice. -/
def nonrelevantTermMarginalCertificate
    (pruning : ObservationPruning.Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (view : UtilityView semantics) (term : view.UtilitySite owner)
    (hnonrelevant : ¬ view.IsRelevantUtilityTerm target term) :
    ReplacementInvariantTermMarginalAt pruning semantics policy owner view
      term where
  marginalLaw :=
    (replacementLaw pruning semantics policy owner
      ((pruning.expandPolicy policy) owner)).map fun assignment =>
        Assignment.restrict diagram assignment (view.term term).parents
  marginal_eq replacement :=
    by
      unfold replacementLaw
      simpa only [termMarginalLaw] using
        nonrelevantTerm_marginal_eq topological view owner target hunique
          term hnonrelevant (pruning.expandPolicy policy) replacement
          ((pruning.expandPolicy policy) owner)

end GameTheory.Experimental.PostArchitecture.MAIDNonrelevantUtilityInvariance
