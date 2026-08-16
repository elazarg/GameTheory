/-
# EXP-107: restore-at-site canonical factorization

Fix a reduced profile and replace exactly one target decision by an arbitrary
full-observation rule.  The resulting canonical policy respects the hybrid
parent map that restores every original observation at the target and retains
only pruning candidates elsewhere.  Its native and exact-utility augmented
laws then factorize over that hybrid graph.  No alternate evaluator, optimality,
conditional-independence, or coverage claim is introduced.
-/

import GameTheory.Experimental.PostArchitecture.MAIDPruningFactorizationBridge
import GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDPruningHybridFactorization

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.MAIDFactorization
open GameTheory.Experimental.PostArchitecture.MAIDPruningFactorizationBridge
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization
open GameTheory.Experimental.PostArchitecture.MAIDUtilityGraphFinite

universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}
variable {semantics : Semantics diagram}

/-- Replace one owner's reduced strategy while keeping every other owner fixed. -/
def fixedReducedPolicy [DecidableEq Player] (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner) : pruning.ReducedPolicy :=
  Profile.update (sig := pruning.reducedBehavioralSignature)
    policy owner fixedOwner

/-- Expand the fixed reduced profile and replace only the target site by the
arbitrary full-observation rule. -/
def hybridPolicy [DecidableEq Player] [DecidableEq Node]
    (pruning : Pruning diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) : Policy diagram :=
  Profile.update (sig := nativeBehavioralSignature diagram)
    (pruning.expandPolicy
      (fixedReducedPolicy pruning policy owner fixedOwner)) owner
    (replaceSiteRule
      (pruning.expandPolicy
        (fixedReducedPolicy pruning policy owner fixedOwner) owner)
      target rule)

/-- The hybrid policy is exactly site surgery on the expanded fixed owner,
viewed against the original expanded reduced baseline. -/
theorem hybridPolicy_eq_update_replaceSiteRule
    [DecidableEq Player] [DecidableEq Node]
    (pruning : Pruning diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    hybridPolicy pruning policy owner fixedOwner target rule =
      Profile.update (sig := nativeBehavioralSignature diagram)
        (pruning.expandPolicy policy) owner
        (replaceSiteRule (pruning.expandOwnerPolicy owner fixedOwner)
          target rule) := by
  unfold hybridPolicy fixedReducedPolicy
  rw [pruning.expandPolicy_update]
  simp only [Profile.update_same]
  rw [Profile.update_idem]

/-- The surgically modified policy depends only on the restore-at-target
hybrid parents. -/
theorem hybridPolicy_respects_restoreAllAt
    [DecidableEq Player] [DecidableEq Node]
    (pruning : Pruning diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    PolicyRespects (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)
      (restoreAllAt_subset_observed pruning target)
      (hybridPolicy pruning policy owner fixedOwner target rule) := by
  intro other site first second hagree
  by_cases hnode : site.1 = target.1
  · have howner : other = owner := by
      have htargetKind : diagram.kind site.1 = .decision owner := by
        simpa only [hnode] using target.2
      exact NodeKind.decision.inj (site.2.symm.trans htargetKind)
    subst other
    have hsite : site = target := Subtype.ext hnode
    subst site
    have hconfig : first = second := by
      funext parent
      have hvalue := congrFun hagree
        (⟨parent.1, by
          simp [MAIDPruningFixpointGraph.Pruning.restoreAllAt]⟩ :
          {node // node ∈
            MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target
              target.1})
      exact hvalue
    unfold hybridPolicy
    rw [Profile.update_same, replaceSiteRule_same]
    exact congrArg rule hconfig
  · have hkept :
        Config.restrict (pruning.kept_sub_observed site.1) first =
          Config.restrict (pruning.kept_sub_observed site.1) second := by
      funext parent
      have hvalue := congrFun hagree
        (⟨parent.1, by
          simp [MAIDPruningFixpointGraph.Pruning.restoreAllAt, hnode]⟩ :
          {node // node ∈
            MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target
              site.1})
      exact hvalue
    by_cases howner : other = owner
    · subst other
      unfold hybridPolicy
      rw [Profile.update_same,
        replaceSiteRule_of_ne
          (pruning.expandPolicy
            (fixedReducedPolicy pruning policy owner fixedOwner) owner)
          target site rule (by
            intro hsite
            exact hnode (congrArg Subtype.val hsite))]
      simp only [Pruning.expandPolicy, fixedReducedPolicy,
        Profile.update_same, Pruning.expandOwnerPolicy]
      exact congrArg (fixedOwner site) hkept
    · unfold hybridPolicy
      rw [Profile.update_of_ne
        (sig := nativeBehavioralSignature diagram) _ _ howner]
      simp only [Pruning.expandPolicy, fixedReducedPolicy,
        Profile.update_of_ne _ _ howner, Pruning.expandOwnerPolicy]
      exact congrArg (policy other site) hkept

/-- Away from the restored target, a hybrid parent configuration is exactly a
candidate-parent configuration. -/
def candidateConfigurationOfHybrid [DecidableEq Node]
    (pruning : Pruning diagram) {owner : Player}
    (target : DecisionSite diagram owner) (node : Node)
    (hne : node ≠ target.1)
    (configuration : ParentConfiguration diagram.Value
      (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)) node) :
    ParentConfiguration diagram.Value
      (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
        (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents pruning))
      node :=
  fun parent => configuration
    ⟨parent.1, by
      simp [MAIDPruningFixpointGraph.effectiveParentsUnder,
        MAIDPruningFixpointGraph.Pruning.restoreAllAt, hne] at parent ⊢⟩

/-- Canonical candidate kernels away from the target and the arbitrary full
target rule, indexed by restore-at-target effective parents. -/
def hybridEffectiveKernels [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    LocalKernels diagram.Value
      (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)) :=
  fun node configuration => by
    by_cases htarget : node = target.1
    · subst node
      exact rule (fun parent => configuration
        ⟨parent.1, by
          unfold MAIDPruningFixpointGraph.effectiveParentsUnder
          rw [target.2]
          simp [MAIDPruningFixpointGraph.Pruning.restoreAllAt]⟩)
    · exact reducedEffectiveKernels semantics pruning
        (fixedReducedPolicy pruning policy owner fixedOwner) node
        (candidateConfigurationOfHybrid pruning target node htarget
          configuration)

theorem hybridEffectiveKernels_of_ne
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) (node : Node)
    (hne : node ≠ target.1)
    (configuration : ParentConfiguration diagram.Value
      (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)) node) :
    hybridEffectiveKernels semantics pruning policy owner fixedOwner target rule
        node configuration =
      reducedEffectiveKernels semantics pruning
        (fixedReducedPolicy pruning policy owner fixedOwner) node
        (candidateConfigurationOfHybrid pruning target node hne
          configuration) := by
  simp [hybridEffectiveKernels, hne]

theorem hybridEffectiveKernels_target_parentConfiguration
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) (assignment : Assignment diagram) :
    hybridEffectiveKernels semantics pruning policy owner fixedOwner target rule
        target.1
        (parentConfiguration diagram.Value
          (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
            (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target))
          assignment target.1) =
      rule (Assignment.restrict diagram assignment
        (diagram.observedParents target.1)) := by
  simp [hybridEffectiveKernels]
  apply congrArg rule
  funext parent
  rfl

/-- Reading a hybrid kernel from an assignment is the canonical node law of
the surgically modified full policy. -/
theorem hybridEffectiveKernels_parentConfiguration
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1))
    (assignment : Assignment diagram) (node : Node) :
    hybridEffectiveKernels semantics pruning policy owner fixedOwner target rule
        node
        (parentConfiguration diagram.Value
          (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
            (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target))
          assignment node) =
      effectiveKernels semantics
        (hybridPolicy pruning policy owner fixedOwner target rule) node
        (parentConfiguration diagram.Value (effectiveParents diagram)
          assignment node) := by
  rw [effectiveKernels_parentConfiguration]
  by_cases htarget : node = target.1
  · subst node
    rw [hybridEffectiveKernels_target_parentConfiguration]
    unfold hybridPolicy
    rw [assignmentNodeLaw_update_replaceSiteRule_target]
  · rw [hybridEffectiveKernels_of_ne semantics pruning policy owner fixedOwner
      target rule node htarget]
    have hconfiguration :
        candidateConfigurationOfHybrid pruning target node htarget
            (parentConfiguration diagram.Value
              (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
                (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target))
              assignment node) =
          parentConfiguration diagram.Value
            (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
              (MAIDPruningFixpointGraph.Pruning.candidateDecisionParents
                pruning)) assignment node := by
      funext parent
      rfl
    rw [hconfiguration,
      reducedEffectiveKernels_parentConfiguration,
      effectiveKernels_parentConfiguration]
    unfold hybridPolicy
    rw [assignmentNodeLaw_update_replaceSiteRule_of_ne semantics
      (pruning.expandPolicy
        (fixedReducedPolicy pruning policy owner fixedOwner)) owner
      (pruning.expandPolicy
        (fixedReducedPolicy pruning policy owner fixedOwner) owner)
      target rule assignment node htarget, Profile.update_eq_self]

/-- Canonical play under target surgery factorizes over the restore-at-target
effective-parent graph. -/
theorem native_play_factorizes_hybrid
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (pruning : Pruning diagram)
    (policy : pruning.ReducedPolicy) (owner : Player)
    (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    Factorizes diagram.Value
      ((nativeBehavioralGameForm semantics).play
        (hybridPolicy pruning policy owner fixedOwner target rule))
      (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target))
      (hybridEffectiveKernels semantics pruning policy owner fixedOwner target
        rule) := by
  intro assignment
  calc
    ((nativeBehavioralGameForm semantics).play
        (hybridPolicy pruning policy owner fixedOwner target rule)).prob
          assignment =
        factorProduct diagram.Value (effectiveParents diagram)
          (effectiveKernels semantics
            (hybridPolicy pruning policy owner fixedOwner target rule))
          Finset.univ assignment :=
      native_play_prob_eq_factorProduct_univ topological semantics
        (hybridPolicy pruning policy owner fixedOwner target rule) assignment
    _ = _ := by
      unfold factorProduct localFactor
      apply Finset.prod_congr rfl
      intro node _
      rw [hybridEffectiveKernels_parentConfiguration]

/-! ## Exact utility augmentation -/

/-- Read a base hybrid-parent configuration from augmented coordinates. -/
def hybridBaseParentConfiguration [DecidableEq Node]
    (view : UtilityView semantics) {graphOwner : Player}
    (pruning : Pruning diagram) {owner : Player}
    (target : DecisionSite diagram owner) (node : Node)
    (configuration : ParentConfiguration
      (graphValue view (owner := graphOwner))
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target))
      (.base node)) :
    ParentConfiguration diagram.Value
      (MAIDPruningFixpointGraph.effectiveParentsUnder diagram
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target)) node :=
  fun parent => configuration
    ⟨.base parent.1, by
      simp [MAIDPruningFixpointGraph.UtilityView.graphParentsUnder]⟩

/-- Utility-term parent scopes are unchanged by the hybrid decision graph. -/
def hybridUtilityParentConfiguration [DecidableEq Node]
    (view : UtilityView semantics) {graphOwner : Player}
    (pruning : Pruning diagram) {owner : Player}
    (target : DecisionSite diagram owner) (site : view.UtilitySite graphOwner)
    (configuration : ParentConfiguration
      (graphValue view (owner := graphOwner))
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target))
      (.utility site)) :
    Config diagram (view.term site).parents :=
  fun parent => configuration
    ⟨.base parent.1, by
      simp [MAIDPruningFixpointGraph.UtilityView.graphParentsUnder]⟩

/-- Hybrid augmented kernels pair the exact native hybrid kernels with the
unchanged deterministic finite utility leaves. -/
def hybridAugmentedKernels
    [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) {graphOwner : Player}
    (pruning : Pruning diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    LocalKernels (graphValue view (owner := graphOwner))
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target))
  | .base node, configuration =>
      hybridEffectiveKernels semantics pruning policy owner fixedOwner target
        rule node
        (hybridBaseParentConfiguration view pruning target node configuration)
  | .utility site, configuration =>
      FinDist.pure
        (hybridUtilityParentConfiguration view pruning target site configuration)

/-- Hybrid and original augmented local factors agree pointwise for the
canonical target-surgery policy. -/
theorem hybridLocalFactor_eq_original
    [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) {graphOwner : Player}
    (pruning : Pruning diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1))
    (assignment : AugmentedAssignment view graphOwner)
    (node : view.GraphNode graphOwner) :
    localFactor (graphValue view (owner := graphOwner))
        (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder view
          (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target))
        (hybridAugmentedKernels view pruning policy owner fixedOwner target rule)
        assignment node =
      localFactor (graphValue view (owner := graphOwner)) view.graphParents
        (augmentedKernels view
          (hybridPolicy pruning policy owner fixedOwner target rule))
        assignment node := by
  cases node with
  | base baseNode =>
      unfold localFactor hybridAugmentedKernels augmentedKernels
      apply congrArg
        (fun law : FinDist (diagram.Value baseNode) =>
          law.prob (assignment (.base baseNode)))
      exact hybridEffectiveKernels_parentConfiguration semantics pruning policy
        owner fixedOwner target rule (projectBase view assignment) baseNode
  | utility _ => rfl

/-- The canonical augmented target-surgery law factorizes over the
restore-at-target graph.  The utility leaves remain the exact canonical
finite-term augmentation. -/
theorem augmentedLaw_factorizes_hybrid
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (graphOwner : Player)
    (pruning : Pruning diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    Factorizes (graphValue view (owner := graphOwner))
      (augmentedLaw view graphOwner
        (hybridPolicy pruning policy owner fixedOwner target rule))
      (MAIDPruningFixpointGraph.UtilityView.graphParentsUnder view
        (MAIDPruningFixpointGraph.Pruning.restoreAllAt pruning target))
      (hybridAugmentedKernels view pruning policy owner fixedOwner target rule) :=
  by
    intro assignment
    calc
      (augmentedLaw view graphOwner
          (hybridPolicy pruning policy owner fixedOwner target rule)).prob
          assignment =
          factorProduct (graphValue view (owner := graphOwner))
            view.graphParents
            (augmentedKernels view
              (hybridPolicy pruning policy owner fixedOwner target rule))
            Finset.univ assignment :=
        MAIDUtilityFactorization.augmentedLaw_factorizes topological view
          graphOwner
          (hybridPolicy pruning policy owner fixedOwner target rule) assignment
      _ = _ := by
        unfold factorProduct
        apply Finset.prod_congr rfl
        intro node _
        exact (hybridLocalFactor_eq_original view pruning policy owner
          fixedOwner target rule assignment node).symm

end GameTheory.Experimental.PostArchitecture.MAIDPruningHybridFactorization
