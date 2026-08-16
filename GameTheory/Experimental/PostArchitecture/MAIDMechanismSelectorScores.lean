/-
# EXP-107: mechanism-selector scores and support transport

The selector cross-product law becomes a reusable equality for every finite
utility-term score at a fixed target context and action.  The same source-rule
slice proves support transport from an arbitrary changed source rule into a
fully mixed baseline source rule.  No positivity assumption is made on the
changed rule or on chance nodes.
-/

import GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorIndependence
import GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorScores

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.MAIDFactorization
open GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorFactorization
open GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorIndependence
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph.UtilityView
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality
open GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
open GameTheory.Experimental.PostArchitecture.MAIDUtilityContinuationFromCI
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable
  {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
  {semantics : Semantics diagram}

/-- The unnormalised score of one utility term at a fixed target
context/action.  It is the joint finite expectation, so it remains defined
when the target atom has zero mass. -/
def componentTermScore
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1)) (selector : Fin 2)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    [Fintype (TermConfig view term)]
    (fullValue : FullAction target) : ℝ :=
  ∑ termValue : TermConfig view term,
    ((componentAugmentedLaw view owner base replacement source sourceRule
      selector).map (fun assignment =>
        (fullAction view target assignment, termConfig view term assignment))).prob
      (fullValue, termValue) * (view.term term).payoff termValue

private theorem componentTermScore_cross_product_aux
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source target : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    (hnot : ¬ SReachable view source target)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm target term)
    (fullValue : FullAction target) (termValue : TermConfig view term) :
    ((componentAugmentedLaw view owner base replacement source sourceRule 0).map
        (fun assignment =>
          (fullAction view target assignment, termConfig view term assignment))).prob
        (fullValue, termValue) *
      ((componentAugmentedLaw view owner base replacement source sourceRule 1).map
        (fullAction view target)).prob fullValue =
    ((componentAugmentedLaw view owner base replacement source sourceRule 0).map
        (fullAction view target)).prob fullValue *
      ((componentAugmentedLaw view owner base replacement source sourceRule 1).map
        (fun assignment =>
          (fullAction view target assignment, termConfig view term assignment))).prob
        (fullValue, termValue) :=
  componentTerm_cross_product topological view owner base replacement source
    target sourceRule hnot term hrelevant fullValue termValue

/-- The two source components give the same term score after cross-multiplying
by their target-context masses. -/
theorem componentTermScore_cross_product
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source target : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    (hnot : ¬ SReachable view source target)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm target term)
    (fullValue : FullAction target)
    [Fintype (TermConfig view term)] :
    componentTermScore view owner base replacement source sourceRule 0 target
        term fullValue *
      ((componentAugmentedLaw view owner base replacement source sourceRule 1).map
        (fullAction view target)).prob fullValue =
    ((componentAugmentedLaw view owner base replacement source sourceRule 0).map
        (fullAction view target)).prob fullValue *
      componentTermScore view owner base replacement source sourceRule 1 target
        term fullValue := by
  unfold componentTermScore
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro termValue htermValue
  have hcross := componentTermScore_cross_product_aux topological view owner
    base replacement source target sourceRule hnot term hrelevant fullValue
    termValue
  calc
    _ = (((componentAugmentedLaw view owner base replacement source sourceRule 0).map
          (fun assignment =>
            (fullAction view target assignment, termConfig view term assignment))).prob
          (fullValue, termValue) *
        ((componentAugmentedLaw view owner base replacement source sourceRule 1).map
          (fullAction view target)).prob fullValue) *
        (view.term term).payoff termValue := by ring
    _ = (((componentAugmentedLaw view owner base replacement source sourceRule 0).map
          (fullAction view target)).prob fullValue *
        ((componentAugmentedLaw view owner base replacement source sourceRule 1).map
          (fun assignment =>
            (fullAction view target assignment, termConfig view term assignment))).prob
          (fullValue, termValue)) *
        (view.term term).payoff termValue := by rw [hcross]
    _ = _ := by ring

/-- On a target atom reached by both components, the corresponding term
conditional expectations agree.  The cross-product form above remains the
primitive statement and does not require these positivity hypotheses. -/
private theorem componentTermScore_conditional_eq
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source target : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    (hnot : ¬ SReachable view source target)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm target term)
    (fullValue : FullAction target) [Fintype (TermConfig view term)]
    (hbase : 0 <
      ((componentAugmentedLaw view owner base replacement source sourceRule 0).map
        (fullAction view target)).prob fullValue)
    (hchanged : 0 <
      ((componentAugmentedLaw view owner base replacement source sourceRule 1).map
        (fullAction view target)).prob fullValue) :
    componentTermScore view owner base replacement source sourceRule 0 target
        term fullValue /
          ((componentAugmentedLaw view owner base replacement source sourceRule 0).map
            (fullAction view target)).prob fullValue =
      componentTermScore view owner base replacement source sourceRule 1 target
        term fullValue /
          ((componentAugmentedLaw view owner base replacement source sourceRule 1).map
            (fullAction view target)).prob fullValue := by
  apply (div_eq_div_iff hbase.ne' hchanged.ne').2
  have hcross := componentTermScore_cross_product topological view owner base
    replacement source target sourceRule hnot term hrelevant fullValue
  simpa [mul_comm] using hcross

private theorem localFactor_pos_of_factorProduct_pos
    [Fintype Node] [DecidableEq Node]
    {parents : Node → Finset Node}
    {kernels : LocalKernels diagram.Value parents}
    {assignment : Assignment diagram}
    (hproduct : 0 < factorProduct diagram.Value parents kernels Finset.univ
      assignment) (node : Node) :
    0 < localFactor diagram.Value parents kernels assignment node := by
  have hne : localFactor diagram.Value parents kernels assignment node ≠ 0 := by
    intro hzero
    have hproductZero :
        factorProduct diagram.Value parents kernels Finset.univ assignment = 0 := by
      unfold factorProduct
      apply Finset.prod_eq_zero (Finset.mem_univ node)
      exact hzero
    exact (ne_of_gt hproduct) hproductZero
  exact lt_of_le_of_ne
    (FinDist.prob_nonneg _ _) hne.symm

private theorem baseline_source_localFactor_pos
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (assignment : Assignment diagram)
    (hmixed : FullyMixedAt replacement source) :
    0 < localFactor diagram.Value (effectiveParents diagram)
        (effectiveKernels semantics
          (baselinePolicy base owner replacement)) assignment source.1 := by
  unfold localFactor
  rw [effectiveKernels_parentConfiguration]
  have hsourceLaw := assignmentNodeLaw_update_replaceSiteRule_target semantics
    base owner replacement source (replacement source) assignment
  have hpolicy :
      Profile.update (sig := nativeBehavioralSignature diagram) base owner
          (replaceSiteRule replacement source (replacement source)) =
        baselinePolicy base owner replacement := by
    unfold baselinePolicy
    rw [replaceSiteRule_self]
  rw [← hpolicy, hsourceLaw]
  simpa [baselinePolicy, replaceSiteRule_self] using
    (FinDist.prob_pos_iff.mpr
      (hmixed (Assignment.restrict diagram assignment
        (diagram.observedParents source.1)) (assignment source.1)))

private theorem baseline_factorProduct_pos_of_changed_support
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    (assignment : Assignment diagram)
    (hchanged : assignment ∈
      ((nativeBehavioralGameForm semantics).play
        (componentPolicy base owner replacement source sourceRule 1)).support)
    (hmixed : FullyMixedAt replacement source) :
    0 < factorProduct diagram.Value (effectiveParents diagram)
        (effectiveKernels semantics (baselinePolicy base owner replacement))
        Finset.univ assignment := by
  have hchangedProb : 0 <
      ((nativeBehavioralGameForm semantics).play
        (componentPolicy base owner replacement source sourceRule 1)).prob
          assignment := FinDist.prob_pos_iff.mpr hchanged
  have hchangedProduct : 0 < factorProduct diagram.Value
      (effectiveParents diagram)
      (effectiveKernels semantics
        (componentPolicy base owner replacement source sourceRule 1))
      Finset.univ assignment := by
    rw [← native_play_prob_eq_factorProduct_univ topological semantics
      (componentPolicy base owner replacement source sourceRule 1) assignment]
    exact hchangedProb
  apply Finset.prod_pos
  intro node hnode
  by_cases hsource : node = source.1
  · subst node
    exact baseline_source_localFactor_pos semantics base owner replacement
      source assignment hmixed
  · have hchangedLocal := localFactor_pos_of_factorProduct_pos
      hchangedProduct node
    rw [show localFactor diagram.Value (effectiveParents diagram)
        (effectiveKernels semantics (baselinePolicy base owner replacement))
        assignment node =
      localFactor diagram.Value (effectiveParents diagram)
        (effectiveKernels semantics
          (componentPolicy base owner replacement source sourceRule 1))
        assignment node by
      unfold localFactor
      rw [effectiveKernels_parentConfiguration,
        effectiveKernels_parentConfiguration]
      simpa [baselinePolicy, componentPolicy] using
        (congrArg (fun law => law.prob (assignment node))
          (assignmentNodeLaw_update_replaceSiteRule_of_ne semantics base owner
            replacement source sourceRule assignment node hsource)).symm]
    exact hchangedLocal

/-- A changed source rule cannot create a target full-action atom outside the
baseline law when the baseline source rule is fully mixed. -/
theorem componentFullAction_support_subset_of_fullyMixed
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (view : UtilityView semantics)
    (owner : Player) (base : Policy diagram)
    (replacement : OwnerPolicy diagram owner)
    (source target : DecisionSite diagram owner)
    (sourceRule : Config diagram (diagram.observedParents source.1) →
      FinDist (diagram.Value source.1))
    (fullValue : FullAction target)
    (hmixed : FullyMixedAt replacement source)
    (hchanged : fullValue ∈
      ((componentAugmentedLaw view owner base replacement source sourceRule 1).map
        (fullAction view target)).support) :
    fullValue ∈
      ((componentAugmentedLaw view owner base replacement source sourceRule 0).map
        (fullAction view target)).support := by
  rw [FinDist.support_map] at hchanged ⊢
  obtain ⟨assignment, hassignment, hfull⟩ := hchanged
  rw [componentAugmentedLaw, augmentedLaw, FinDist.support_map] at hassignment
  obtain ⟨nativeAssignment, hnative, haugmented⟩ := hassignment
  have hproduct := baseline_factorProduct_pos_of_changed_support topological
    semantics base owner replacement source sourceRule
    nativeAssignment hnative hmixed
  · refine ⟨augmentAssignment view (owner := owner) nativeAssignment, ?_, ?_⟩
    · unfold componentAugmentedLaw augmentedLaw
      rw [FinDist.support_map (augmentAssignment view (owner := owner))]
      refine ⟨nativeAssignment, ?_, rfl⟩
      apply FinDist.prob_pos_iff.mp
      have hprob : 0 <
          ((nativeBehavioralGameForm semantics).play
            (baselinePolicy base owner replacement)).prob nativeAssignment := by
        rw [native_play_prob_eq_factorProduct_univ topological semantics
          (baselinePolicy base owner replacement) nativeAssignment]
        exact hproduct
      simpa [componentPolicy] using hprob
    · rw [haugmented]
      exact hfull

end GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorScores
