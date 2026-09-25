/-
# EXP-107: one-source strategic nonreachability

Changing a fully mixed reference rule at a source that is not strategically
reachable from a distinct same-owner target preserves target-rule optimality.
The proof uses the exact mechanism-selector cross law and canonical site
surgery.  All score comparisons are division-free, including at zero-mass
target contexts and actions.
-/

import GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorScores
import GameTheory.Experimental.PostArchitecture.MAIDPruningNonrelevantInvariance
import GameTheory.Experimental.PostArchitecture.MAIDPruningRelevantContinuation
import GameTheory.Experimental.PostArchitecture.MAIDSiteOptimalityScores

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDStrategicNonreachability

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorFactorization
open GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorIndependence
open GameTheory.Experimental.PostArchitecture.MAIDMechanismSelectorScores
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
open GameTheory.Experimental.PostArchitecture.MAIDPruningRelevantContinuation
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality
open GameTheory.Experimental.PostArchitecture.MAIDSiteOptimalityScores
open GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
open GameTheory.Experimental.PostArchitecture.MAIDSiteReplacementContext
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityContinuationFromCI
open GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable
  {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
  {semantics : Semantics diagram}

private abbrev TargetAtom {owner : Player}
    (target : DecisionSite diagram owner) :=
  MAIDReplacementInvariantUtility.FullContext target ×
    diagram.Value target.1

/-! ## Full-information bridge for nonrelevant terms -/

private def fullPruning : Pruning diagram where
  kept := diagram.observedParents
  kept_sub_observed _ _ hmember := hmember

private def reducedPolicyOfPolicy (policy : Policy diagram) :
    (fullPruning (diagram := diagram)).ReducedPolicy :=
  policy

private def reducedOwnerPolicyOfOwnerPolicy {owner : Player}
    (replacement : OwnerPolicy diagram owner) :
    (fullPruning (diagram := diagram)).ReducedOwnerPolicy owner :=
  replacement

private theorem expandPolicy_reducedPolicyOfPolicy
    (policy : Policy diagram) :
    (fullPruning (diagram := diagram)).expandPolicy
        (reducedPolicyOfPolicy policy) = policy := by
  funext owner site context
  apply congrArg (policy owner site)
  funext node
  rfl

private theorem expandOwnerPolicy_reducedOwnerPolicyOfOwnerPolicy
    {owner : Player} (replacement : OwnerPolicy diagram owner) :
    (fullPruning (diagram := diagram)).expandOwnerPolicy owner
        (reducedOwnerPolicyOfOwnerPolicy replacement) = replacement := by
  funext site context
  apply congrArg (replacement site)
  funext node
  rfl

private theorem restoreAllAt_fullPruning
    [DecidableEq Node] {owner : Player}
    (target : DecisionSite diagram owner) :
    Pruning.restoreAllAt (fullPruning (diagram := diagram)) target =
      fun node => diagram.observedParents node := by
  funext node
  simp [Pruning.restoreAllAt, fullPruning]

private theorem graphParentsUnder_observed_eq
    [DecidableEq Node] (view : UtilityView semantics) (owner : Player) :
    MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        (owner := owner) view (fun node => diagram.observedParents node) =
      view.graphParents := by
  funext node
  cases node with
  | utility term => rfl
  | base node =>
      unfold MAIDPruningFixpointGraph.UtilityView.graphParentsUnder
        MAIDPruningFixpointGraph.effectiveParentsUnder
        MAIDRequisiteObservation.UtilityView.graphParents
        MAIDRequisiteObservation.effectiveParents
      cases hkind : diagram.kind node <;> rfl

private theorem not_relevant_under_fullPruning
    [DecidableEq Node] (view : UtilityView semantics) {owner : Player}
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    (hnonrelevant : ¬ view.IsRelevantUtilityTerm target term) :
    ¬ MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
      (Pruning.restoreAllAt (fullPruning (diagram := diagram)) target)
      target term := by
  rw [restoreAllAt_fullPruning target]
  unfold MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder
  rw [graphParentsUnder_observed_eq view owner]
  unfold MAIDRequisiteObservation.UtilityView.IsRelevantUtilityTerm at hnonrelevant
  unfold MAIDRequisiteObservation.UtilityView.DirectedEdge at hnonrelevant
  unfold FiniteBNMoralSeparation.DirectedEdge
  exact hnonrelevant

private theorem nonrelevantTerm_site_marginal_eq
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    [Fintype (Assignment diagram)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    (hnonrelevant : ¬ view.IsRelevantUtilityTerm target term)
    (first second : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1)) :
    (siteReplacementLaw semantics base owner replacement target first).map
        (fun assignment => Assignment.restrict diagram assignment
          (view.term term).parents) =
      (siteReplacementLaw semantics base owner replacement target second).map
        (fun assignment => Assignment.restrict diagram assignment
          (view.term term).parents) := by
  have hmarginal :=
    MAIDPruningNonrelevantInvariance.nonrelevantTerm_marginal_eq
      topological view (fullPruning (diagram := diagram))
      (reducedPolicyOfPolicy base) owner
      (reducedOwnerPolicyOfOwnerPolicy replacement) target term
      (not_relevant_under_fullPruning view target term hnonrelevant)
      first second
  rw [expandPolicy_reducedPolicyOfPolicy,
    expandOwnerPolicy_reducedOwnerPolicyOfOwnerPolicy] at hmarginal
  exact hmarginal

/-! ## Site scores through constant-action probes -/

private def siteTermFullScore
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1)) (view : UtilityView semantics)
    (term : view.UtilitySite owner) [Fintype (TermConfig view term)]
    (full : TargetAtom target) : ℝ :=
  ∑ termValue : TermConfig view term,
    (((siteReplacementLaw semantics base owner replacement target rule).map
      (siteFullActionTermProjection view target term))
        (full, termValue)).toReal * (view.term term).payoff termValue

private theorem siteTermFullScore_rule_mul_constant
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1)) (view : UtilityView semantics)
    (term : view.UtilitySite owner) [Fintype (TermConfig view term)]
    (context : MAIDReplacementInvariantUtility.FullContext target)
    (action : diagram.Value target.1) :
    siteTermFullScore semantics base owner replacement target rule view term
        (context, action) =
      ((rule context) action).toReal *
        siteTermFullScore semantics base owner replacement target
          (constantSiteRule target action) view term (context, action) := by
  unfold siteTermFullScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro termValue _
  have hpoint := siteReplacementLaw_prob_eq_rule_mul_constant topological
    semantics base owner replacement target view term rule context action
      termValue
  rw [hpoint]
  rw [ENNReal.toReal_mul]
  ring

private theorem siteRuleExpectedUtility_eq_sum_termFullScore
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    [Fintype (MAIDReplacementInvariantUtility.FullContext target)]
    [Fintype (Assignment diagram)]
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (rule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1)) :
    siteRuleExpectedUtility semantics base owner replacement target rule
        (payoffIntegrable_of_finite _ _) =
      ∑ full : TargetAtom target, ∑ term : view.UtilitySite owner,
        siteTermFullScore semantics base owner replacement target rule view
          term full := by
  unfold siteRuleExpectedUtility expectedUtility
  let law := siteReplacementLaw semantics base owner replacement target rule
  calc
    expect law (fun assignment => semantics.utility owner assignment)
        (payoffIntegrable_of_finite _ _) =
        expect law (fun assignment => ∑ term : view.UtilitySite owner,
          (view.term term).payoff
            (Assignment.restrict diagram assignment
              (view.term term).parents)) (payoffIntegrable_of_finite _ _) := by
      apply expect_congr_on_support
      intro assignment _
      simpa [UtilityView.term, UtilityTerm.value] using
        view.utility_eq_sum owner assignment
    _ = ∑ term : view.UtilitySite owner,
        expect law (fun assignment =>
          (view.term term).payoff
            (Assignment.restrict diagram assignment
              (view.term term).parents)) (payoffIntegrable_of_finite _ _) := by
      exact expect_sum law (fun term : view.UtilitySite owner =>
        fun assignment => (view.term term).payoff
          (Assignment.restrict diagram assignment (view.term term).parents))
        (fun _ => payoffIntegrable_of_finite _ _)
    _ = ∑ term : view.UtilitySite owner, ∑ full : TargetAtom target,
        siteTermFullScore semantics base owner replacement target rule view
          term full := by
      apply Finset.sum_congr rfl
      intro term _
      have hprojection :
          (fun assignment : Assignment diagram =>
            ((Assignment.restrict diagram assignment
                (diagram.observedParents target.1), assignment target.1),
              Assignment.restrict diagram assignment
                (view.term term).parents)) =
            siteFullActionTermProjection view target term := by
        funext assignment
        rfl
      unfold siteTermFullScore
      rw [← hprojection]
      exact expect_eq_sum_joint_fibres law
          (fun assignment =>
            (Assignment.restrict diagram assignment
              (diagram.observedParents target.1), assignment target.1))
          (fun assignment => Assignment.restrict diagram assignment
            (view.term term).parents)
          (view.term term).payoff
    _ = _ := Finset.sum_comm

private def siteRelevantValue
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    [Fintype (MAIDReplacementInvariantUtility.FullContext target)]
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (rule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1)) : ℝ := by
  classical
  exact ∑ context : MAIDReplacementInvariantUtility.FullContext target,
    ∑ action : diagram.Value target.1,
      ∑ term ∈ Finset.univ.filter
          (view.IsRelevantUtilityTerm target),
        siteTermFullScore semantics base owner replacement target rule view
          term (context, action)

private def siteNonrelevantValue
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (rule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1)) : ℝ := by
  classical
  exact ∑ term ∈ Finset.univ.filter
      (¬ view.IsRelevantUtilityTerm target ·),
    expect ((siteReplacementLaw semantics base owner replacement target rule).map
      (fun assignment => Assignment.restrict diagram assignment
        (view.term term).parents)) (view.term term).payoff
      (payoffIntegrable_of_finite _ _)

private def siteRelevantProbeScore
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (context : MAIDReplacementInvariantUtility.FullContext target)
    (action : diagram.Value target.1) : ℝ := by
  classical
  exact ∑ term ∈ Finset.univ.filter
      (view.IsRelevantUtilityTerm target),
    siteTermFullScore semantics base owner replacement target
      (constantSiteRule target action) view term (context, action)

private theorem siteRelevantValue_eq_sum_probe
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    [Fintype (MAIDReplacementInvariantUtility.FullContext target)]
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (rule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1)) :
    siteRelevantValue semantics base owner replacement target view rule =
      ∑ context : MAIDReplacementInvariantUtility.FullContext target,
        ∑ action : diagram.Value target.1,
        ((rule context) action).toReal *
            siteRelevantProbeScore semantics base owner replacement target
              view context action := by
  classical
  unfold siteRelevantValue siteRelevantProbeScore
  apply Finset.sum_congr rfl
  intro context _
  apply Finset.sum_congr rfl
  intro action _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro term hterm
  exact siteTermFullScore_rule_mul_constant topological semantics base owner
    replacement target rule view term context action

private theorem siteRuleExpectedUtility_eq_relevant_add_nonrelevant
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    [Fintype (Assignment diagram)]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    [Fintype (MAIDReplacementInvariantUtility.FullContext target)]
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (rule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1)) :
    siteRuleExpectedUtility semantics base owner replacement target rule
        (payoffIntegrable_of_finite _ _) =
      siteRelevantValue semantics base owner replacement target view rule +
        siteNonrelevantValue semantics base owner replacement target view
          rule := by
  classical
  rw [siteRuleExpectedUtility_eq_sum_termFullScore semantics base owner
    replacement target view rule]
  unfold siteRelevantValue siteNonrelevantValue
  have hterm : ∀ term : view.UtilitySite owner,
      (∑ full : TargetAtom target,
          siteTermFullScore semantics base owner replacement target rule view
            term full) =
        expect ((siteReplacementLaw semantics base owner replacement target rule).map
          (fun assignment => Assignment.restrict diagram assignment
            (view.term term).parents)) (view.term term).payoff
          (payoffIntegrable_of_finite _ _) := by
    intro term
    rw [expect_map]
    let law := siteReplacementLaw semantics base owner replacement target rule
    have hfibres := expect_eq_sum_joint_fibres law
      (fun assignment =>
        (Assignment.restrict diagram assignment
          (diagram.observedParents target.1), assignment target.1))
      (fun assignment => Assignment.restrict diagram assignment
        (view.term term).parents)
      (view.term term).payoff
    have hprojection :
        (fun assignment : Assignment diagram =>
          ((Assignment.restrict diagram assignment
              (diagram.observedParents target.1), assignment target.1),
            Assignment.restrict diagram assignment
              (view.term term).parents)) =
          siteFullActionTermProjection view target term := by
      funext assignment
      rfl
    unfold siteTermFullScore
    rw [← hprojection]
    exact hfibres.symm
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, term]
    rw [hterm term]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (view.IsRelevantUtilityTerm target)]
  congr 1
  calc
    ∑ term ∈ Finset.univ.filter (view.IsRelevantUtilityTerm target),
        expect ((siteReplacementLaw semantics base owner replacement target rule).map
          (fun assignment => Assignment.restrict diagram assignment
            (view.term term).parents)) (view.term term).payoff
          (payoffIntegrable_of_finite _ _) =
      ∑ term ∈ Finset.univ.filter (view.IsRelevantUtilityTerm target),
        ∑ full : TargetAtom target,
          siteTermFullScore semantics base owner replacement target rule view
            term full := by
      apply Finset.sum_congr rfl
      intro term _
      rw [hterm term]
    _ = ∑ full : TargetAtom target,
        ∑ term ∈ Finset.univ.filter (view.IsRelevantUtilityTerm target),
          siteTermFullScore semantics base owner replacement target rule view
            term full := by
      rw [Finset.sum_comm]
    _ = ∑ context : MAIDReplacementInvariantUtility.FullContext target,
        ∑ action : diagram.Value target.1,
          ∑ term ∈ Finset.univ.filter
              (view.IsRelevantUtilityTerm target),
            siteTermFullScore semantics base owner replacement target rule view
              term (context, action) := by
      unfold TargetAtom
      rw [Fintype.sum_prod_type]

private theorem siteNonrelevantValue_eq
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    [Fintype (Assignment diagram)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (first second : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1)) :
    siteNonrelevantValue semantics base owner replacement target view first =
      siteNonrelevantValue semantics base owner replacement target view
        second := by
  classical
  unfold siteNonrelevantValue
  apply Finset.sum_congr rfl
  intro term hterm
  have hnonrelevant : ¬ view.IsRelevantUtilityTerm target term := by
    simpa using (Finset.mem_filter.mp hterm).2
  exact expect_congr_law
    (nonrelevantTerm_site_marginal_eq topological view base owner replacement
      target term hnonrelevant first second) _ _ _

/-! ## Mechanism components as site-replacement probes -/

private theorem componentPolicy_zero_eq_siteReplacement
    [DecidableEq Player] [DecidableEq Node]
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (source target : DecisionSite diagram owner)
    (sourceRule : MAIDReplacementInvariantUtility.FullContext source →
      PMF (diagram.Value source.1))
    (targetRule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1)) :
    componentPolicy base owner (replaceSiteRule replacement target targetRule)
        source sourceRule 0 =
      Profile.update (sig := nativeBehavioralSignature diagram) base owner
        (replaceSiteRule replacement target targetRule) := by
  simp [componentPolicy, baselinePolicy]

private theorem componentPolicy_one_eq_siteReplacement
    [DecidableEq Player] [DecidableEq Node]
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (source target : DecisionSite diagram owner) (hneq : source ≠ target)
    (sourceRule : MAIDReplacementInvariantUtility.FullContext source →
      PMF (diagram.Value source.1))
    (targetRule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1)) :
    componentPolicy base owner (replaceSiteRule replacement target targetRule)
        source sourceRule 1 =
      Profile.update (sig := nativeBehavioralSignature diagram) base owner
        (replaceSiteRule (replaceSiteRule replacement source sourceRule)
          target targetRule) := by
  unfold componentPolicy
  rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
  apply congrArg
    (Profile.update (sig := nativeBehavioralSignature diagram) base owner)
  exact replaceSiteRule_commute_of_ne replacement target source hneq.symm
    targetRule sourceRule

private theorem componentTermScore_eq_siteTermFullScore
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : MAIDReplacementInvariantUtility.FullContext source →
      PMF (diagram.Value source.1)) (selector : Fin 2)
    (target : DecisionSite diagram owner)
    (targetReplacement : OwnerPolicy diagram owner)
    (targetRule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1))
    (hpolicy : componentPolicy base owner replacement source sourceRule
        selector =
      Profile.update (sig := nativeBehavioralSignature diagram) base owner
        (replaceSiteRule targetReplacement target targetRule))
    (term : view.UtilitySite owner) [Fintype (TermConfig view term)]
    (full : TargetAtom target) :
    componentTermScore view owner base replacement source sourceRule selector
        target term full =
      siteTermFullScore semantics base owner targetReplacement target
        targetRule view term full := by
  unfold componentTermScore componentAugmentedLaw augmentedLaw
    siteTermFullScore siteReplacementLaw
  rw [hpolicy, PMF.map_comp]
  rfl

private theorem componentFullActionMass_eq_siteFullActionMass
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player)
    (base : Policy diagram) (replacement : OwnerPolicy diagram owner)
    (source : DecisionSite diagram owner)
    (sourceRule : MAIDReplacementInvariantUtility.FullContext source →
      PMF (diagram.Value source.1)) (selector : Fin 2)
    (target : DecisionSite diagram owner)
    (targetReplacement : OwnerPolicy diagram owner)
    (targetRule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1))
    (hpolicy : componentPolicy base owner replacement source sourceRule
        selector =
      Profile.update (sig := nativeBehavioralSignature diagram) base owner
        (replaceSiteRule targetReplacement target targetRule))
    (full : TargetAtom target) :
    (((componentAugmentedLaw view owner base replacement source sourceRule
      selector).map (fullAction view target)) full).toReal =
      (((siteReplacementLaw semantics base owner targetReplacement target
        targetRule).map
        (fun assignment =>
          (Assignment.restrict diagram assignment
            (diagram.observedParents target.1), assignment target.1)))
          full).toReal := by
  unfold componentAugmentedLaw augmentedLaw siteReplacementLaw
  rw [hpolicy, PMF.map_comp]
  rfl

private def siteContextMass
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (context : MAIDReplacementInvariantUtility.FullContext target) : ℝ :=
  ((siteReplacementContextLawAt topological semantics base owner replacement
    target).contextLaw context).toReal

private theorem constantSiteRule_fullAction_prob_eq_contextMass
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    [DecidableEq (MAIDReplacementInvariantUtility.FullContext target)]
    (context : MAIDReplacementInvariantUtility.FullContext target)
    (action : diagram.Value target.1) :
    (((siteReplacementLaw semantics base owner replacement target
        (constantSiteRule target action)).map
      (fun assignment =>
        (Assignment.restrict diagram assignment
          (diagram.observedParents target.1), assignment target.1)))
        (context, action)).toReal =
      siteContextMass topological semantics base owner replacement target
        context := by
  classical
  rw [(siteReplacementContextLawAt topological semantics base owner
    replacement target).contextAction_eq (constantSiteRule target action)]
  unfold siteContextMass
  simp only [constantSiteRule, PMF.pure_map]
  have hkernel :
      (fun observed : MAIDReplacementInvariantUtility.FullContext target =>
        PMF.pure (observed, action)) =
      PMF.pure ∘ (fun observed => (observed, action)) := rfl
  rw [hkernel, PMF.bind_pure_comp]
  rw [pmf_map_apply_of_injective _ (by
    intro first second heq
    exact congrArg Prod.fst heq) context]

private theorem siteRelevantProbeScore_cross_product
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (source target : DecisionSite diagram owner) (hneq : source ≠ target)
    (sourceRule : MAIDReplacementInvariantUtility.FullContext source →
      PMF (diagram.Value source.1))
    (hnot : ¬ MAIDPruningFixpointGraph.UtilityView.SReachable view source
      target)
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (context : MAIDReplacementInvariantUtility.FullContext target)
    (action : diagram.Value target.1) :
    siteRelevantProbeScore semantics base owner replacement target view
        context action *
      siteContextMass topological semantics base owner
        (replaceSiteRule replacement source sourceRule) target context =
    siteContextMass topological semantics base owner replacement target
        context *
      siteRelevantProbeScore semantics base owner
        (replaceSiteRule replacement source sourceRule) target view context
          action := by
  classical
  let targetRule := constantSiteRule target action
  let selectorReplacement := replaceSiteRule replacement target targetRule
  have hzero := componentPolicy_zero_eq_siteReplacement base owner replacement
    source target sourceRule targetRule
  have hone := componentPolicy_one_eq_siteReplacement base owner replacement
    source target hneq sourceRule targetRule
  unfold siteRelevantProbeScore
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro term hterm
  have hrelevant : view.IsRelevantUtilityTerm target term :=
    (Finset.mem_filter.mp hterm).2
  have hcross := componentTermScore_cross_product topological view owner base
    selectorReplacement source target sourceRule hnot term hrelevant
      (context, action)
  have hscoreZero := componentTermScore_eq_siteTermFullScore view owner base
    selectorReplacement source sourceRule 0 target replacement targetRule
      hzero term (context, action)
  have hscoreOne := componentTermScore_eq_siteTermFullScore view owner base
    selectorReplacement source sourceRule 1 target
      (replaceSiteRule replacement source sourceRule) targetRule hone term
        (context, action)
  have hmassZero := componentFullActionMass_eq_siteFullActionMass view owner
    base selectorReplacement source sourceRule 0 target replacement targetRule
      hzero (context, action)
  have hmassOne := componentFullActionMass_eq_siteFullActionMass view owner
    base selectorReplacement source sourceRule 1 target
      (replaceSiteRule replacement source sourceRule) targetRule hone
        (context, action)
  rw [hscoreZero, hscoreOne, hmassZero, hmassOne] at hcross
  rw [constantSiteRule_fullAction_prob_eq_contextMass topological semantics
    base owner replacement target context action] at hcross
  rw [constantSiteRule_fullAction_prob_eq_contextMass topological semantics
    base owner (replaceSiteRule replacement source sourceRule) target context
      action] at hcross
  exact hcross

private theorem siteContextMass_pos_of_changed
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (view : UtilityView semantics)
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (source target : DecisionSite diagram owner) (hneq : source ≠ target)
    (sourceRule : MAIDReplacementInvariantUtility.FullContext source →
      PMF (diagram.Value source.1))
    (hmixed : FullyMixedAt replacement source)
    (context : MAIDReplacementInvariantUtility.FullContext target)
    (hchanged : 0 < siteContextMass topological semantics base owner
      (replaceSiteRule replacement source sourceRule) target context) :
    0 < siteContextMass topological semantics base owner replacement target
      context := by
  classical
  let action := semantics.defaultValue target.1
  let targetRule := constantSiteRule target action
  let selectorReplacement := replaceSiteRule replacement target targetRule
  have hzero := componentPolicy_zero_eq_siteReplacement base owner replacement
    source target sourceRule targetRule
  have hone := componentPolicy_one_eq_siteReplacement base owner replacement
    source target hneq sourceRule targetRule
  have hmixedSelector : FullyMixedAt selectorReplacement source := by
    apply hmixed.congr source
    intro sourceContext
    dsimp only [selectorReplacement]
    rw [replaceSiteRule_of_ne replacement target source targetRule hneq]
  have hmassOne := componentFullActionMass_eq_siteFullActionMass view owner
    base selectorReplacement source sourceRule 1 target
      (replaceSiteRule replacement source sourceRule) targetRule hone
        (context, action)
  have hmassZero := componentFullActionMass_eq_siteFullActionMass view owner
    base selectorReplacement source sourceRule 0 target replacement targetRule
      hzero (context, action)
  have hchangedFull : 0 <
      (((componentAugmentedLaw view owner base selectorReplacement source
        sourceRule 1).map (fullAction view target))
          (context, action)).toReal := by
    rw [hmassOne]
    rw [constantSiteRule_fullAction_prob_eq_contextMass topological semantics
      base owner (replaceSiteRule replacement source sourceRule) target context
        action]
    exact hchanged
  have hbaselineSupport := componentFullAction_support_subset_of_fullyMixed
    topological semantics view owner base selectorReplacement source target
      sourceRule (context, action) hmixedSelector
        ((PMF.apply_pos_iff _ _).mp
          (ENNReal.toReal_pos_iff.mp hchangedFull).1)
  have hbaselineFull : 0 <
      (((componentAugmentedLaw view owner base selectorReplacement source
        sourceRule 0).map (fullAction view target))
          (context, action)).toReal :=
    ENNReal.toReal_pos
      (ne_of_gt ((PMF.apply_pos_iff _ _).mpr hbaselineSupport))
      (PMF.apply_ne_top _ _)
  rw [hmassZero] at hbaselineFull
  rw [constantSiteRule_fullAction_prob_eq_contextMass topological semantics
    base owner replacement target context action] at hbaselineFull
  exact hbaselineFull

/-! ## Optimality as pointwise probe ranking -/

private def replaceContextWithPure
    {owner : Player} (target : DecisionSite diagram owner)
    [DecidableEq (MAIDReplacementInvariantUtility.FullContext target)]
    (rule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1))
    (chosen : MAIDReplacementInvariantUtility.FullContext target)
    (action : diagram.Value target.1) :
    MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1) :=
  fun context => if context = chosen then PMF.pure action else rule context

private theorem siteRelevantProbeScore_le_of_optimal
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    [Fintype (Assignment diagram)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (view : UtilityView semantics)
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    [Fintype (MAIDReplacementInvariantUtility.FullContext target)]
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (targetRule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1))
    (hoptimal : IsOptimalSiteRule semantics base owner replacement target
      targetRule)
    (context : MAIDReplacementInvariantUtility.FullContext target)
    (action : diagram.Value target.1) :
    siteRelevantProbeScore semantics base owner replacement target view
        context action ≤
      ∑ candidate : diagram.Value target.1,
        ((targetRule context) candidate).toReal *
          siteRelevantProbeScore semantics base owner replacement target view
            context candidate := by
  classical
  let alternative := replaceContextWithPure target targetRule context action
  have hutility :
      siteRuleExpectedUtility semantics base owner replacement target
          alternative (payoffIntegrable_of_finite _ _) ≤
        siteRuleExpectedUtility semantics base owner replacement target
          targetRule (payoffIntegrable_of_finite _ _) := by
    exact (euPreference_iff _ owner _ _
      (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)).mp (hoptimal alternative)
  rw [siteRuleExpectedUtility_eq_relevant_add_nonrelevant semantics base owner
    replacement target view alternative] at hutility
  rw [siteRuleExpectedUtility_eq_relevant_add_nonrelevant semantics base owner
    replacement target view targetRule] at hutility
  have hnonrelevant := siteNonrelevantValue_eq topological view base owner
    replacement target alternative targetRule
  have hrelevant :
      siteRelevantValue semantics base owner replacement target view
          alternative ≤
        siteRelevantValue semantics base owner replacement target view
          targetRule := by
    rw [hnonrelevant] at hutility
    exact (add_le_add_iff_right _).mp hutility
  rw [siteRelevantValue_eq_sum_probe topological semantics base owner
    replacement target view alternative] at hrelevant
  rw [siteRelevantValue_eq_sum_probe topological semantics base owner
    replacement target view targetRule] at hrelevant
  let alternativeAt := fun observed =>
    ∑ candidate : diagram.Value target.1,
      ((alternative observed) candidate).toReal *
        siteRelevantProbeScore semantics base owner replacement target view
          observed candidate
  let targetAt := fun observed =>
    ∑ candidate : diagram.Value target.1,
      ((targetRule observed) candidate).toReal *
        siteRelevantProbeScore semantics base owner replacement target view
          observed candidate
  have hrest :
      ∑ observed ∈
          (Finset.univ : Finset
            (MAIDReplacementInvariantUtility.FullContext target)).erase
              context,
          alternativeAt observed =
        ∑ observed ∈
          (Finset.univ : Finset
            (MAIDReplacementInvariantUtility.FullContext target)).erase
              context,
          targetAt observed := by
    apply Finset.sum_congr rfl
    intro observed hobserved
    have hne : observed ≠ context := Finset.ne_of_mem_erase hobserved
    simp [alternativeAt, targetAt, alternative, replaceContextWithPure, hne]
  have haltSplit := Finset.add_sum_erase
    (Finset.univ : Finset
      (MAIDReplacementInvariantUtility.FullContext target))
    alternativeAt (Finset.mem_univ context)
  have htargetSplit := Finset.add_sum_erase
    (Finset.univ : Finset
      (MAIDReplacementInvariantUtility.FullContext target))
    targetAt (Finset.mem_univ context)
  have hlocal : alternativeAt context ≤ targetAt context := by
    have hglobal : (∑ observed, alternativeAt observed) ≤
        ∑ observed, targetAt observed := by
      simpa [alternativeAt, targetAt] using hrelevant
    rw [← haltSplit, ← htargetSplit, hrest] at hglobal
    linarith
  have halternative : alternativeAt context =
      siteRelevantProbeScore semantics base owner replacement target view
        context action := by
    unfold alternativeAt alternative replaceContextWithPure
    simp only [ite_true, PMF.pure_apply, apply_ite,
      ENNReal.toReal_one, ENNReal.toReal_zero,
      ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ action]
    simp
  rw [halternative] at hlocal
  exact hlocal

private theorem siteRelevantProbeScore_eq_zero_of_contextMass_eq_zero
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (view : UtilityView semantics)
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (context : MAIDReplacementInvariantUtility.FullContext target)
    (action : diagram.Value target.1)
    (hzero : siteContextMass topological semantics base owner replacement
      target context = 0) :
    siteRelevantProbeScore semantics base owner replacement target view
      context action = 0 := by
  classical
  unfold siteRelevantProbeScore
  apply Finset.sum_eq_zero
  intro term hterm
  unfold siteTermFullScore
  apply Finset.sum_eq_zero
  intro termValue _
  let law := siteReplacementLaw semantics base owner replacement target
    (constantSiteRule target action)
  have hfull :
      (law.map (fun assignment =>
        (Assignment.restrict diagram assignment
          (diagram.observedParents target.1), assignment target.1)))
          (context, action) = 0 := by
    have hreal :
        ((law.map (fun assignment =>
          (Assignment.restrict diagram assignment
            (diagram.observedParents target.1), assignment target.1)))
            (context, action)).toReal = 0 := by
      unfold law
      rw [constantSiteRule_fullAction_prob_eq_contextMass topological semantics
        base owner replacement target context action]
      exact hzero
    rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with hzero | htop
    · exact hzero
    · exact False.elim ((PMF.apply_ne_top _ _) htop)
  have hjoint := joint_mass_eq_zero_of_fullAction_mass_eq_zero_at law
    (fun assignment =>
      (Assignment.restrict diagram assignment
        (diagram.observedParents target.1), assignment target.1))
    (fun assignment => Assignment.restrict diagram assignment
      (view.term term).parents)
    (context, action) termValue hfull
  have hprojection :
      (fun assignment : Assignment diagram =>
        ((Assignment.restrict diagram assignment
            (diagram.observedParents target.1), assignment target.1),
          Assignment.restrict diagram assignment
            (view.term term).parents)) =
        siteFullActionTermProjection view target term := by
    funext assignment
    rfl
  rw [← hprojection, hjoint]
  simp

private theorem siteRelevantProbeScore_le_after_source_change
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    [Fintype (Assignment diagram)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (view : UtilityView semantics)
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (source target : DecisionSite diagram owner) (hneq : source ≠ target)
    (sourceRule : MAIDReplacementInvariantUtility.FullContext source →
      PMF (diagram.Value source.1))
    (hnot : ¬ MAIDPruningFixpointGraph.UtilityView.SReachable view source
      target)
    (hmixed : FullyMixedAt replacement source)
    [Fintype (MAIDReplacementInvariantUtility.FullContext target)]
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (targetRule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1))
    (hoptimal : IsOptimalSiteRule semantics base owner replacement target
      targetRule)
    (context : MAIDReplacementInvariantUtility.FullContext target)
    (action : diagram.Value target.1) :
    siteRelevantProbeScore semantics base owner
        (replaceSiteRule replacement source sourceRule) target view context
          action ≤
      ∑ candidate : diagram.Value target.1,
        ((targetRule context) candidate).toReal *
          siteRelevantProbeScore semantics base owner
            (replaceSiteRule replacement source sourceRule) target view context
              candidate := by
  classical
  let changed := replaceSiteRule replacement source sourceRule
  let changedMass := siteContextMass topological semantics base owner changed
    target context
  let baselineMass := siteContextMass topological semantics base owner
    replacement target context
  by_cases hchangedZero : changedMass = 0
  · have hscoreZero : ∀ candidate : diagram.Value target.1,
        siteRelevantProbeScore semantics base owner changed target view context
          candidate = 0 := by
      intro candidate
      exact siteRelevantProbeScore_eq_zero_of_contextMass_eq_zero topological
        semantics view base owner changed target context candidate hchangedZero
    dsimp only [changed] at hscoreZero ⊢
    simp_rw [hscoreZero]
    simp
  · have hchangedNonneg : 0 ≤ changedMass :=
      ENNReal.toReal_nonneg
    have hchangedPos : 0 < changedMass :=
      lt_of_le_of_ne hchangedNonneg (Ne.symm hchangedZero)
    have hbaselinePos : 0 < baselineMass :=
      siteContextMass_pos_of_changed topological semantics view base owner
        replacement source target hneq sourceRule hmixed context hchangedPos
    have hbaselineRank := siteRelevantProbeScore_le_of_optimal topological
      semantics view base owner replacement target targetRule hoptimal context
        action
    have hcrossAction := siteRelevantProbeScore_cross_product topological view
      base owner replacement source target hneq sourceRule hnot context action
    have hcrossExpected :
        (∑ candidate : diagram.Value target.1,
            ((targetRule context) candidate).toReal *
              siteRelevantProbeScore semantics base owner replacement target
                view context candidate) * changedMass =
          baselineMass *
            (∑ candidate : diagram.Value target.1,
              ((targetRule context) candidate).toReal *
                siteRelevantProbeScore semantics base owner changed target view
                  context candidate) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro candidate _
      have hcross := siteRelevantProbeScore_cross_product topological view
        base owner replacement source target hneq sourceRule hnot context
          candidate
      dsimp only [changedMass, baselineMass, changed] at hcross ⊢
      calc
        (((targetRule context) candidate).toReal *
            siteRelevantProbeScore semantics base owner replacement target view
              context candidate) *
            siteContextMass topological semantics base owner
              (replaceSiteRule replacement source sourceRule) target context =
          ((targetRule context) candidate).toReal *
            (siteRelevantProbeScore semantics base owner replacement target
                view context candidate *
              siteContextMass topological semantics base owner
                (replaceSiteRule replacement source sourceRule) target
                  context) := by ring
        _ = ((targetRule context) candidate).toReal *
            (siteContextMass topological semantics base owner replacement
                target context *
              siteRelevantProbeScore semantics base owner
                (replaceSiteRule replacement source sourceRule) target view
                  context candidate) := by rw [hcross]
        _ = siteContextMass topological semantics base owner replacement
              target context *
            (((targetRule context) candidate).toReal *
              siteRelevantProbeScore semantics base owner
                (replaceSiteRule replacement source sourceRule) target view
                  context candidate) := by ring
    have hscaled := mul_le_mul_of_nonneg_right hbaselineRank hchangedNonneg
    rw [hcrossAction, hcrossExpected] at hscaled
    nlinarith

/-! ## One-source optimality transport -/

theorem IsOptimalSiteRule.transport_replaceSiteRule_of_not_sReachable
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    [Fintype (Assignment diagram)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (view : UtilityView semantics)
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (source target : DecisionSite diagram owner) (hneq : source ≠ target)
    (sourceRule : MAIDReplacementInvariantUtility.FullContext source →
      PMF (diagram.Value source.1))
    (hnot : ¬ MAIDPruningFixpointGraph.UtilityView.SReachable view source
      target)
    (hmixed : FullyMixedAt replacement source)
    [Fintype (MAIDReplacementInvariantUtility.FullContext target)]
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (targetRule : MAIDReplacementInvariantUtility.FullContext target →
      PMF (diagram.Value target.1))
    (hoptimal : IsOptimalSiteRule semantics base owner replacement target
      targetRule) :
    IsOptimalSiteRule semantics base owner
      (replaceSiteRule replacement source sourceRule) target targetRule := by
  classical
  intro alternative
  let changed := replaceSiteRule replacement source sourceRule
  have hrelevant :
      siteRelevantValue semantics base owner changed target view alternative ≤
        siteRelevantValue semantics base owner changed target view
          targetRule := by
    rw [siteRelevantValue_eq_sum_probe topological semantics base owner
      changed target view alternative]
    rw [siteRelevantValue_eq_sum_probe topological semantics base owner
      changed target view targetRule]
    apply Finset.sum_le_sum
    intro context _
    let targetExpected :=
      ∑ action : diagram.Value target.1,
        ((targetRule context) action).toReal *
          siteRelevantProbeScore semantics base owner changed target view
            context action
    calc
      ∑ action : diagram.Value target.1,
          ((alternative context) action).toReal *
            siteRelevantProbeScore semantics base owner changed target view
              context action ≤
        ∑ action : diagram.Value target.1,
          ((alternative context) action).toReal * targetExpected := by
            apply Finset.sum_le_sum
            intro action _
            apply mul_le_mul_of_nonneg_left
            · exact siteRelevantProbeScore_le_after_source_change
                topological semantics view base owner replacement source target
                  hneq sourceRule hnot hmixed targetRule hoptimal context action
            · exact ENNReal.toReal_nonneg
      _ = targetExpected := by
        have hmass :
            ∑ action : diagram.Value target.1,
              ((alternative context) action).toReal = 1 := by
          have hconstant := expect_eq_sum (alternative context)
            (fun _ => (1 : ℝ)) (payoffIntegrable_of_finite _ _)
          rw [expect_constant] at hconstant
          simpa only [mul_one] using hconstant.symm
        rw [← Finset.sum_mul, hmass, one_mul]
      _ = ∑ action : diagram.Value target.1,
          ((targetRule context) action).toReal *
            siteRelevantProbeScore semantics base owner changed target view
              context action := rfl
  have hnonrelevant := siteNonrelevantValue_eq topological view base owner
    changed target alternative targetRule
  have hcomparison :
      siteRuleExpectedUtility semantics base owner changed target alternative
          (payoffIntegrable_of_finite _ _) ≤
        siteRuleExpectedUtility semantics base owner changed target targetRule
          (payoffIntegrable_of_finite _ _) := by
    rw [siteRuleExpectedUtility_eq_relevant_add_nonrelevant semantics base owner
      changed target view alternative]
    rw [siteRuleExpectedUtility_eq_relevant_add_nonrelevant semantics base owner
      changed target view targetRule]
    rw [hnonrelevant]
    exact add_le_add_left hrelevant _
  exact (euPreference_iff _ owner _ _
    (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)).mpr hcomparison

end GameTheory.Experimental.PostArchitecture.MAIDStrategicNonreachability
