/-
# EXP-107: site-local optimality score bridges

This module contains the division-free algebra surrounding a site-local
replacement.  It does not assert optimality transport or deviation coverage:
those statements still require the graphical nonreachability argument.
-/

import GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality
import GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDSiteOptimalityScores

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
open GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
open GameTheory.Experimental.PostArchitecture.MAIDSiteReplacementContext
open GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation.UtilityView

universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-! ## Policy surgery algebra -/

theorem replaceSiteRule_commute_of_ne [DecidableEq Node]
    {owner : Player} (policy : OwnerPolicy diagram owner)
    (first second : DecisionSite diagram owner)
    (hneq : first ≠ second)
    (firstRule : Config diagram (diagram.observedParents first.1) →
      FinDist (diagram.Value first.1))
    (secondRule : Config diagram (diagram.observedParents second.1) →
      FinDist (diagram.Value second.1)) :
    replaceSiteRule (replaceSiteRule policy first firstRule)
        second secondRule =
      replaceSiteRule (replaceSiteRule policy second secondRule)
        first firstRule := by
  funext site
  by_cases hfirst : site = first
  · subst site
    rw [replaceSiteRule_of_ne _ second first secondRule hneq]
    rw [replaceSiteRule_same]
    rw [replaceSiteRule_same]
  · by_cases hsecond : site = second
    · subst site
      rw [replaceSiteRule_same]
      rw [replaceSiteRule_of_ne _ first second firstRule hneq.symm]
      rw [replaceSiteRule_same]
    · simp [replaceSiteRule, hfirst, hsecond]

theorem replaceSiteRule_congr_of_eq_off_target [DecidableEq Node]
    {owner : Player} (first second : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1))
    (hagree : ∀ site, site ≠ target → first site = second site) :
    replaceSiteRule first target rule =
      replaceSiteRule second target rule := by
  funext site
  by_cases hsite : site = target
  · subst site
    simp
  · simp [replaceSiteRule, hsite, hagree site hsite]

theorem siteReplacementLaw_congr_of_eq_off_target
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (first second : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1))
    (hagree : ∀ site, site ≠ target → first site = second site) :
    siteReplacementLaw semantics base owner first target rule =
      siteReplacementLaw semantics base owner second target rule := by
  unfold siteReplacementLaw
  rw [replaceSiteRule_congr_of_eq_off_target first second target rule hagree]

/-! ## Shared target-context marginals -/

theorem siteReplacementLaw_context_marginal_eq
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    (siteReplacementLaw semantics base owner replacement target rule).map
        (fun assignment => Assignment.restrict diagram assignment
          (diagram.observedParents target.1)) =
      (siteReplacementContextLawAt topological semantics base owner replacement
        target).contextLaw := by
  have hjoint := (siteReplacementContextLawAt topological semantics base owner
    replacement target).contextAction_eq rule
  calc
    (siteReplacementLaw semantics base owner replacement target rule).map
        (fun assignment => Assignment.restrict diagram assignment
          (diagram.observedParents target.1)) =
      FinDist.map Prod.fst
        ((siteReplacementLaw semantics base owner replacement target rule).map
          (fun assignment =>
            (Assignment.restrict diagram assignment
              (diagram.observedParents target.1), assignment target.1))) := by
          rw [FinDist.map_comp]
          rfl
    _ = (siteReplacementContextLawAt topological semantics base owner
        replacement target).contextLaw.bind fun context =>
          FinDist.map Prod.fst ((rule context).map fun action =>
            (context, action)) := by
          rw [hjoint, FinDist.map_bind]
    _ = (siteReplacementContextLawAt topological semantics base owner
        replacement target).contextLaw := by
          simp only [FinDist.map_comp]
          calc
            (siteReplacementContextLawAt topological semantics base owner
                replacement target).contextLaw.bind (fun context =>
                  FinDist.map (Prod.fst ∘ fun action => (context, action))
                    (rule context)) =
                (siteReplacementContextLawAt topological semantics base owner
                  replacement target).contextLaw.bind (fun context =>
                    FinDist.pure context) := by
              apply FinDist.bind_congr
              intro context _
              simp [Function.comp_def, FinDist.map_const]
            _ = (siteReplacementContextLawAt topological semantics base owner
                replacement target).contextLaw := FinDist.bind_pure _

/-! ## Zero-mass support facts -/

theorem joint_mass_eq_zero_of_fullAction_mass_eq_zero_at
    {Ω : Type*} {Context Action Term : Type*}
    [DecidableEq (Context × Action)]
    [DecidableEq ((Context × Action) × Term)]
    (law : FinDist Ω) (fullAction : Ω → Context × Action)
    (term : Ω → Term) (fullValue : Context × Action)
    (termValue : Term)
    (hzero : (law.map fullAction).prob fullValue = 0) :
    (law.map fun omega => (fullAction omega, term omega)).prob
        (fullValue, termValue) = 0 := by
  apply FinDist.prob_eq_zero_iff.mpr
  intro hjoint
  rw [FinDist.support_map] at hjoint
  obtain ⟨omega, homega, hvalue⟩ := hjoint
  apply (FinDist.prob_eq_zero_iff.mp hzero)
  rw [FinDist.support_map]
  exact ⟨omega, homega, congrArg Prod.fst hvalue⟩

/-! ## Unnormalised term scores -/

def siteRuleTermScore
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : FullContext target → FinDist (diagram.Value target.1))
    (view : UtilityView semantics) (term : view.UtilitySite owner)
    [Fintype (TermConfig view term)]
    (context : FullContext target)
    (action : diagram.Value target.1) : ℝ :=
  ∑ termValue : TermConfig view term,
    ((siteReplacementLaw semantics base owner replacement target rule).map
      (fun assignment =>
        (Assignment.restrict diagram assignment
            (diagram.observedParents target.1),
          (assignment target.1,
            Assignment.restrict diagram assignment
              (view.term term).parents)))).prob
      (context, (action, termValue)) * (view.term term).payoff termValue

def siteRuleContextActionScore
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : FullContext target → FinDist (diagram.Value target.1))
    (view : UtilityView semantics)
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (context : FullContext target)
    (action : diagram.Value target.1) : ℝ :=
  ∑ term : view.UtilitySite owner,
    siteRuleTermScore semantics base owner replacement target rule view term
      context action

theorem expect_eq_sum_joint_fibres
    {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y]
    (law : FinDist Ω) (first : Ω → X) (second : Ω → Y)
    (value : Y → ℝ) :
    law.expect (fun omega => value (second omega)) =
      ∑ firstValue : X, ∑ secondValue : Y,
        (law.map (fun omega => (first omega, second omega))).prob
          (firstValue, secondValue) * value secondValue := by
  calc
    law.expect (fun omega => value (second omega)) =
        (law.map (fun omega => (first omega, second omega))).expect
          (fun pair => value pair.2) := by
      rw [FinDist.expect_map]
    _ = ∑ pair : X × Y,
        (law.map (fun omega => (first omega, second omega))).prob pair *
          value pair.2 := FinDist.expect_eq_sum _ _
    _ = ∑ firstValue : X, ∑ secondValue : Y,
        (law.map (fun omega => (first omega, second omega))).prob
          (firstValue, secondValue) * value secondValue := by
      rw [← Finset.univ_product_univ, Finset.sum_product]

theorem expect_eq_sum_joint_triples
    {Ω X Y Z : Type*} [Fintype Ω] [Fintype X] [Fintype Y] [Fintype Z]
    (law : FinDist Ω) (first : Ω → X) (second : Ω → Y)
    (third : Ω → Z) (value : Z → ℝ) :
    law.expect (fun omega => value (third omega)) =
      ∑ firstValue : X, ∑ secondValue : Y, ∑ thirdValue : Z,
        (law.map (fun omega =>
          (first omega, (second omega, third omega)))).prob
            (firstValue, (secondValue, thirdValue)) * value thirdValue := by
  calc
    law.expect (fun omega => value (third omega)) =
        ∑ firstValue : X, ∑ pair : Y × Z,
          (law.map (fun omega =>
            (first omega, (second omega, third omega)))).prob
              (firstValue, pair) * value pair.2 := by
      simpa using
        (expect_eq_sum_joint_fibres law first
          (fun omega => (second omega, third omega))
          (fun pair => value pair.2))
    _ = ∑ firstValue : X, ∑ secondValue : Y, ∑ thirdValue : Z,
        (law.map (fun omega =>
          (first omega, (second omega, third omega)))).prob
            (firstValue, (secondValue, thirdValue)) * value thirdValue := by
      apply Finset.sum_congr rfl
      intro firstValue _
      rw [← Finset.univ_product_univ, Finset.sum_product]

theorem siteRuleExpectedUtility_eq_sum_context_action
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    [Fintype (Assignment diagram)]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    [Fintype (FullContext target)]
    (view : UtilityView semantics)
    [∀ term : view.UtilitySite owner, Fintype (TermConfig view term)]
    (rule : FullContext target → FinDist (diagram.Value target.1)) :
    siteRuleExpectedUtility semantics base owner replacement target rule =
      ∑ context : FullContext target, ∑ action : diagram.Value target.1,
        siteRuleContextActionScore semantics base owner replacement target
          rule view context action := by
  unfold siteRuleExpectedUtility expectedUtility
  calc
    (siteReplacementLaw semantics base owner replacement target rule).expect
        (fun assignment => semantics.utility owner assignment) =
      (siteReplacementLaw semantics base owner replacement target rule).expect
        (fun assignment => ∑ term : view.UtilitySite owner,
          (view.term term).payoff
            (Assignment.restrict diagram assignment
              (view.term term).parents)) := by
      apply FinDist.expect_congr
      intro assignment _
      simpa [UtilityView.term, UtilityTerm.value] using
        view.utility_eq_sum owner assignment
    _ = ∑ term : view.UtilitySite owner,
        (siteReplacementLaw semantics base owner replacement target rule).expect
          (fun assignment =>
            (view.term term).payoff
              (Assignment.restrict diagram assignment
                (view.term term).parents)) :=
      (FinDist.expect_sum_comm _ _).symm
    _ = ∑ term : view.UtilitySite owner,
        ∑ fullValue : FullContext target,
          ∑ action : diagram.Value target.1,
            siteRuleTermScore semantics base owner replacement target rule
              view term fullValue action := by
      apply Finset.sum_congr rfl
      intro term _
      simpa [FullContext, siteRuleTermScore] using
        (expect_eq_sum_joint_triples
          (siteReplacementLaw semantics base owner replacement target rule)
          (fun assignment =>
            Assignment.restrict diagram assignment
              (diagram.observedParents target.1))
          (fun assignment => assignment target.1)
          (fun assignment =>
            Assignment.restrict diagram assignment (view.term term).parents)
          (view.term term).payoff)
    _ = _ := by
      simp only [siteRuleContextActionScore]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro context _
      rw [Finset.sum_comm]

end GameTheory.Experimental.PostArchitecture.MAIDSiteOptimalityScores
