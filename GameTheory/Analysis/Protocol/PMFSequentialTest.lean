/-
# Sequential consistency on an infinite action carrier

The general execution and Bayes fixture lives below Analysis. Its geometric
strategy supplies an infinite-support witness for perturbation-limit
consistency. Vanishing geometric trembles also approximate a pure strategy on
the countable action menu; bounded continuation values converge while holding
the infinite-support belief fixed.
-/

import GameTheory.Analysis.Protocol.Sequential
import GameTheory.Analysis.Protocol.BehavioralBayes
import GameTheory.Analysis.Protocol.BehavioralConvergence
import GameTheory.Experimental.PostArchitecture.PMFSequentialGate
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace GameTheory.Tests.PMFSequential

open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration
open GameTheory.Experimental.PMFSequentialGate
open Filter

private theorem geometricBehavioralProfile_fullSupport_everywhere :
    ∀ i info (choice : canonicalInformation.Choice i info),
      choice ∈ (behavioralProfile geometric i info).support := by
  intro i info choice
  cases i
  cases info with
  | none =>
      rcases choice with ⟨choice, hlegal⟩
      cases choice with
      | none => simp [behavioralProfile, localBehavioral]
      | some action => simp at hlegal
  | some info =>
      cases info
      rcases choice with ⟨choice, hlegal⟩
      cases choice with
      | none => simp at hlegal
      | some action =>
          simpa [behavioralProfile, localBehavioral] using
            (show action ∈ geometric.support from
            (geometric_positive action).ne')

theorem geometricBehavioralProfile_fullSupport :
    ∀ i (site : canonicalInformation.InformationSite i)
      (choice : canonicalInformation.Choice i site.1),
      choice ∈ (behavioralProfile geometric i site.1).support := by
  intro i site choice
  exact geometricBehavioralProfile_fullSupport_everywhere i site.1 choice

def geometricFullSupportAssessment :
    canonicalInformation.BehavioralAssessment :=
  canonicalInformation.bayesAssessment (behavioralProfile geometric)
    geometricBehavioralProfile_fullSupport canonicalDecisionInformationAntichain

theorem geometricFullSupportAssessment_infinite_bayes_fiber :
    (geometricFullSupportAssessment.belief () decisionSite).support.Infinite := by
  have heq :
      geometricFullSupportAssessment.belief () decisionSite =
        decisionBayesBelief geometric := by
    apply PMF.ext
    intro history
    simp [geometricFullSupportAssessment,
      GameTheory.Protocol.InformationModel.bayesAssessment,
      GameTheory.Protocol.InformationModel.bayesBelief_apply,
      decisionBayesBelief_ratio]
  rw [heq]
  exact geometricDecisionAssessment_has_infinite_bayes_fiber

theorem geometricDecisionAssessment_fullyMixed :
    (decisionBayesAssessment geometric).IsFullyMixed := by
  intro i site choice
  exact geometricBehavioralProfile_fullSupport i site choice

theorem geometricDecisionAssessment_sequentiallyConsistent :
    (decisionBayesAssessment geometric).IsSequentiallyConsistent
      canonicalDecisionInformationAntichain := by
  exact ⟨fun _ => decisionBayesAssessment geometric,
    fun _ => ⟨geometricDecisionAssessment_fullyMixed,
      geometricDecisionAssessment_bayesConsistent⟩,
    InformationModel.behavioralAssessmentConvergesPointwise_const _⟩

private def trembleWeight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private theorem trembleWeight_pos (n : ℕ) : 0 < trembleWeight n := by
  unfold trembleWeight
  positivity

private theorem trembleWeight_le_one (n : ℕ) : trembleWeight n ≤ 1 := by
  unfold trembleWeight
  apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Positive geometric trembles around a pure action on the infinite menu. -/
def trembleLaw (n : ℕ) : PMF ℕ :=
  mix (trembleWeight n) (trembleWeight_pos n).le (trembleWeight_le_one n)
    geometric (PMF.pure 0)

theorem trembleLaw_fullSupport (n action : ℕ) :
    action ∈ (trembleLaw n).support :=
  mem_support_mix_left _ _ _ (trembleWeight_pos n)
    (show action ∈ geometric.support from (geometric_positive action).ne')

theorem trembleLaw_infiniteSupport (n : ℕ) : (trembleLaw n).support.Infinite := by
  have heq : (trembleLaw n).support = Set.univ :=
    Set.eq_univ_iff_forall.mpr (trembleLaw_fullSupport n)
  rw [heq]
  exact Set.infinite_univ

theorem trembleLaw_convergesPointwise :
    PMFConvergesPointwise trembleLaw (PMF.pure 0) :=
  pmfConvergesPointwise_mix_zero trembleWeight
    (fun n => (trembleWeight_pos n).le) trembleWeight_le_one
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) _ _

theorem tremblingBehavioral_convergesPointwise
    (i : PUnit) (info : canonicalInformation.InfoState i) :
    PMFConvergesPointwise (fun n => behavioralProfile (trembleLaw n) i info)
      (behavioralProfile (PMF.pure 0) i info) := by
  cases i
  cases info with
  | none => exact pmfConvergesPointwise_const _
  | some info =>
      cases info
      exact trembleLaw_convergesPointwise.map _

/-- These assessments vary the strategy and keep the existing infinite
Bayes belief fixed. Their definition makes no Bayes-consistency claim. -/
def fixedBeliefAssessment (law : PMF ℕ) : canonicalInformation.BehavioralAssessment where
  strategy := behavioralProfile law
  belief := (decisionBayesAssessment geometric).belief

theorem fixedBeliefAssessment_infinite_belief (law : PMF ℕ) :
    ((fixedBeliefAssessment law).belief () decisionSite).support.Infinite := by
  simp only [fixedBeliefAssessment, decisionBayesAssessment_atSite]
  exact geometricDecisionAssessment_has_infinite_bayes_fiber

theorem tremblingAssessment_fullyMixed (n : ℕ) :
    (fixedBeliefAssessment (trembleLaw n)).IsFullyMixed := by
  have hfull : ∀ i info (choice : canonicalInformation.Choice i info),
      choice ∈ (behavioralProfile (trembleLaw n) i info).support := by
    intro i info choice
    cases i
    cases info with
    | none =>
        rcases choice with ⟨choice, hlegal⟩
        cases choice with
        | none => simp [behavioralProfile, localBehavioral]
        | some action => simp at hlegal
    | some info =>
        cases info
        rcases choice with ⟨choice, hlegal⟩
        cases choice with
        | none => simp at hlegal
        | some action =>
            simp only [behavioralProfile, localBehavioral, PMF.mem_support_map_iff]
            exact ⟨action, trembleLaw_fullSupport n action, rfl⟩
  exact fun i site choice => hfull i site.1 choice

theorem pureAssessment_not_fullyMixed :
    ¬ (fixedBeliefAssessment (PMF.pure 0)).IsFullyMixed := by
  intro hfull
  let choice : canonicalInformation.Choice () decisionSite.1 :=
    ⟨some 1, by simp [decisionSite_info]⟩
  have h := hfull () decisionSite choice
  simp only [fixedBeliefAssessment, behavioralProfile, decisionSite_info,
    localBehavioral, PMF.pure_map, PMF.support_pure] at h
  have hvalues := congrArg Subtype.val h
  simp [choice] at hvalues

/-- Actual continuation values converge with both infinite actions and an
infinite belief fiber, under a bound on the chosen history payoff. -/
theorem trembling_continuation_value_tendsto
    (payoff : canonicalDecision.History → ℝ) (fuel : ℕ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ history, |payoff history| ≤ C) :
    Tendsto (fun n =>
      ((fixedBeliefAssessment (trembleLaw n)).continuationContext
        decisionSite payoff fuel).value (localBehavioral (trembleLaw n))
        (payoffIntegrable_of_bounded _ payoff hbound)) atTop
      (nhds (((fixedBeliefAssessment (PMF.pure 0)).continuationContext
        decisionSite payoff fuel).value (localBehavioral (PMF.pure 0))
        (payoffIntegrable_of_bounded _ payoff hbound))) := by
  exact canonicalInformation.continuationContext_value_tendsto_of_bounded
    (sequence := fun n => fixedBeliefAssessment (trembleLaw n))
    (target := fixedBeliefAssessment (PMF.pure 0))
    tremblingBehavioral_convergesPointwise () decisionSite
    (pmfConvergesPointwise_const _)
    (alternative := fun n => localBehavioral (trembleLaw n))
    (replacement := localBehavioral (PMF.pure 0))
    (tremblingBehavioral_convergesPointwise ())
    payoff fuel C hC hbound

end GameTheory.Tests.PMFSequential
