/-
# Fully mixed assessments with optimal perturbed local choices

A positive uniform tremble turns every residual local lottery at a decision
site into a fully supported lottery. Bayes beliefs then depend continuously on
the residual profile. A simultaneous local-score fixed point over the decision
sites supplies an assessment whose local choices are optimal among lotteries
with that same tremble. Only finitely many histories are needed: decision sites
and their menus are then finite, while information values that no history
reaches keep a fallback choice.

This is a local-deviation theorem. Whole continuation-policy optimality requires
a separate perfect-recall argument.
-/

import GameTheory.Analysis.LocalChoiceFixedPoint
import GameTheory.Analysis.Protocol.BehavioralBayes
import GameTheory.Analysis.Protocol.BehavioralContinuity
import GameTheory.Protocol.BehavioralMixture
import GameTheory.Protocol.BehavioralTerminal
import GameTheory.Protocol.FiniteHorizon
import GameTheory.Protocol.FiniteInformation
import GameTheory.Math.Probability.ExpectationMixture
import GameTheory.Math.Probability.Uniform

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
    (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- The local laws obtained by mixing a fixed uniform tremble with an
arbitrary residual law. This is the feasible set for perturbed local choices. -/
def uniformTrembleLaws (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (i : ι) (info : M.InfoState i)
    [Finite (M.Choice i info)] [Nonempty (M.Choice i info)] :
    Set (PMF (M.Choice i info)) :=
  {law | ∃ residual, law = mix ε h0 h1
    (@PMF.uniformOfFintype _ (Fintype.ofFinite _) _) residual}

private theorem exists_uniformTremble_locallyOptimal_bayesAssessment_truncated
    [Fintype ι] [DecidableEq ι] [Finite E.History]
    [∀ i, DecidableEq (M.InfoState i)]
    (fallback : (i : ι) → M.Policy i)
    (hactsOnce : M.ActsOnceWhereItMatters)
    (hantichain : M.DecisionInformationAntichain)
    (ε : ℝ) (hε : 0 < ε) (h1 : ε ≤ 1)
    (payoff : ι → E.History → ℝ) (fuel : ℕ) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.IsFullyMixed ∧
      BehavioralAssessment.IsBayesConsistent M assessment hantichain ∧
      (∀ i (site : M.InformationSite i),
        assessment.strategy i site.1 ∈ M.uniformTrembleLaws ε hε.le h1 i site.1) ∧
      ∀ i (site : M.InformationSite i) (law : PMF (M.Choice i site.1)),
        law ∈ M.uniformTrembleLaws ε hε.le h1 i site.1 →
        (assessment.truncatedContinuationContext site (payoff i) (fuel + 1)).IntegrableAt
            ((assessment.strategy i).withLaw site.1 law) ∧
          (assessment.truncatedContinuationContext site (payoff i) (fuel + 1)).IntegrableAt
              (assessment.strategy i) ∧
            (assessment.truncatedContinuationContext site (payoff i) (fuel + 1)).value
                ((assessment.strategy i).withLaw site.1 law) ≤
              (assessment.truncatedContinuationContext site (payoff i) (fuel + 1)).value
                (assessment.strategy i) := by
  classical
  let _ : ∀ i (site : M.InformationSite i), Fintype (M.InformationHistory i site.1) :=
    fun _ _ => Fintype.ofFinite _
  let Coordinate := (i : ι) × M.InformationSite i
  let Action (c : Coordinate) := M.Choice c.1 c.2.1
  let _ : Fintype Coordinate := Fintype.ofFinite _
  let _ : ∀ i (site : M.InformationSite i), Fintype (M.Choice i site.1) :=
    fun _ _ => Fintype.ofFinite _
  let _ : ∀ c : Coordinate, Fintype (Action c) := fun c => Fintype.ofFinite (M.Choice c.1 c.2.1)
  let uniform (i : ι) (site : M.InformationSite i) : PMF (M.Choice i site.1) :=
    @PMF.uniformOfFintype _ (Fintype.ofFinite _) _
  let Domain := Set.pi Set.univ fun c : Coordinate => simplexWeights (Action c)
  let residual (x : Domain) (i : ι) (site : M.InformationSite i) : PMF (M.Choice i site.1) :=
    PMF.ofSimplex (x.property ⟨i, site⟩ (Set.mem_univ _))
  let profile (x : Domain) (i : ι) : M.BehavioralPolicy i := fun info =>
    if hsite : M.IsDecisionInfo i info then
      mix ε hε.le h1 (uniform i ⟨info, hsite⟩) (residual x i ⟨info, hsite⟩)
    else PMF.pure (fallback i info)
  have hprofile_site (x : Domain) (i : ι) (site : M.InformationSite i) :
      profile x i site.1 = mix ε hε.le h1 (uniform i site) (residual x i site) :=
    dite_eq_left site.2
  have hprofile_full (x : Domain) (i : ι) (site : M.InformationSite i) :
      ∀ choice, choice ∈ (profile x i site.1).support := by
    intro choice
    rw [hprofile_site]
    exact mem_support_mix_left ε hε.le h1 hε
      (@PMF.mem_support_uniformOfFintype _ (Fintype.ofFinite _) _ choice)
  let assessment (x : Domain) := M.bayesAssessment (profile x) (hprofile_full x) hantichain
  have hprofile (i : ι) (info : M.InfoState i) (choice : M.Choice i info) :
      Continuous fun x : Domain => ((profile x i info choice).toReal) := by
    by_cases hsite : M.IsDecisionInfo i info
    · obtain ⟨site, rfl⟩ : ∃ site : M.InformationSite i, site.1 = info :=
        ⟨⟨info, hsite⟩, rfl⟩
      have hformula (x : Domain) :
          (profile x i site.1 choice).toReal =
            ε * (uniform i site choice).toReal + (1 - ε) * x.val ⟨i, site⟩ choice := by
        rw [hprofile_site x i site, mix_apply, ENNReal.toReal_add]
        · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le,
            ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - ε),
            show ((residual x i site) choice).toReal = x.val ⟨i, site⟩ choice from
              congrFun (PMF.ofSimplex_toReal _) choice]
        · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)
        · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)
      have coordinate_continuous :
          Continuous (fun x : Domain => x.val ⟨i, site⟩ choice) :=
        (continuous_apply choice).comp
          ((continuous_apply (⟨i, site⟩ : Coordinate)).comp continuous_subtype_val)
      rw [show (fun x : Domain => (profile x i site.1 choice).toReal) =
          fun x => ε * (uniform i site choice).toReal + (1 - ε) * x.val ⟨i, site⟩ choice by
        funext x
        exact hformula x]
      exact (continuous_const.mul continuous_const).add
        (coordinate_continuous.const_mul (1 - ε))
    · have hconst (x : Domain) : profile x i info = PMF.pure (fallback i info) :=
        dite_eq_right hsite
      simp only [hconst]
      exact continuous_const
  have hbelief (i : ι) (site : M.InformationSite i)
      (history : M.InformationHistory i site.1) :
      Continuous fun x : Domain => ((assessment x).belief i site history).toReal :=
    M.continuous_bayesBelief_prob ExecutionProtocol.FiniteTransitions.of_finite_history
      profile hprofile i site (hantichain i site)
      (fun x => M.informationMass_pos_of_fullSupport (profile x) (hprofile_full x) i site)
      history
  have hintegrable (x : Domain) (i : ι) (site : M.InformationSite i)
      (alternative : M.BehavioralPolicy i) :
      ((assessment x).truncatedContinuationContext site (payoff i) (fuel + 1)).IntegrableAt
        alternative := by
    exact payoffIntegrable_of_finite _ _
  let scoreValue (x : Domain) (i : ι) (site : M.InformationSite i)
      (alternative : M.BehavioralPolicy i) : ℝ :=
    ((assessment x).truncatedContinuationContext site (payoff i) (fuel + 1)).value
      alternative
  let score (x : Domain) (c : Coordinate) (choice : Action c) : ℝ :=
    scoreValue x c.1 c.2 ((profile x c.1).commit c.2.1 choice)
  have hscore (c : Coordinate) (choice : Action c) :
      Continuous fun x : Domain => score x c choice := by
    apply M.continuous_truncatedContinuationContext_value assessment hprofile c.1 c.2
      (hbelief c.1 c.2) (fun x => (profile x c.1).commit c.2.1 choice)
    intro info action
    by_cases hinfo : info = c.2.1
    · subst info
      simp only [BehavioralPolicy.commit_self]
      exact continuous_const
    · simp only [BehavioralPolicy.commit_of_ne _ _ _ hinfo]
      exact hprofile c.1 info action
  obtain ⟨x, hx⟩ := exists_localChoice_fixedPoint score hscore
  refine ⟨assessment x, hprofile_full x,
    M.bayesAssessment_isBayesConsistent (profile x) (hprofile_full x) hantichain,
    (fun i site => ⟨residual x i site, hprofile_site x i site⟩), ?_⟩
  intro i site law hlaw
  obtain ⟨alternative, rfl⟩ := hlaw
  let context := (assessment x).truncatedContinuationContext site (payoff i) (fuel + 1)
  let altLaw := mix ε hε.le h1 (uniform i site) alternative
  let baseLaw := profile x i site.1
  let value := fun choice => scoreValue x i site ((profile x i).commit site.1 choice)
  let hAlt := hintegrable x i site ((profile x i).withLaw site.1 altLaw)
  let hBase := hintegrable x i site (profile x i)
  have hbestValue : expect alternative value ≤ expect (residual x i site) value :=
    hx ⟨i, site⟩ alternative
  have hAltValue := BehavioralAssessment.truncatedContinuationContext_withLaw_eq_expect
    M hactsOnce (assessment x) site (profile x i) altLaw (payoff i) fuel hAlt
    value (by intro choice _; rfl)
  have hBaseValue := BehavioralAssessment.truncatedContinuationContext_withLaw_eq_expect
    M hactsOnce (assessment x) site (profile x i) baseLaw (payoff i) fuel
    (hintegrable x i site ((profile x i).withLaw site.1 baseLaw))
    value (by intro choice _; rfl)
  have hbaseLaw : (profile x i).withLaw site.1 baseLaw = profile x i :=
    BehavioralPolicy.withLaw_eq_self _ _
  have huniform : PayoffIntegrable (uniform i site) value :=
    payoffIntegrable_of_finite _ _
  have haltMix := expect_mix ε hε.le h1 (uniform i site) alternative value huniform
    (payoffIntegrable_of_finite _ _)
  have hbaseMix := expect_mix ε hε.le h1 (uniform i site) (residual x i site) value
    huniform (payoffIntegrable_of_finite _ _)
  obtain ⟨-, hAltValue⟩ := hAltValue
  obtain ⟨-, hBaseValue⟩ := hBaseValue
  refine ⟨?_, ?_, ?_⟩
  · simpa only [assessment, M.bayesAssessment_strategy] using hAlt
  · simpa only [assessment, M.bayesAssessment_strategy] using hBase
  · simpa only [assessment, M.bayesAssessment_strategy] using (show
      context.value ((profile x i).withLaw site.1 altLaw) ≤
        context.value (profile x i) from by
      rw [hAltValue]
      have hbaseValue' : context.value (profile x i) = expect baseLaw value := by
        simpa only [hbaseLaw] using hBaseValue
      rw [hbaseValue', show baseLaw = _ from hprofile_site x i site, haltMix, hbaseMix]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hbestValue (sub_nonneg.mpr h1)))

/-- Every positive uniform perturbation has a fully mixed Bayes assessment
whose local law at every decision site is optimal against every feasible
perturbed replacement. The conclusion is for local replacements only, scored by
whole terminal continuations. Finitely many histories suffice; the fallback
supplies a choice at information values that no history reaches. -/
theorem exists_uniformTremble_locallyOptimal_bayesAssessment
    [Fintype ι] [DecidableEq ι] [Finite E.History]
    [∀ i, DecidableEq (M.InfoState i)]
    (fallback : (i : ι) → M.Policy i)
    (hactsOnce : M.ActsOnceWhereItMatters)
    (hantichain : M.DecisionInformationAntichain)
    (ε : ℝ) (hε : 0 < ε) (h1 : ε ≤ 1)
    (payoff : ι → E.History → ℝ) (certificate : E.WellFoundedHistories) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.IsFullyMixed ∧
      BehavioralAssessment.IsBayesConsistent M assessment hantichain ∧
      (∀ i (site : M.InformationSite i),
        assessment.strategy i site.1 ∈ M.uniformTrembleLaws ε hε.le h1 i site.1) ∧
      ∀ i (site : M.InformationSite i) (law : PMF (M.Choice i site.1)),
        law ∈ M.uniformTrembleLaws ε hε.le h1 i site.1 →
        (assessment.continuationContext certificate site (payoff i)).IntegrableAt
            ((assessment.strategy i).withLaw site.1 law) ∧
          (assessment.continuationContext certificate site (payoff i)).IntegrableAt
              (assessment.strategy i) ∧
            (assessment.continuationContext certificate site (payoff i)).value
                ((assessment.strategy i).withLaw site.1 law) ≤
              (assessment.continuationContext certificate site (payoff i)).value
                (assessment.strategy i) := by
  let _ := Fintype.ofFinite E.History
  obtain ⟨bound, hpositive, hbound⟩ := E.exists_pos_boundedHorizon
  obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
  obtain ⟨assessment, hfull, hbayes, hfeasible, hlocal⟩ :=
    exists_uniformTremble_locallyOptimal_bayesAssessment_truncated M fallback hactsOnce
      hantichain ε hε h1 payoff fuel
  refine ⟨assessment, hfull, hbayes, hfeasible, ?_⟩
  simp only [assessment.continuationContext_eq_truncated_of_bounded certificate hbound]
  exact hlocal

end GameTheory.Protocol.InformationModel
