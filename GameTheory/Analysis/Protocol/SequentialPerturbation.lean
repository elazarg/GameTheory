/-
# Fully mixed assessments with optimal perturbed local choices

A positive uniform tremble turns every residual local lottery into a fully
supported lottery. Bayes beliefs then depend continuously on the residual
profile. A simultaneous local-score fixed point supplies an assessment whose
local choices are optimal among lotteries with that same tremble.

This is a local-deviation theorem. Whole continuation-policy optimality requires
a separate perfect-recall argument.
-/

import GameTheory.Analysis.LocalChoiceFixedPoint
import GameTheory.Analysis.Protocol.BehavioralBayes
import GameTheory.Analysis.Protocol.BehavioralContinuity
import GameTheory.Protocol.BehavioralMixture
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
    [Fintype (M.Choice i info)] [Nonempty (M.Choice i info)] :
    Set (PMF (M.Choice i info)) :=
  {law | ∃ residual, law = mix ε h0 h1 (PMF.uniformOfFintype _) residual}

/-- Every positive uniform perturbation has a fully mixed Bayes assessment
whose local law is optimal against every feasible perturbed replacement.
The conclusion is for local replacements only; scores use the existing whole
continuation runner with horizon `fuel + 1`. -/
theorem exists_uniformTremble_locallyOptimal_bayesAssessment
    [Fintype ι] [DecidableEq ι]
    [Fintype E.State] [Fintype E.History] [∀ i, Fintype (E.Action i)]
    [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)]
    [∀ i info, Fintype (M.Choice i info)] [∀ i info, Nonempty (M.Choice i info)]
    [∀ i (site : M.InformationSite i), Fintype (M.InformationHistory i site.1)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (hantichain : M.DecisionInformationAntichain)
    (ε : ℝ) (hε : 0 < ε) (h1 : ε ≤ 1)
    (payoff : ι → E.History → ℝ) (fuel : ℕ) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.IsFullyMixed ∧
      BehavioralAssessment.IsBayesConsistent M assessment hantichain ∧
      (∀ i info, assessment.strategy i info ∈ M.uniformTrembleLaws ε hε.le h1 i info) ∧
      ∀ i (site : M.InformationSite i) (law : PMF (M.Choice i site.1)),
        law ∈ M.uniformTrembleLaws ε hε.le h1 i site.1 →
        ∃ halt : (assessment.continuationContext site (payoff i) (fuel + 1)).IntegrableAt
            ((assessment.strategy i).withLaw site.1 law),
          ∃ hbase : (assessment.continuationContext site (payoff i) (fuel + 1)).IntegrableAt
              (assessment.strategy i),
            (assessment.continuationContext site (payoff i) (fuel + 1)).value
                ((assessment.strategy i).withLaw site.1 law) halt ≤
              (assessment.continuationContext site (payoff i) (fuel + 1)).value
                (assessment.strategy i) hbase := by
  classical
  let Coordinate := (i : ι) × M.InfoState i
  let Action (c : Coordinate) := M.Choice c.1 c.2
  let Domain := Set.pi Set.univ fun c : Coordinate => simplexWeights (Action c)
  let residual (x : Domain) (i : ι) (info : M.InfoState i) : PMF (M.Choice i info) :=
    PMF.ofSimplex (x.property ⟨i, info⟩ (Set.mem_univ _))
  let profile (x : Domain) (i : ι) : M.BehavioralPolicy i := fun info =>
    mix ε hε.le h1 (PMF.uniformOfFintype _) (residual x i info)
  have hprofile_full (x : Domain) (i : ι) (site : M.InformationSite i) :
      ∀ choice, choice ∈ (profile x i site.1).support := by
    intro choice
    exact mem_support_mix_left ε hε.le h1 hε
      (PMF.mem_support_uniformOfFintype choice)
  let assessment (x : Domain) := M.bayesAssessment (profile x) (hprofile_full x) hantichain
  have hprofile (i : ι) (info : M.InfoState i) (choice : M.Choice i info) :
      Continuous fun x : Domain => ((profile x i info choice).toReal) := by
    have hformula (x : Domain) :
        (profile x i info choice).toReal =
          ε * (PMF.uniformOfFintype (M.Choice i info) choice).toReal +
            (1 - ε) * x.val ⟨i, info⟩ choice := by
      simp only [profile, mix_apply]
      rw [ENNReal.toReal_add]
      · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - ε)]
        rw [show (PMF.ofSimplex (x.property ⟨i, info⟩ (Set.mem_univ _)) choice).toReal =
          x.val ⟨i, info⟩ choice by
            exact congrFun (PMF.ofSimplex_toReal _) choice]
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)
    have coordinate_continuous :
        Continuous (fun x : Domain => x.val ⟨i, info⟩ choice) :=
      (continuous_apply choice).comp
        ((continuous_apply (⟨i, info⟩ : Coordinate)).comp continuous_subtype_val)
    rw [show (fun x : Domain => (profile x i info choice).toReal) =
        fun x => ε * (PMF.uniformOfFintype (M.Choice i info) choice).toReal +
          (1 - ε) * x.val ⟨i, info⟩ choice by
      funext x
      exact hformula x]
    exact (continuous_const.mul continuous_const).add
      (coordinate_continuous.const_mul (1 - ε))
  have hbelief (i : ι) (site : M.InformationSite i)
      (history : M.InformationHistory i site.1) :
      Continuous fun x : Domain => ((assessment x).belief i site history).toReal :=
    M.continuous_bayesBelief_prob profile hprofile i site (hantichain i site)
      (fun x => M.informationMass_pos_of_fullSupport (profile x) (hprofile_full x) i site)
      history
  have hintegrable (x : Domain) (i : ι) (site : M.InformationSite i)
      (alternative : M.BehavioralPolicy i) :
      ((assessment x).continuationContext site (payoff i) (fuel + 1)).IntegrableAt
        alternative := by
    exact payoffIntegrable_of_finite _ _
  let scoreValue (x : Domain) (i : ι) (site : M.InformationSite i)
      (alternative : M.BehavioralPolicy i) : ℝ :=
    ((assessment x).continuationContext site (payoff i) (fuel + 1)).value
      alternative (hintegrable x i site alternative)
  let score (x : Domain) (c : Coordinate) (choice : Action c) : ℝ :=
    if hsite : ∃ history : M.InformationHistory c.1 c.2,
        ¬ E.terminal history.1.state ∧ ∃ action : E.Action c.1,
          some action ∈ M.menu c.1 c.2 then
      scoreValue x c.1 ⟨c.2, hsite⟩ ((profile x c.1).commit c.2 choice)
    else 0
  have hscore_site (x : Domain) (i : ι) (site : M.InformationSite i)
      (choice : M.Choice i site.1) :
      score x ⟨i, site.1⟩ choice =
        scoreValue x i site ((profile x i).commit site.1 choice) := by
    rcases site with ⟨info, hsite⟩
    simp only [score, dite_eq_left hsite]
  have hscore (c : Coordinate) (choice : Action c) :
      Continuous fun x : Domain => score x c choice := by
    by_cases hsite : ∃ history : M.InformationHistory c.1 c.2,
        ¬ E.terminal history.1.state ∧ ∃ action : E.Action c.1,
          some action ∈ M.menu c.1 c.2
    · simp only [score, dite_eq_left hsite]
      apply M.continuous_continuationContext_value assessment hprofile c.1 ⟨c.2, hsite⟩
        (hbelief c.1 ⟨c.2, hsite⟩) (fun x => (profile x c.1).commit c.2 choice)
      intro info action
      by_cases hinfo : info = c.2
      · subst info
        simp only [BehavioralPolicy.commit_self]
        exact continuous_const
      · simp only [BehavioralPolicy.commit_of_ne _ _ _ hinfo]
        exact hprofile c.1 info action
    · simp only [score, dite_eq_right hsite]
      exact continuous_const
  obtain ⟨x, hx⟩ := exists_localChoice_fixedPoint score hscore
  refine ⟨assessment x, hprofile_full x,
    M.bayesAssessment_isBayesConsistent (profile x) (hprofile_full x) hantichain,
    (fun i info => ⟨residual x i info, rfl⟩), ?_⟩
  intro i site law hlaw
  obtain ⟨alternative, rfl⟩ := hlaw
  let context := (assessment x).continuationContext site (payoff i) (fuel + 1)
  let altLaw := mix ε hε.le h1 (PMF.uniformOfFintype _) alternative
  let baseLaw := profile x i site.1
  let value := fun choice => scoreValue x i site ((profile x i).commit site.1 choice)
  let hAlt := hintegrable x i site ((profile x i).withLaw site.1 altLaw)
  let hBase := hintegrable x i site (profile x i)
  have hbest : expect alternative (score x ⟨i, site.1⟩)
        (payoffIntegrable_of_finite _ _) ≤
      expect (residual x i site.1) (score x ⟨i, site.1⟩)
        (payoffIntegrable_of_finite _ _) := hx ⟨i, site.1⟩ alternative
  have hscore_eq := funext (hscore_site x i site)
  rw [hscore_eq] at hbest
  have hbestValue : expect alternative value (payoffIntegrable_of_finite _ _) ≤
      expect (residual x i site.1) value (payoffIntegrable_of_finite _ _) := by
    simpa only [scoreValue, hscore_site] using hbest
  have hAltValue := BehavioralAssessment.continuationContext_withLaw_eq_expect
    M hactsOnce (assessment x) site (profile x i) altLaw (payoff i) fuel hAlt
    value (by intro choice _; rfl)
  have hBaseValue := BehavioralAssessment.continuationContext_withLaw_eq_expect
    M hactsOnce (assessment x) site (profile x i) baseLaw (payoff i) fuel
    (hintegrable x i site ((profile x i).withLaw site.1 baseLaw))
    value (by intro choice _; rfl)
  have hbaseLaw : (profile x i).withLaw site.1 baseLaw = profile x i :=
    BehavioralPolicy.withLaw_eq_self _ _
  have huniform : PayoffIntegrable (PMF.uniformOfFintype (M.Choice i site.1)) value :=
    payoffIntegrable_of_finite _ _
  have haltMix := expect_mix ε hε.le h1
    (PMF.uniformOfFintype (M.Choice i site.1)) alternative value huniform
    (payoffIntegrable_of_finite _ _)
  have hbaseMix := expect_mix ε hε.le h1
    (PMF.uniformOfFintype (M.Choice i site.1)) (residual x i site.1) value
    huniform (payoffIntegrable_of_finite _ _)
  obtain ⟨hAltExpectation, hAltValue⟩ := hAltValue
  obtain ⟨hBaseExpectation, hBaseValue⟩ := hBaseValue
  refine ⟨?_, ?_, ?_⟩
  · simpa only [assessment, M.bayesAssessment_strategy] using hAlt
  · simpa only [assessment, M.bayesAssessment_strategy] using hBase
  · simpa only [assessment, M.bayesAssessment_strategy] using (show
      context.value ((profile x i).withLaw site.1 altLaw) hAlt ≤
        context.value (profile x i) hBase from by
      rw [hAltValue]
      have hbaseValue' : context.value (profile x i) hBase =
          expect baseLaw value hBaseExpectation := by
        simpa only [hbaseLaw] using hBaseValue
      rw [hbaseValue']
      rw [haltMix, hbaseMix]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hbestValue (sub_nonneg.mpr h1)))

end GameTheory.Protocol.InformationModel
