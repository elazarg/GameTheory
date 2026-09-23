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
import GameTheory.Analysis.Protocol.CounterfactualRegret

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
    Set (FinDist (M.Choice i info)) :=
  {law | ∃ residual, law = FinDist.mix ε h0 h1 FinDist.uniformOfFintype residual}

/-- Belief averaging preserves local-law affinity when decision information
is not revisited. Terminal histories contribute a constant continuation payoff. -/
theorem BehavioralAssessment.continuationContext_withLaw_eq_expect
    [Fintype ι] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (assessment : M.BehavioralAssessment)
    {i : ι} [DecidableEq (M.InfoState i)] (site : M.InformationSite i)
    (policy : M.BehavioralPolicy i) (law : FinDist (M.Choice i site.1))
    (payoff : E.History → ℝ) (fuel : ℕ) :
    (assessment.continuationContext site payoff (fuel + 1)).value
        (policy.withLaw site.1 law) =
      law.expect fun choice =>
        (assessment.continuationContext site payoff (fuel + 1)).value
          (policy.commit site.1 choice) := by
  simp_rw [BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  show (assessment.belief i site).expect (fun history =>
      M.behavioralContinuationValue assessment.strategy i
        (policy.withLaw site.1 law) payoff (fuel + 1) history.1) =
    law.expect (fun choice => (assessment.belief i site).expect (fun history =>
      M.behavioralContinuationValue assessment.strategy i
        (policy.commit site.1 choice) payoff (fuel + 1) history.1))
  have hhistory (history : M.InformationHistory i site.1) :
      M.behavioralContinuationValue assessment.strategy i
          (policy.withLaw site.1 law) payoff (fuel + 1) history.1 =
        law.expect fun choice => M.behavioralContinuationValue assessment.strategy i
          (policy.commit site.1 choice) payoff (fuel + 1) history.1 := by
    by_cases hterm : E.terminal history.1.state
    · simp only [behavioralContinuationValue, M.runBehavioralFrom_of_terminal _ _ hterm,
        FinDist.expect_pure, FinDist.expect_const]
    · exact M.behavioralContinuationValue_withLaw_eq_expect hactsOnce
        assessment.strategy i site policy law history hterm payoff fuel
  simp_rw [hhistory]
  exact FinDist.expect_comm _ _ _

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
      ∀ i (site : M.InformationSite i) (law : FinDist (M.Choice i site.1)),
        law ∈ M.uniformTrembleLaws ε hε.le h1 i site.1 →
        (assessment.continuationContext site (payoff i) (fuel + 1)).value
            ((assessment.strategy i).withLaw site.1 law) ≤
          (assessment.continuationContext site (payoff i) (fuel + 1)).value
            (assessment.strategy i) := by
  classical
  let Coordinate := (i : ι) × M.InfoState i
  let Action (c : Coordinate) := M.Choice c.1 c.2
  let Domain := Set.pi Set.univ fun c : Coordinate => simplexWeights (Action c)
  let residual (x : Domain) (i : ι) (info : M.InfoState i) : FinDist (M.Choice i info) :=
    FinDist.ofSimplex (x.property ⟨i, info⟩ (Set.mem_univ _))
  let profile (x : Domain) (i : ι) : M.BehavioralPolicy i := fun info =>
    FinDist.mix ε hε.le h1 FinDist.uniformOfFintype (residual x i info)
  have hprofile_full (x : Domain) (i : ι) (site : M.InformationSite i) :
      (profile x i site.1).FullSupport := by
    intro choice
    exact FinDist.mem_support_mix_left ε hε.le h1 hε
      (FinDist.mem_support_uniformOfFintype choice)
  let assessment (x : Domain) := M.bayesAssessment (profile x) (hprofile_full x) hantichain
  have hprofile (i : ι) (info : M.InfoState i) (choice : M.Choice i info) :
      Continuous fun x : Domain => (profile x i info).prob choice := by
    simp only [profile, residual, FinDist.prob_mix, FinDist.prob_ofSimplex]
    have coordinate_continuous :
        Continuous (fun x : Domain => x.val ⟨i, info⟩ choice) :=
      (continuous_apply choice).comp
        ((continuous_apply (⟨i, info⟩ : Coordinate)).comp continuous_subtype_val)
    exact continuous_const.add (coordinate_continuous.const_mul (1 - ε))
  have hbelief (i : ι) (site : M.InformationSite i)
      (history : M.InformationHistory i site.1) :
      Continuous fun x : Domain => ((assessment x).belief i site).prob history :=
    M.continuous_bayesBelief_prob profile hprofile i site (hantichain i site)
      (fun x => M.informationMass_pos_of_fullSupport (profile x) (hprofile_full x) i site)
      history
  let score (x : Domain) (c : Coordinate) (choice : Action c) : ℝ :=
    if hsite : ∃ history : M.InformationHistory c.1 c.2,
        ¬ E.terminal history.1.state ∧ ∃ action : E.Action c.1,
          some action ∈ M.menu c.1 c.2 then
      ((assessment x).continuationContext ⟨c.2, hsite⟩ (payoff c.1) (fuel + 1)).value
        ((profile x c.1).commit c.2 choice)
    else 0
  have hscore_site (x : Domain) (i : ι) (site : M.InformationSite i)
      (choice : M.Choice i site.1) :
      score x ⟨i, site.1⟩ choice =
        ((assessment x).continuationContext site (payoff i) (fuel + 1)).value
          ((profile x i).commit site.1 choice) := by
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
  show ((assessment x).continuationContext site (payoff i) (fuel + 1)).value
      ((profile x i).withLaw site.1
        (FinDist.mix ε hε.le h1 FinDist.uniformOfFintype alternative)) ≤
    ((assessment x).continuationContext site (payoff i) (fuel + 1)).value (profile x i)
  have hbest : alternative.expect (score x ⟨i, site.1⟩) ≤
      (residual x i site.1).expect (score x ⟨i, site.1⟩) := hx ⟨i, site.1⟩ alternative
  have hscore_eq := funext (hscore_site x i site)
  rw [hscore_eq] at hbest
  rw [BehavioralAssessment.continuationContext_withLaw_eq_expect M hactsOnce
    (assessment x) site]
  calc
    _ ≤ (profile x i site.1).expect (fun choice =>
        ((assessment x).continuationContext site (payoff i) (fuel + 1)).value
          ((profile x i).commit site.1 choice)) := by
      show (FinDist.mix ε hε.le h1 FinDist.uniformOfFintype alternative).expect _ ≤
        (FinDist.mix ε hε.le h1 FinDist.uniformOfFintype (residual x i site.1)).expect _
      simp only [FinDist.expect_mix]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hbest (sub_nonneg.mpr h1))
    _ = _ := by
      simpa only [BehavioralPolicy.withLaw_eq_self] using
        (BehavioralAssessment.continuationContext_withLaw_eq_expect M hactsOnce
          (assessment x) site (profile x i) (profile x i site.1) (payoff i) fuel).symm

end GameTheory.Protocol.InformationModel
