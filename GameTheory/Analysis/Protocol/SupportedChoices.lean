/-
# Supported choices under sequential rationality

Where the continuation runner factors a law installed at a decision site, a
continuation value is affine in the site's current law. Sequential rationality
therefore makes every choice the assessment plays with positive probability
optimal against every whole continuation policy, with play after the site
unchanged, and a choice that is uniformly worse than some policy on every
history of the site gets no probability. The uniform bound ranges over all
histories of the site, including those the belief ignores, so no positive
belief on each history is needed.
-/

import GameTheory.Analysis.Protocol.CounterfactualRegret

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type*} [DecidableEq ι] {E : ExecutionProtocol ι} {M : InformationModel E}
  {who : ι} [DecidableEq (M.InfoState who)]

/-- Installing a law at the site factors the belief-averaged outcome into a
choice draw followed by the corresponding committed continuation. -/
theorem BehavioralAssessment.continuationContextWith_outcome_withLaw
    (assessment : M.BehavioralAssessment) (run : M.ContinuationRunner)
    (site : M.InformationSite who) (hfactor : M.RunnerFactorsAt run who site)
    (payoff : E.History → ℝ) (policy : M.BehavioralPolicy who)
    (law : PMF (M.Choice who site.1)) :
    (assessment.continuationContextWith run site payoff).outcome (policy.withLaw site.1 law) =
      law.bind fun choice =>
        (assessment.continuationContextWith run site payoff).outcome
          (policy.commit site.1 choice) := by
  change (assessment.belief who site).bind (fun history =>
      run (Profile.update (sig := M.behavioralSignature) assessment.strategy who
        (policy.withLaw site.1 law)) history.1) =
    law.bind fun choice => (assessment.belief who site).bind fun history =>
      run (Profile.update (sig := M.behavioralSignature) assessment.strategy who
        (policy.commit site.1 choice)) history.1
  simp_rw [hfactor assessment.strategy policy law]
  exact PMF.bind_comm _ _ _

/-- **Supported choices attain the site's value.** A sequentially rational
assessment is indifferent among the choices it plays with positive probability:
committing to any of them leaves the continuation value unchanged. -/
theorem BehavioralAssessment.supported_choice_value
    (assessment : M.BehavioralAssessment) (run : M.ContinuationRunner)
    (site : M.InformationSite who) (hfactor : M.RunnerFactorsAt run who site)
    (payoff : E.History → ℝ)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContextWith run site payoff))
    (integrable : ∀ policy,
      (assessment.continuationContextWith run site payoff).IntegrableAt policy)
    (choice : M.Choice who site.1)
    (supported : choice ∈ (assessment.strategy who site.1).support) :
    (assessment.continuationContextWith run site payoff).value
        ((assessment.strategy who).commit site.1 choice) =
      (assessment.continuationContextWith run site payoff).value
        (assessment.strategy who) := by
  have mixture := assessment.continuationContextWith_outcome_withLaw run site hfactor
    payoff (assessment.strategy who) (assessment.strategy who site.1)
  rw [BehavioralPolicy.withLaw_eq_self] at mixture
  have optimal := (Context.isLocallyOptimal_iff_of_integrable (integrable _)
    fun alternative _ => integrable alternative).mp rational
  have hintegrable := integrable (assessment.strategy who)
  unfold Context.IntegrableAt at hintegrable
  rw [mixture] at hintegrable
  have affine : (assessment.continuationContextWith run site payoff).value
      (assessment.strategy who) = expect (assessment.strategy who site.1) fun choice =>
        (assessment.continuationContextWith run site payoff).value
          ((assessment.strategy who).commit site.1 choice) := by
    unfold Context.value
    rw [mixture]
    exact expect_bind_tower _ _ _ hintegrable
  exact expect_eq_const_of_le_on_support (assessment.strategy who site.1) _ _
    (payoffIntegrable_bind_conditionalExpectation _ _ _ hintegrable)
    (fun alternative _ => optimal ((assessment.strategy who).commit site.1 alternative)
      (Set.mem_univ _)) affine.symm choice supported

/-- **Supported choices are optimal** against whole continuation-policy
deviations, not merely against other current choices. -/
theorem BehavioralAssessment.supported_choice_optimal
    (assessment : M.BehavioralAssessment) (run : M.ContinuationRunner)
    (site : M.InformationSite who) (hfactor : M.RunnerFactorsAt run who site)
    (payoff : E.History → ℝ)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContextWith run site payoff))
    (integrable : ∀ policy,
      (assessment.continuationContextWith run site payoff).IntegrableAt policy)
    (choice : M.Choice who site.1)
    (supported : choice ∈ (assessment.strategy who site.1).support)
    (alternative : M.BehavioralPolicy who) :
    (assessment.continuationContextWith run site payoff).value alternative ≤
      (assessment.continuationContextWith run site payoff).value
        ((assessment.strategy who).commit site.1 choice) := by
  rw [assessment.supported_choice_value run site hfactor payoff rational integrable choice
    supported]
  exact (Context.isLocallyOptimal_iff_of_integrable
      (integrable _) fun alternative _ => integrable alternative).mp rational
    alternative (Set.mem_univ _)

/-- **Uniformly worse choices get no probability.** If committing to a choice
scores at most `upper` from every history of the site while some policy scores
at least `lower > upper` from every history, a sequentially rational assessment
never plays that choice. The bounds range over all histories of the site, so
this also controls histories the belief assigns probability zero. -/
theorem BehavioralAssessment.not_supported_choice_of_uniform_gap
    (assessment : M.BehavioralAssessment) (run : M.ContinuationRunner)
    (site : M.InformationSite who) (hfactor : M.RunnerFactorsAt run who site)
    (payoff : E.History → ℝ)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContextWith run site payoff))
    (integrable : ∀ policy,
      (assessment.continuationContextWith run site payoff).IntegrableAt policy)
    (choice : M.Choice who site.1) (alternative : M.BehavioralPolicy who)
    (upper lower : ℝ) (gap : upper < lower)
    (bad : ∀ history : M.InformationHistory who site.1,
      expect (run (Profile.update (sig := M.behavioralSignature) assessment.strategy who
        ((assessment.strategy who).commit site.1 choice)) history.1) payoff ≤ upper)
    (good : ∀ history : M.InformationHistory who site.1,
      lower ≤ expect (run (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who alternative) history.1) payoff) :
    choice ∉ (assessment.strategy who site.1).support := by
  intro supported
  have best := assessment.supported_choice_optimal run site hfactor payoff rational
    integrable choice supported alternative
  have badIntegrable := integrable ((assessment.strategy who).commit site.1 choice)
  have goodIntegrable := integrable alternative
  simp only [BehavioralAssessment.continuationContextWith_value] at best
  have badBound := expect_bind_le_constant_on_support _ _ _ upper badIntegrable
    (fun history _ => bad history)
  have goodBound := expect_bind_ge_constant_on_support _ _ _ lower goodIntegrable
    (fun history _ => good history)
  exact (not_le_of_gt gap) (goodBound.trans (best.trans badBound))

end GameTheory.Protocol.InformationModel
