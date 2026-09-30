/-
# Beliefs and laws at retained sites

Vanishing perturbations of retained laws force the limit to play the embedded
laws at every retained decision site. If approximants of the larger protocol
dominate the embedded play of the smaller one by factors whose loss is
negligible relative to a retained site's mass, their Bayes beliefs at that site
converge to the prescribed belief, even when the site is unreached in the limit.
The belief statement uses a common decision depth at the retained site only.
-/

import GameTheory.Analysis.Protocol.BeliefTransport
import GameTheory.Analysis.Protocol.RestrictionDomination

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type*} [Fintype ι] {E T : ExecutionProtocol ι}
  {M : InformationModel E} {N : InformationModel T}

private theorem information_event_meets (assessment : M.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (who : ι) (site : M.InformationSite who)
    (depth : ℕ) (clock : InformationSite.CommonDepth M site depth) :
    ∃ history ∈ {history : E.History | M.infoOf who history.trace = site.1},
      history ∈ (M.runBehavioral assessment.strategy depth).support := by
  let witness := site.2.choose
  refine ⟨witness.1, witness.2, ?_⟩
  have positive := M.historyReachWeight_pos_of_fullSupport assessment.strategy mixed witness.1
  rw [historyReachWeight, clock witness] at positive
  exact (PMF.apply_pos_iff _ _).mp positive

private theorem bayes_belief_eq (assessment : M.BehavioralAssessment)
    (who : ι) (site : M.InformationSite who)
    (antichain : site.IsHistoryAntichain)
    (positive : 0 < M.informationMass assessment.strategy who site)
    (bayes : BehavioralAssessment.IsBayesConsistentAt M assessment who site antichain positive) :
    assessment.belief who site = M.bayesBelief assessment.strategy who site antichain positive := by
  ext history
  rw [M.bayesBelief_apply]
  exact bayes history

namespace ActionRestriction

variable (restriction : M.ActionRestriction N)

omit [Fintype ι] in
/-- Convergent laws of the smaller protocol and vanishing retained trembles
force the limit of the larger protocol to extend the limit profile. -/
theorem extendsProfile_of_perturbs_converges
    (reference : (i : ι) → N.BehavioralPolicy i)
    (sourceSequence : ℕ → M.BehavioralAssessment) (source : M.BehavioralAssessment)
    (targetSequence : ℕ → N.BehavioralAssessment) (target : N.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (targetConverges : BehavioralAssessmentConvergesPointwise targetSequence target)
    (epsilon : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ epsilon n) (small : ∀ n, epsilon n ≤ 1)
    (vanishes : Tendsto epsilon atTop (nhds 0))
    (perturbs : ∀ n, restriction.PerturbsProfile (sourceSequence n).strategy reference
      (targetSequence n).strategy (epsilon n) (nonnegative n) (small n)) :
    restriction.ExtendsProfile source.strategy target.strategy := by
  intro who site
  have sourceLaws := (sourceConverges.strategy who site).map (restriction.choice who site.1)
  have targetLaws := targetConverges.strategy who (restriction.site who site)
  apply pmf_ext_toReal
  intro action
  have convergence := (vanishes.mul_const
    (((reference who (restriction.information who site.1)) action).toReal)).add
      (((tendsto_const_nhds (x := (1 : ℝ))).sub vanishes).mul (sourceLaws.toReal action))
  simp only [zero_mul, sub_zero, one_mul, zero_add] at convergence
  have same (n : ℕ) :
      (((targetSequence n).strategy who (restriction.information who site.1)) action).toReal =
      epsilon n * (((reference who (restriction.information who site.1)) action).toReal) +
        (1 - epsilon n) *
          ((((sourceSequence n).strategy who site.1).map
            (restriction.choice who site.1)) action).toReal := by
    rw [perturbs n who site, mix_apply_toReal]
  exact tendsto_nhds_unique (targetLaws.toReal action)
    (convergence.congr' (Eventually.of_forall fun n => (same n).symm))

omit [Fintype ι] in
/-- Embedded histories reflect the entire retained information event,
including histories that a particular profile does not reach. -/
theorem information_event_preimage (who : ι) (site : M.InformationSite who) :
    restriction.history ⁻¹'
        {history | N.infoOf who history.trace = (restriction.site who site).1} =
      {history | M.infoOf who history.trace = site.1} := by
  ext history
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, restriction.observed,
    site_val, Function.Embedding.apply_eq_iff_eq]

/-- **Retained beliefs converge.** Beliefs at a retained site follow from a
bound on execution laws, not from an assumed translation of beliefs. The
dominating factors' loss must be negligible relative to the retained site's
mass in the smaller protocol. -/
theorem retained_beliefs_converge
    (sourceSequence : ℕ → M.BehavioralAssessment)
    (targetSequence : ℕ → N.BehavioralAssessment)
    (sourceAntichain : M.DecisionInformationAntichain)
    (targetAntichain : N.DecisionInformationAntichain)
    (sourceMixed : ∀ n, (sourceSequence n).IsFullyMixed)
    (targetMixed : ∀ n, (targetSequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent M
      (sourceSequence n) sourceAntichain)
    (targetBayes : ∀ n, BehavioralAssessment.IsBayesConsistent N
      (targetSequence n) targetAntichain)
    (who : ι) (site : M.InformationSite who) (depth : ℕ)
    (clock : InformationSite.CommonDepth N (restriction.site who site) depth)
    (factor : ℕ → ℝ) (positive : ∀ n, 0 < factor n)
    (atMostOne : ∀ n, factor n ≤ 1)
    (lower : ∀ n history,
      factor n * (((M.runBehavioral (sourceSequence n).strategy depth).map
        restriction.history) history).toReal ≤
          ((N.runBehavioral (targetSequence n).strategy depth) history).toReal)
    (negligible : Tendsto (fun n => (1 - factor n) /
      (factor n * (M.informationMass (sourceSequence n).strategy who site).toReal)) atTop
        (nhds 0))
    (limit : PMF (M.InformationHistory who site.1))
    (converges : PMFConvergesPointwise (fun n => (sourceSequence n).belief who site) limit) :
    PMFConvergesPointwise
      (fun n => (targetSequence n).belief who (restriction.site who site))
      (limit.map (restriction.informationHistory who site)) := by
  classical
  let sourceEvent : Set E.History := {history | M.infoOf who history.trace = site.1}
  let targetEvent : Set T.History :=
    {history | N.infoOf who history.trace = (restriction.site who site).1}
  have sourceClock := restriction.source_commonDepth who site depth clock
  have sourceMeet (n : ℕ) := information_event_meets (sourceSequence n)
    (sourceMixed n) who site depth sourceClock
  have targetMeet (n : ℕ) := information_event_meets (targetSequence n)
    (targetMixed n) who (restriction.site who site) depth clock
  have preimage : restriction.history ⁻¹' targetEvent = sourceEvent :=
    restriction.information_event_preimage who site
  have encodedMeet (n : ℕ) : ∃ history ∈ targetEvent,
      history ∈ ((M.runBehavioral (sourceSequence n).strategy depth).map
        restriction.history).support := by
    obtain ⟨history, observed, supported⟩ := sourceMeet n
    refine ⟨restriction.history history, ?_, ?_⟩
    · change history ∈ restriction.history ⁻¹' targetEvent
      rwa [preimage]
    · rw [PMF.support_map]
      exact ⟨history, supported, rfl⟩
  have sourcePositive (n : ℕ) :=
    M.informationMass_pos_of_fullSupport _ (sourceMixed n) who site
  have targetPositive (n : ℕ) :=
    N.informationMass_pos_of_fullSupport _ (targetMixed n) who (restriction.site who site)
  have sourceConditioned (n : ℕ) :
      (((M.runBehavioral (sourceSequence n).strategy depth).map restriction.history).filter
        targetEvent (encodedMeet n)) =
      ((sourceSequence n).belief who site).map
        (fun history => restriction.history history.1) := by
    rw [← map_filter_embedding
      (M.runBehavioral (sourceSequence n).strategy depth) restriction.history
      sourceEvent targetEvent (fun history => by
        change history ∈ restriction.history ⁻¹' targetEvent ↔ history ∈ sourceEvent
        rw [preimage]) (sourceMeet n) (encodedMeet n)]
    rw [← M.bayesBelief_map_eq_filter (sourceSequence n).strategy who site depth
      sourceClock (sourceAntichain who site) (sourcePositive n) (sourceMeet n),
      ← bayes_belief_eq (sourceSequence n) who site (sourceAntichain who site)
        (sourcePositive n) (sourceBayes n who site (sourcePositive n)), PMF.map_comp]
    rfl
  have targetConditioned (n : ℕ) :
      (N.runBehavioral (targetSequence n).strategy depth).filter targetEvent (targetMeet n) =
        ((targetSequence n).belief who (restriction.site who site)).map Subtype.val := by
    rw [← N.bayesBelief_map_eq_filter (targetSequence n).strategy who
      (restriction.site who site) depth clock (targetAntichain who (restriction.site who site))
      (targetPositive n) (targetMeet n),
      ← bayes_belief_eq (targetSequence n) who (restriction.site who site)
        (targetAntichain who (restriction.site who site)) (targetPositive n)
        (targetBayes n who (restriction.site who site) (targetPositive n))]
  have mass (n : ℕ) :
      (((M.runBehavioral (sourceSequence n).strategy depth).map
        restriction.history).toOuterMeasure targetEvent).toReal =
        (M.informationMass (sourceSequence n).strategy who site).toReal := by
    rw [PMF.toOuterMeasure_map_apply, preimage,
      M.informationMass_eq_fixedDepth_toOuterMeasure (sourceSequence n).strategy who site
        depth sourceClock]
  have conditioned := conditional_domination_converges
    (fun n => (M.runBehavioral (sourceSequence n).strategy depth).map restriction.history)
    (fun n => N.runBehavioral (targetSequence n).strategy depth) targetEvent encodedMeet targetMeet
    factor positive atMostOne lower (by simpa only [mass] using negligible)
    (limit.map (fun history => restriction.history history.1)) (by
      simpa only [sourceConditioned] using
        converges.map (fun history => restriction.history history.1))
  rw [show (fun history : M.InformationHistory who site.1 =>
      restriction.history history.1) =
      Subtype.val ∘ restriction.informationHistory who site by rfl,
    ← PMF.map_comp] at conditioned
  intro history
  have point := conditioned history.1
  simpa only [targetConditioned, pmf_map_apply_of_injective _ Subtype.val_injective]
    using point

end ActionRestriction

end GameTheory.Protocol.InformationModel
