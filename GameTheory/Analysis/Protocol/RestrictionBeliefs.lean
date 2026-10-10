/-
# Beliefs and laws at retained sites

Vanishing perturbations of retained laws force the limit to play the embedded
laws at every retained decision site. If approximants of the larger protocol
dominate the embedded play of the smaller one by factors whose loss is
negligible relative to a retained site's mass, their Bayes beliefs at that site
converge to the prescribed belief, even when the site is unreached in the limit.
Terminal passage through the site supplies conditioning without a common decision depth.
-/

import GameTheory.Analysis.Protocol.BeliefTransport
import GameTheory.Analysis.Protocol.RestrictionDomination

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type*} {E T : ExecutionProtocol ι}
  {M : InformationModel E} {N : InformationModel T}
variable [E.FiniteMovers] [T.FiniteMovers]

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

omit [E.FiniteMovers] [T.FiniteMovers] in
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

omit [E.FiniteMovers] [T.FiniteMovers] in
/-- Embedded histories reflect the entire retained information event,
including histories that a particular profile does not reach. -/
theorem information_event_preimage (who : ι) (site : M.InformationSite who) :
    restriction.history ⁻¹'
        {history | N.infoOf who history.trace = (restriction.site who site).1} =
      {history | M.infoOf who history.trace = site.1} := by
  ext history
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, restriction.observed,
    site_val, Function.Embedding.apply_eq_iff_eq]

section TerminalPassage

/-- **Retained beliefs converge without a common depth.** Beliefs at a
retained site follow from a bound on terminal laws. The dominating factors'
loss must be negligible relative to the retained site's mass in the smaller
protocol. The histories of the site may lie at different depths. -/
theorem retained_beliefs_converge
    (sourceCertificate : E.WellFoundedHistories) (targetCertificate : T.WellFoundedHistories)
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
    (who : ι) (site : M.InformationSite who)
    (factor : ℕ → ℝ) (positive : ∀ n, 0 < factor n)
    (atMostOne : ∀ n, factor n ≤ 1)
    (lower : ∀ n final, factor n *
      (((M.runBehavioralTerminalFrom sourceCertificate (sourceSequence n).strategy
        E.initHistory).map restriction.history) final).toReal ≤
          ((N.runBehavioralTerminalFrom targetCertificate (targetSequence n).strategy
            T.initHistory) final).toReal)
    (negligible : Tendsto (fun n => (1 - factor n) /
      (factor n * (M.informationMass (sourceSequence n).strategy who site).toReal)) atTop
        (nhds 0))
    (limit : PMF (M.InformationHistory who site.1))
    (converges : PMFConvergesPointwise (fun n => (sourceSequence n).belief who site) limit) :
    PMFConvergesPointwise
      (fun n => (targetSequence n).belief who (restriction.site who site))
      (limit.map (restriction.informationHistory who site)) := by
  classical
  let sourceLaw (n : ℕ) := (M.runBehavioralTerminalFrom sourceCertificate
    (sourceSequence n).strategy E.initHistory).map restriction.history
  let targetLaw (n : ℕ) :=
    N.runBehavioralTerminalFrom targetCertificate (targetSequence n).strategy T.initHistory
  let passage : Set T.History := {final | ∃ history, N.infoOf who history.trace =
    (restriction.site who site).1 ∧ T.HistoryReaches history final}
  have sourceMass (n : ℕ) :=
    M.informationMass_pos_of_fullSupport _ (sourceMixed n) who site
  have targetMass (n : ℕ) :=
    N.informationMass_pos_of_fullSupport _ (targetMixed n) who (restriction.site who site)
  have sourcePassage (n : ℕ) : (sourceLaw n).toOuterMeasure passage =
      M.informationMass (sourceSequence n).strategy who site := by
    rw [PMF.toOuterMeasure_map_apply, restriction.passage_preimage,
      M.informationMass_eq_passage sourceCertificate _ who site (sourceAntichain who site)]
  have targetPassage (n : ℕ) : (targetLaw n).toOuterMeasure passage =
      N.informationMass (targetSequence n).strategy who (restriction.site who site) :=
    (N.informationMass_eq_passage targetCertificate _ who _ (targetAntichain who _)).symm
  have sourcePositive (n : ℕ) : 0 < ((sourceLaw n).toOuterMeasure passage).toReal := by
    rw [sourcePassage]
    exact ENNReal.toReal_pos (sourceMass n).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
      (M.informationMass_le_one _ who site (sourceAntichain who site)))
  rw [pmfConvergesPointwise_iff_toReal]
  intro history
  let cone : Set T.History := {final | T.HistoryReaches history.1 final}
  have inside : cone ⊆ passage := fun final reach => ⟨history.1, history.2, reach⟩
  have targetRatio (n : ℕ) :
      ((targetLaw n).toOuterMeasure cone).toReal / ((targetLaw n).toOuterMeasure passage).toReal =
        ((targetSequence n).belief who (restriction.site who site) history).toReal := by
    rw [bayes_belief_eq (targetSequence n) who _ (targetAntichain who _) (targetMass n)
      (targetBayes n who _ (targetMass n)), N.bayesBelief_apply_eq_passage targetCertificate,
      ENNReal.toReal_div]
  have sourceLimit : Tendsto (fun n => ((sourceLaw n).toOuterMeasure cone).toReal /
      ((sourceLaw n).toOuterMeasure passage).toReal) atTop
        (nhds ((limit.map (restriction.informationHistory who site)) history).toReal) := by
    by_cases embedded : history ∈ Set.range (restriction.informationHistory who site)
    · obtain ⟨original, rfl⟩ := embedded
      rw [pmf_map_apply_of_injective _ (restriction.informationHistory who site).injective]
      refine (converges.toReal original).congr fun n => ?_
      rw [bayes_belief_eq (sourceSequence n) who site (sourceAntichain who site) (sourceMass n)
        (sourceBayes n who site (sourceMass n)), M.bayesBelief_apply_eq_passage sourceCertificate,
        ENNReal.toReal_div, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply,
        restriction.passage_preimage]
      simp only [cone, informationHistory_val, restriction.cone_preimage]
    · have zero : (limit.map (restriction.informationHistory who site)) history = 0 := by
        rw [PMF.apply_eq_zero_iff, PMF.support_map]
        rintro ⟨original, -, same⟩
        exact embedded ⟨original, same⟩
      rw [zero, ENNReal.toReal_zero]
      refine tendsto_const_nhds.congr fun n => ?_
      rw [PMF.toOuterMeasure_map_apply, restriction.cone_preimage_eq_empty who site history
        embedded, MeasureTheory.measure_empty, ENNReal.toReal_zero, zero_div]
  exact (conditional_domination_converges_of_subset sourceLaw targetLaw passage cone inside
    sourcePositive factor positive atMostOne lower
    (by simpa only [sourcePassage] using negligible) _ sourceLimit).congr targetRatio


end TerminalPassage

end ActionRestriction

end GameTheory.Protocol.InformationModel
