/-
# Consistent completion beyond an action restriction

A consistent assessment of the smaller protocol extends to a consistent
assessment of the larger one that keeps its behavior and beliefs at retained
sites and is optimal against single-site law changes at every new site. New
sites are completed simultaneously by perturbed agent equilibria, whose
trembles at retained sites vanish faster than the reach of those sites along
the smaller protocol's approximating sequence; execution-law domination then
carries the prescribed beliefs across. Incentives at retained sites are a
separate obligation, not assumed here.
-/

import GameTheory.Analysis.Protocol.AgentCompletion
import GameTheory.Analysis.Protocol.RestrictionBeliefs
import GameTheory.Math.Probability.RelativeTremble

noncomputable section

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E T : ExecutionProtocol ι} {M : InformationModel E} {N : InformationModel T}
  [Fintype T.History] [∀ i, DecidableEq (N.InfoState i)]
  (restriction : M.ActionRestriction N)

/-- **Consistent extension.** Keep a consistent assessment of the smaller
protocol at retained sites and complete all new sites, with common decision
depths required only at retained sites. -/
theorem exists_consistent_extension
    (source : M.BehavioralAssessment) (sourceAntichain : M.DecisionInformationAntichain)
    (sourceConsistent : source.IsSequentiallyConsistent sourceAntichain)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall) (certificate : T.WellFoundedHistories)
    (payoff : ι → T.History → ℝ)
    (depth : ∀ who, M.InformationSite who → ℕ)
    (clock : ∀ who site, InformationSite.CommonDepth N (restriction.site who site)
      (depth who site)) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentiallyConsistent decisionRecall.decisionInformationAntichain ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      ∀ who (site : N.InformationSite who), ¬ restriction.Retained who site.1 →
        ∀ law : PMF (N.Choice who site.1),
          (target.continuationContext certificate site (payoff who)).value
              ((target.strategy who).withLaw site.1 law) ≤
            (target.continuationContext certificate site (payoff who)).value
              (target.strategy who) := by
  classical
  have _ : Finite E.History := Finite.of_injective restriction.history restriction.history.injective
  let _ := Fintype.ofFinite (Σ who, M.InformationSite who)
  obtain ⟨sourceSequence, sourceApproximates, sourceConverges⟩ := sourceConsistent
  let mass (n : ℕ) (entry : Σ who, M.InformationSite who) : ℝ :=
    (M.informationMass (sourceSequence n).strategy entry.1 entry.2).toReal
  have massPositive (n : ℕ) (entry : Σ who, M.InformationSite who) : 0 < mass n entry :=
    ENNReal.toReal_pos
      (M.informationMass_pos_of_fullSupport _ (sourceApproximates n).1 entry.1 entry.2).ne'
      (ne_top_of_le_ne_top ENNReal.one_ne_top
        (M.informationMass_le_one _ entry.1 entry.2 (sourceAntichain entry.1 entry.2)))
  let reach (n : ℕ) : ℝ := ∏ entry, min (1 : ℝ) (mass n entry)
  have reachPositive (n : ℕ) : 0 < reach n :=
    Finset.prod_pos fun entry _ => lt_min zero_lt_one (massPositive n entry)
  have reachBound (n : ℕ) (entry : Σ who, M.InformationSite who) : reach n ≤ mass n entry := by
    have bound := Finset.prod_le_prod_of_subset_of_le_one₀
      (s := {entry}) (t := Finset.univ) (f := fun other => min (1 : ℝ) (mass n other))
      (Finset.subset_univ _) (fun other _ => (lt_min zero_lt_one (massPositive n other)).le)
      (fun other _ _ => min_le_left _ _)
    have single : reach n ≤ min (1 : ℝ) (mass n entry) := by
      simpa only [Finset.prod_singleton] using bound
    exact single.trans (min_le_right _ _)
  let epsilon := relativeTremble reach
  have positive := relativeTremble_pos reach reachPositive
  have small := relativeTremble_lt_one reach
  have vanishes := relativeTremble_tendsto reach reachPositive
  let fallback (who : ι) : N.Policy who := fun info =>
    ((reference.strategy who info).support_nonempty).choose
  let referenceLaws : Profile (N.agentForm fallback certificate).sig.mixed :=
    fun agent => reference.strategy agent.1 agent.2.1
  have playedFull (who : ι) (info : N.InfoState who) (played : info ∈ N.playedInformation who) :
      FullSupport (reference.strategy who info) := by
    unfold playedInformation at played
    obtain ⟨history, member, rfl⟩ := Finset.mem_image.mp played
    have running := (Finset.mem_filter.mp member).2
    by_cases active : T.active history.state who
    · obtain ⟨site, same⟩ := N.exists_informationSite_of_active who history running active
      rw [← same]
      exact referenceMixed who site
    · let _ := N.subsingleton_choice_of_not_active history.trace active
      intro choice
      obtain ⟨witness, supported⟩ :=
        (reference.strategy who (N.infoOf who history.trace)).support_nonempty
      simpa only [Subsingleton.elim witness choice] using supported
  have referenceFull (agent : N.InformationAgent N.playedInformation) :
      FullSupport (referenceLaws agent) :=
    playedFull agent.1 agent.2.1 agent.2.2
  let pinned (n : ℕ) : Profile (N.agentForm fallback certificate).sig.mixed := fun agent =>
    restriction.perturbProfile (sourceSequence n).strategy reference.strategy
      (epsilon n) (positive n).le (small n).le agent.1 agent.2.1
  have pinnedFull (n : ℕ) (agent : N.InformationAgent N.playedInformation) :
      FullSupport (pinned n agent) :=
    restriction.perturbProfile_fullSupport (sourceSequence n).strategy reference.strategy
      (epsilon n) (positive n) (small n).le agent.1 agent.2.1 (referenceFull agent)
  let free : Finset (N.InformationAgent N.playedInformation) :=
    Finset.univ.filter fun agent => ¬ restriction.Retained agent.1 agent.2.1
  obtain ⟨residual, sequence, target, index, played, mixed, bayes,
      increasing, converges, consistent, freeOptimal⟩ :=
    N.exists_consistent_free_agent_completion decisionRecall fallback certificate payoff free
      pinned referenceLaws (fun n agent _ => pinnedFull n agent) referenceFull epsilon positive
      small vanishes
  have perturbs (n : ℕ) : restriction.PerturbsProfile (sourceSequence n).strategy
      reference.strategy (sequence n).strategy (epsilon n) (positive n).le (small n).le := by
    intro who site
    let agent := N.agentAt (restriction.site who site)
    have notFree : agent ∉ free := by
      simp only [free, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      exact restriction.retained_site who site
    exact (congrFun (congrFun (played n) who) (restriction.information who site.1)).trans
      ((N.agentBehavior_at N.playedInformation fallback _ agent).trans
        ((ite_eq_right notFree).trans
          (restriction.perturbProfile_perturbs (sourceSequence n).strategy
            reference.strategy (epsilon n) (positive n).le (small n).le who site)))
  have sourceAlong : BehavioralAssessmentConvergesPointwise
      (fun n => sourceSequence (index n)) source :=
    ⟨fun who site => (sourceConverges.strategy who site).subseq increasing,
      fun who site => (sourceConverges.belief who site).subseq increasing⟩
  have extendsTarget : restriction.ExtendsProfile source.strategy target.strategy :=
    restriction.extendsProfile_of_perturbs_converges reference.strategy
      (fun n => sourceSequence (index n)) source (fun n => sequence (index n)) target
      sourceAlong converges
      (fun n => epsilon (index n)) (fun n => (positive (index n)).le)
      (fun n => (small (index n)).le) (vanishes.comp increasing.tendsto_atTop)
      (fun n => perturbs (index n))
  refine ⟨target, consistent, extendsTarget, ?_, ?_⟩
  · intro who site
    let elapsed := depth who site
    let steps := Fintype.card ι * elapsed
    let factor (n : ℕ) := (1 - epsilon n) ^ steps
    have factorPositive (n : ℕ) : 0 < factor n := pow_pos (sub_pos.mpr (small n)) _
    have factorBound (n : ℕ) : factor n ≤ 1 :=
      pow_le_one₀ (sub_pos.mpr (small n)).le (by linarith [positive n])
    have negligible : Tendsto (fun n => (1 - factor n) /
        (factor n * (M.informationMass (sourceSequence n).strategy who site).toReal)) atTop
          (nhds 0) := by
      apply squeeze_zero
      · intro n
        exact div_nonneg (sub_nonneg.mpr (factorBound n))
          (mul_nonneg (factorPositive n).le ENNReal.toReal_nonneg)
      · intro n
        exact div_le_div_of_nonneg_left (sub_nonneg.mpr (factorBound n))
          (mul_pos (factorPositive n) (reachPositive n))
          (mul_le_mul_of_nonneg_left (reachBound n ⟨who, site⟩) (factorPositive n).le)
      · exact relativeTremble_power_ratio_tendsto reach reachPositive steps
    have beliefs := restriction.retained_beliefs_converge sourceSequence sequence
      sourceAntichain decisionRecall.decisionInformationAntichain
      (fun n => (sourceApproximates n).1) mixed (fun n => (sourceApproximates n).2) bayes
      who site elapsed (clock who site) factor factorPositive factorBound
      (fun n history => restriction.perturbed_run_domination (sourceSequence n).strategy
        reference.strategy (sequence n).strategy (epsilon n) (positive n).le (small n).le
        (perturbs n) elapsed history)
      negligible (source.belief who site) (sourceConverges.belief who site)
    exact (converges.belief who (restriction.site who site)).unique
      (beliefs.subseq increasing)
  · intro who site newSite law
    have member : N.agentAt site ∈ free := by
      simp only [free, Finset.mem_filter, Finset.mem_univ, true_and]
      exact newSite
    exact freeOptimal who site member law

end GameTheory.Protocol.InformationModel.ActionRestriction
