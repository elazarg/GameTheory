/-
# Simultaneous completion of free agents

Some agents of the agent normal form keep prescribed laws, which may vary
along a sequence. Every other agent trembles toward a fixed reference with a
vanishing weight, and finite Nash existence chooses all their residual laws
together. The assembled profiles are fully mixed, so their Bayes assessments
turn each free agent's ex ante optimality into optimality of its continuation.
One common subsequence converges to a consistent assessment at which every free
decision site is optimal against single-site law changes. The prescribed laws
need not converge, and nothing is claimed about the prescribed sites.
-/

import GameTheory.Analysis.Protocol.ExtensiveFormPerfection

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ExecutionProtocol ι}
  (M : InformationModel E) [Fintype E.History] [∀ i, DecidableEq (M.InfoState i)]

/-- **Consistent completion of free agents.** -/
theorem exists_consistent_free_agent_completion (hrecall : M.DecisionRecall)
    (fallback : (i : ι) → M.Policy i) (certificate : E.WellFoundedHistories)
    (payoff : ι → E.History → ℝ) (free : Finset (M.InformationAgent M.playedInformation))
    (pinned : ℕ → Profile (M.agentForm fallback certificate).sig.mixed)
    (reference : Profile (M.agentForm fallback certificate).sig.mixed)
    (pinnedFull : ∀ n agent, agent ∉ free → FullSupport (pinned n agent))
    (referenceFull : ∀ agent, FullSupport (reference agent))
    (epsilon : ℕ → ℝ) (positive : ∀ n, 0 < epsilon n) (small : ∀ n, epsilon n < 1)
    (vanishes : Tendsto epsilon atTop (nhds 0)) :
    ∃ (residual : ℕ → Profile (M.agentForm fallback certificate).sig.mixed)
      (sequence : ℕ → M.BehavioralAssessment) (limit : M.BehavioralAssessment)
      (index : ℕ → ℕ),
      (∀ n, (sequence n).strategy = M.agentBehavior M.playedInformation fallback
        (pinnedTremble free (pinned n) reference (residual n) (epsilon n) (positive n).le
          (small n).le)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n)
        hrecall.decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent hrecall.decisionInformationAntichain ∧
      ∀ i (site : M.InformationSite i), M.agentAt site ∈ free →
        ∀ law : PMF (M.Choice i site.1),
          (limit.continuationContext certificate site (payoff i)).value
              ((limit.strategy i).withLaw site.1 law) ≤
            (limit.continuationContext certificate site (payoff i)).value
              (limit.strategy i) := by
  let F := M.agentForm fallback certificate
  let _ (agent : M.InformationAgent M.playedInformation) : Fintype (F.sig.Strategy agent) :=
    @Fintype.ofFinite _ (M.finite_choice_of_played agent.2.2)
  have _ (agent : M.InformationAgent M.playedInformation) : Nonempty (F.sig.Strategy agent) :=
    M.nonempty_choice_of_played agent.2.2
  have : Finite F.sig.Outcome := inferInstanceAs (Finite E.History)
  have integrable : F.HasIntegrableUtility (M.agentUtility payoff) :=
    fun _ _ => payoffIntegrable_of_finite _ _
  choose residual optimal using fun n => exists_pinned_tremble_bestResponses
    (F := M.agentForm fallback certificate) (M.agentUtility payoff) integrable free (pinned n)
    reference (epsilon n) (positive n).le (small n)
  let played (n : ℕ) := pinnedTremble free (pinned n) reference (residual n) (epsilon n)
    (positive n).le (small n).le
  let behavior (n : ℕ) := M.agentBehavior M.playedInformation fallback (played n)
  have full (n : ℕ) : ∀ i (site : M.InformationSite i) (choice : M.Choice i site.1),
      choice ∈ (behavior n i site.1).support := by
    intro i site choice
    have supported := pinnedTremble_fullSupport free (pinned n) reference (residual n)
      (epsilon n) (positive n) (small n).le (pinnedFull n) (fun agent _ => referenceFull agent)
      (M.agentAt site) choice
    rwa [show behavior n i site.1 = played n (M.agentAt site) from
      M.agentBehavior_at M.playedInformation fallback _ (M.agentAt site)]
  let antichain := hrecall.decisionInformationAntichain
  let sequence (n : ℕ) : M.BehavioralAssessment := M.bayesAssessment (behavior n) (full n) antichain
  have sequenceStrategy (n : ℕ) : (sequence n).strategy = behavior n :=
    M.bayesAssessment_strategy _ _ _
  have mixed (n : ℕ) : (sequence n).IsFullyMixed := by
    intro i site choice
    rw [sequenceStrategy]
    exact full n i site choice
  have bayes (n : ℕ) : BehavioralAssessment.IsBayesConsistent M (sequence n) antichain :=
    M.bayesAssessment_isBayesConsistent _ _ _
  obtain ⟨limit, index, increasing, converges⟩ :=
    M.exists_subseq_behavioralAssessmentConvergesPointwise_atSites_of_uniformlyTight sequence
      (fun _ _ => uniformlyTight_of_finite _) (fun _ _ => uniformlyTight_of_finite _)
  refine ⟨residual, sequence, limit, index, sequenceStrategy, mixed, bayes, increasing, converges,
    converges.isSequentiallyConsistent antichain (fun n => mixed (index n))
      (fun n => bayes (index n)), ?_⟩
  intro i site freeSite law
  let total : ℝ := ∑ history : E.History, |payoff i history|
  have totalBound (history : E.History) : |payoff i history| ≤ total :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff i other)) (Finset.mem_univ history)
  have playedAt (n : ℕ) : (sequence n).strategy i site.1 =
      mix (epsilon n) (positive n).le (small n).le (reference (M.agentAt site))
        (residual n (M.agentAt site)) := by
    rw [sequenceStrategy]
    exact (M.agentBehavior_at M.playedInformation fallback _ (M.agentAt site)).trans
      (ite_eq_left freeSite)
  have residualConverges : PMFConvergesPointwise (fun n => residual (index n) (M.agentAt site))
      (limit.strategy i site.1) := by
    apply PMFConvergesPointwise.of_mix_vanishing (α := M.Choice i site.1)
      (reference (M.agentAt site))
      (fun n => residual (index n) (M.agentAt site)) _ (fun n => epsilon (index n))
      (fun n => (positive (index n)).le) (fun n => small (index n))
      (vanishes.comp increasing.tendsto_atTop)
    convert converges.strategy i site using 1
    funext n
    exact (playedAt (index n)).symm
  have comparison (n : ℕ) (replacement : PMF (M.Choice i site.1)) :
      ((sequence n).continuationContext certificate site (payoff i)).value
          (((sequence n).strategy i).withLaw site.1 replacement) -
        ((sequence n).continuationContext certificate site (payoff i)).value
          ((sequence n).strategy i) =
      ((M.informationMass (behavior n) i site).toReal)⁻¹ *
        (expectedUtility (M.agentUtility payoff) (M.agentAt site)
            (F.mixed.play (Profile.update (played n) (M.agentAt site) replacement)) -
          expectedUtility (M.agentUtility payoff) (M.agentAt site) (F.mixed.play (played n))) := by
    have identity := M.agentGain_eq_mass_mul hrecall fallback certificate payoff (played n)
      (full n) site replacement
    have massPositive : 0 < (M.informationMass (behavior n) i site).toReal := by
      have positiveMass := M.informationMass_pos_of_fullSupport _ (mixed n) i site
      rw [sequenceStrategy] at positiveMass
      exact ENNReal.toReal_pos positiveMass.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
        (M.informationMass_le_one _ i site (antichain i site)))
    exact (eq_inv_mul_iff_mul_eq₀ massPositive.ne').mpr identity.symm
  have gain (n : ℕ) :
      ((sequence (index n)).continuationContext certificate site (payoff i)).value
          (((sequence (index n)).strategy i).withLaw site.1 law) ≤
        ((sequence (index n)).continuationContext certificate site (payoff i)).value
          (((sequence (index n)).strategy i).withLaw site.1
            (residual (index n) (M.agentAt site))) := by
    have better := optimal (index n) (M.agentAt site) freeSite law
    have first := comparison (index n) law
    have second := comparison (index n) (residual (index n) (M.agentAt site))
    have inverseNonnegative : 0 ≤ ((M.informationMass (behavior (index n)) i site).toReal)⁻¹ :=
      inv_nonneg.mpr ENNReal.toReal_nonneg
    have scaled :
        ((M.informationMass (behavior (index n)) i site).toReal)⁻¹ *
            (expectedUtility (M.agentUtility payoff) (M.agentAt site)
                (F.mixed.play (Profile.update (played (index n)) (M.agentAt site) law)) -
              expectedUtility (M.agentUtility payoff) (M.agentAt site)
                (F.mixed.play (played (index n)))) ≤
          ((M.informationMass (behavior (index n)) i site).toReal)⁻¹ *
            (expectedUtility (M.agentUtility payoff) (M.agentAt site)
                (F.mixed.play (Profile.update (played (index n)) (M.agentAt site)
                  (residual (index n) (M.agentAt site)))) -
              expectedUtility (M.agentUtility payoff) (M.agentAt site)
                (F.mixed.play (played (index n)))) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right better _) inverseNonnegative
    linarith
  have value (replacement : ℕ → M.BehavioralPolicy i) (target : M.BehavioralPolicy i)
      (hreplacement : ∀ decision : M.InformationSite i,
        PMFConvergesPointwise (fun n => replacement n decision.1) (target decision.1)) :=
    M.continuationContext_value_tendsto_of_bounded_terminal certificate
      (fun j decision => converges.strategy j decision) i site (converges.belief i site)
      hreplacement (payoff i) total ((abs_nonneg _).trans (totalBound E.initHistory))
      (fun final _ => totalBound final)
  have withLawLimit (laws : ℕ → PMF (M.Choice i site.1)) (target : PMF (M.Choice i site.1))
      (lawsConverge : PMFConvergesPointwise laws target) (decision : M.InformationSite i) :
      PMFConvergesPointwise
        (fun n => ((sequence (index n)).strategy i).withLaw site.1 (laws n) decision.1)
        ((limit.strategy i).withLaw site.1 target decision.1) := by
    by_cases hsame : decision = site
    · subst decision
      simpa only [BehavioralPolicy.withLaw_self] using lawsConverge
    · have different : decision.1 ≠ site.1 := fun equal => hsame (Subtype.ext equal)
      simpa only [BehavioralPolicy.withLaw_of_ne _ _ _ different] using
        converges.strategy i decision
  have upper := value _ _ (withLawLimit _ _ residualConverges)
  rw [BehavioralPolicy.withLaw_eq_self] at upper
  exact le_of_tendsto_of_tendsto' (value _ _ (withLawLimit _ _ (pmfConvergesPointwise_const law)))
    upper gain

end GameTheory.Protocol.InformationModel
