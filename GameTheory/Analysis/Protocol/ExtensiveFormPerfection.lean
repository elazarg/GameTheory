/-
# Extensive-form trembling-hand perfection

A behavioral profile is trembling-hand perfect in the extensive form when it is
assembled from a trembling-hand perfect profile of the agent normal form, whose
agents are the information values met at nonterminal histories. Selten's
existence theorem for finite games therefore gives such a profile in every
protocol with finitely many histories.

Under decision recall every such profile is the strategy of a sequential
equilibrium. The perturbed agent equilibria are fully mixed, so their Bayes
assessments evaluate each agent's local deviation by the site's mass times its
continuation gain; that local optimality passes to a consistent limit, and
one-shot optimality at a consistent assessment is sequential rationality.

Primary references: R. Selten, “Reexamination of the Perfectness Concept for
Equilibrium Points in Extensive Games,” *International Journal of Game
Theory* 4 (1975); D. M. Kreps and R. Wilson, “Sequential Equilibria,”
*Econometrica* 50 (1982).
-/

import GameTheory.Analysis.PerturbedEquilibrium
import GameTheory.Analysis.Protocol.AgentForm
import GameTheory.Analysis.Protocol.AssessmentCompactness
import GameTheory.Analysis.Protocol.SequentialOneShot

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type*} [DecidableEq ι] {E : ExecutionProtocol ι}
  (M : InformationModel E) [Fintype E.History] [∀ i, DecidableEq (M.InfoState i)]
variable [Fintype ι]

omit [DecidableEq ι] in
/-- The information values of each player at nonterminal histories. -/
def playedInformation (who : ι) : Finset (M.InfoState who) := by
  classical
  exact (Finset.univ.filter fun history : E.History => ¬ E.terminal history.state).image
    fun history => M.infoOf who history.trace

omit [Fintype ι] [DecidableEq ι] in
theorem mem_playedInformation {who : ι} {history : E.History}
    (running : ¬ E.terminal history.state) :
    M.infoOf who history.trace ∈ M.playedInformation who := by
  classical
  unfold playedInformation
  exact Finset.mem_image.mpr ⟨history, Finset.mem_filter.mpr ⟨Finset.mem_univ _, running⟩, rfl⟩

omit [Fintype ι] [DecidableEq ι] in
theorem site_mem_playedInformation {who : ι} (site : M.InformationSite who) :
    site.1 ∈ M.playedInformation who := by
  obtain ⟨history, running, _⟩ := site.2
  rw [← history.2]
  exact M.mem_playedInformation running

omit [Fintype ι] [DecidableEq ι] in
/-- Played information covers every nonterminal history. -/
theorem coversInformationSites_playedInformation (bound : ℕ) :
    M.CoversInformationSites M.playedInformation bound :=
  fun _ _ running _ => M.mem_playedInformation running

omit [Fintype ι] [DecidableEq ι] in
/-- An agent at a played information value has finitely many choices: one
where its player is inactive, finitely many at a decision site. -/
theorem finite_choice_of_played {who : ι} {info : M.InfoState who}
    (played : info ∈ M.playedInformation who) : Finite (M.Choice who info) := by
  classical
  unfold playedInformation at played
  obtain ⟨history, member, rfl⟩ := Finset.mem_image.mp played
  have running := (Finset.mem_filter.mp member).2
  by_cases active : E.active history.state who
  · obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history running active
    rw [← same]
    infer_instance
  · let _ := M.subsingleton_choice_of_not_active history.trace active
    infer_instance

omit [Fintype ι] [DecidableEq ι] [Fintype E.History] [∀ i, DecidableEq (M.InfoState i)] in
/-- An agent at a played information value has a legal choice. -/
theorem nonempty_choice_of_played [Fintype E.History] [∀ i, DecidableEq (M.InfoState i)]
    {who : ι} {info : M.InfoState who}
    (played : info ∈ M.playedInformation who) : Nonempty (M.Choice who info) := by
  classical
  unfold playedInformation at played
  obtain ⟨history, member, rfl⟩ := Finset.mem_image.mp played
  have running := (Finset.mem_filter.mp member).2
  obtain ⟨joint, legal⟩ := E.exists_legal running
  exact ⟨⟨joint who, (M.menu_adequate who history.trace (joint who)).mpr
    (E.legalOption_of_legal legal who)⟩⟩

omit [DecidableEq ι] in
/-- The agent normal form over played information. -/
abbrev agentForm (fallback : (i : ι) → M.Policy i) (certificate : E.WellFoundedHistories) :
    GameForm (M.InformationAgent M.playedInformation) :=
  M.informationAgentForm M.playedInformation fallback certificate

omit [Fintype ι] [DecidableEq ι] in
/-- Every agent receives its player's payoff. -/
abbrev agentUtility (payoff : ι → E.History → ℝ) :
    E.History → M.InformationAgent M.playedInformation → ℝ :=
  fun history agent => payoff agent.1 history

/-- **Extensive-form trembling-hand perfection.** A behavioral profile is
perfect when, at every decision site, it is the law of a trembling-hand perfect
profile of the agent normal form. -/
def IsExtensiveFormPerfect (fallback : (i : ι) → M.Policy i)
    (certificate : E.WellFoundedHistories) (payoff : ι → E.History → ℝ)
    (strategy : (i : ι) → M.BehavioralPolicy i) : Prop :=
  ∃ laws : Profile (M.agentForm fallback certificate).sig.mixed,
    (M.agentForm fallback certificate).IsTremblingHandPerfect
        (euPreference (M.agentUtility payoff)) laws ∧
      ∀ i (site : M.InformationSite i),
        strategy i site.1 = M.agentBehavior M.playedInformation fallback laws i site.1

/-- **Perfect profiles exist.** Every protocol with finitely many histories has
an extensive-form trembling-hand perfect profile. -/
theorem exists_isExtensiveFormPerfect (fallback : (i : ι) → M.Policy i)
    (certificate : E.WellFoundedHistories) (payoff : ι → E.History → ℝ) :
    ∃ strategy, M.IsExtensiveFormPerfect fallback certificate payoff strategy := by
  let F := M.agentForm fallback certificate
  let _ (agent : M.InformationAgent M.playedInformation) : Fintype (F.sig.Strategy agent) :=
    @Fintype.ofFinite _ (M.finite_choice_of_played agent.2.2)
  have _ (agent : M.InformationAgent M.playedInformation) : Nonempty (F.sig.Strategy agent) :=
    M.nonempty_choice_of_played agent.2.2
  have : Finite F.sig.Outcome := inferInstanceAs (Finite E.History)
  have integrable : F.HasIntegrableUtility (M.agentUtility payoff) :=
    fun _ _ => payoffIntegrable_of_finite _ _
  obtain ⟨laws, perfect⟩ := exists_isTremblingHandPerfect (F := F) (M.agentUtility payoff)
    integrable
  exact ⟨M.agentBehavior M.playedInformation fallback laws, laws, perfect, fun _ _ => rfl⟩

/-- The agent choosing at a decision site. -/
abbrev agentAt {i : ι} (site : M.InformationSite i) : M.InformationAgent M.playedInformation :=
  ⟨i, ⟨site.1, M.site_mem_playedInformation site⟩⟩

/-- **Agent deviations at fully mixed play.** When agent laws assemble a
profile that is fully mixed at decision sites, a deviation of the agent at a
site changes its player's expected payoff by the site's mass times the change
of the site's Bayes continuation value. -/
theorem agentGain_eq_mass_mul (hrecall : M.DecisionRecall) (fallback : (i : ι) → M.Policy i)
    (certificate : E.WellFoundedHistories) (payoff : ι → E.History → ℝ)
    (laws : Profile (M.agentForm fallback certificate).sig.mixed)
    (full : ∀ i (site : M.InformationSite i) (choice : M.Choice i site.1),
      choice ∈ (M.agentBehavior M.playedInformation fallback laws i site.1).support)
    {i : ι} (site : M.InformationSite i) (replacement : PMF (M.Choice i site.1)) :
    expectedUtility (M.agentUtility payoff) (M.agentAt site)
        ((M.agentForm fallback certificate).mixed.play
          (Profile.update laws (M.agentAt site) replacement)) -
      expectedUtility (M.agentUtility payoff) (M.agentAt site)
        ((M.agentForm fallback certificate).mixed.play laws) =
    (M.informationMass (M.agentBehavior M.playedInformation fallback laws) i site).toReal *
      (((M.bayesAssessment _ full hrecall.decisionInformationAntichain).continuationContext
          certificate site (payoff i)).value
          ((M.agentBehavior M.playedInformation fallback laws i).withLaw site.1 replacement) -
        ((M.bayesAssessment _ full hrecall.decisionInformationAntichain).continuationContext
          certificate site (payoff i)).value
          (M.agentBehavior M.playedInformation fallback laws i)) := by
  let F := M.agentForm fallback certificate
  obtain ⟨horizon, -, bounded⟩ := E.exists_pos_boundedHorizon
  have realize (profile : Profile F.sig.mixed) : F.mixed.play profile =
      M.runBehavioralTerminalFrom certificate
        (M.agentBehavior M.playedInformation fallback profile) E.initHistory :=
    M.informationAgentForm_mixed_play M.playedInformation fallback certificate bounded
      hrecall.actsOnceWhereItMatters (M.coversInformationSites_playedInformation horizon) profile
  have update : M.agentBehavior M.playedInformation fallback
      (Profile.update (sig := F.sig.mixed) laws (M.agentAt site) replacement) =
    Profile.update (sig := M.behavioralSignature) (M.agentBehavior M.playedInformation fallback
      laws) i ((M.agentBehavior M.playedInformation fallback laws i).withLaw site.1 replacement) :=
    M.agentBehavior_update M.playedInformation fallback laws (M.agentAt site) replacement
  have mixed : (M.bayesAssessment _ full hrecall.decisionInformationAntichain).IsFullyMixed := by
    intro j decision choice
    rw [M.bayesAssessment_strategy]
    exact full j decision choice
  have root := BehavioralAssessment.rootGain_withLaw_eq_mass_mul M hrecall
    (M.bayesAssessment _ full hrecall.decisionInformationAntichain) mixed
    (M.bayesAssessment_isBayesConsistent _ _ _) certificate i (payoff i) site replacement
  simp only [M.bayesAssessment_strategy] at root
  change expect (F.mixed.play _) (payoff i) - expect (F.mixed.play laws) (payoff i) = _
  rw [realize, realize, update]
  exact root

/-- **Perfect profiles are sequential equilibria.** Under decision recall, an
extensive-form trembling-hand perfect profile is, at every decision site, the
strategy of a sequential equilibrium. -/
theorem IsExtensiveFormPerfect.exists_sequentialEquilibrium (hrecall : M.DecisionRecall)
    {fallback : (i : ι) → M.Policy i} {certificate : E.WellFoundedHistories}
    {payoff : ι → E.History → ℝ} {strategy : (i : ι) → M.BehavioralPolicy i}
    (perfect : M.IsExtensiveFormPerfect fallback certificate payoff strategy) :
    ∃ assessment : M.BehavioralAssessment,
      (∀ i (site : M.InformationSite i), assessment.strategy i site.1 = strategy i site.1) ∧
        assessment.IsSequentialEquilibrium hrecall.decisionInformationAntichain certificate
          payoff := by
  obtain ⟨laws, ⟨lower, approximating, hequilibria, hzero, hconverges⟩, hstrategy⟩ := perfect
  let F := M.agentForm fallback certificate
  let behavior (n : ℕ) := M.agentBehavior M.playedInformation fallback (approximating n)
  have full (n : ℕ) : ∀ i (site : M.InformationSite i) (choice : M.Choice i site.1),
      choice ∈ (behavior n i site.1).support := by
    intro i site choice
    have supported := GameForm.Perturbation.Positive.fullSupport_of_respects F
      (hequilibria n).1 (hequilibria n).2.1 (M.agentAt site) choice
    rwa [show behavior n i site.1 = approximating n (M.agentAt site) from
      M.agentBehavior_at M.playedInformation fallback _ (M.agentAt site)]
  let antichain := hrecall.decisionInformationAntichain
  let sequence (n : ℕ) : M.BehavioralAssessment := M.bayesAssessment (behavior n) (full n) antichain
  have sequenceStrategy (n : ℕ) : (sequence n).strategy = behavior n :=
    M.bayesAssessment_strategy _ _ _
  obtain ⟨limit, subseq, increasing, converges⟩ :=
    M.exists_subseq_behavioralAssessmentConvergesPointwise_atSites_of_uniformlyTight sequence
      (fun _ _ => uniformlyTight_of_finite _) (fun _ _ => uniformlyTight_of_finite _)
  have mixed (n : ℕ) : (sequence n).IsFullyMixed := by
    intro i site choice
    rw [sequenceStrategy]
    exact full n i site choice
  have bayes (n : ℕ) : BehavioralAssessment.IsBayesConsistent M (sequence n) antichain :=
    M.bayesAssessment_isBayesConsistent _ _ _
  have strategyAt (i : ι) (site : M.InformationSite i) :
      limit.strategy i site.1 = strategy i site.1 := by
    rw [hstrategy]
    apply (converges.strategy i site).unique
    have agentLimit := (hconverges (M.agentAt site)).subseq increasing
    have same : (fun n => (sequence (subseq n)).strategy i site.1) =
        fun n => approximating (subseq n) (M.agentAt site) := by
      funext n
      rw [sequenceStrategy]
      exact M.agentBehavior_at M.playedInformation fallback _ (M.agentAt site)
    rw [M.agentBehavior_at M.playedInformation fallback laws (M.agentAt site), same]
    exact agentLimit
  let total (i : ι) : ℝ := ∑ history : E.History, |payoff i history|
  have totalBound (i : ι) (history : E.History) : |payoff i history| ≤ total i :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff i other)) (Finset.mem_univ history)
  have localOptimal : ∀ (i : ι) (site : M.InformationSite i) (law : PMF (M.Choice i site.1)),
      (limit.continuationContext certificate site (payoff i)).value
          ((limit.strategy i).withLaw site.1 law) ≤
        (limit.continuationContext certificate site (payoff i)).value (limit.strategy i) := by
    intro i site law
    let _ : Fintype (F.sig.Strategy (M.agentAt site)) := @Fintype.ofFinite _
      (M.finite_choice_of_played (M.agentAt site).2.2)
    obtain ⟨repaired, respects, repairedConverges⟩ : ∃ repaired : ℕ → PMF (M.Choice i site.1),
        (∀ n, F.StrategyRespectsPerturbation (lower (subseq n) (M.agentAt site)) (repaired n)) ∧
          PMFConvergesPointwise repaired law :=
      F.exists_repair_convergesPointwise (fun n => lower (subseq n) (M.agentAt site))
        (fun n => approximating (subseq n) (M.agentAt site))
        (fun n action => ((hequilibria (subseq n)).1 (M.agentAt site) action).le)
        (fun n => (hequilibria (subseq n)).2.1 (M.agentAt site))
        (fun action => (hzero (M.agentAt site) action).comp increasing.tendsto_atTop) law
    have gain (n : ℕ) :
        ((sequence (subseq n)).continuationContext certificate site (payoff i)).value
            (((sequence (subseq n)).strategy i).withLaw site.1 (repaired n)) -
          ((sequence (subseq n)).continuationContext certificate site (payoff i)).value
            ((sequence (subseq n)).strategy i) ≤ 0 := by
      have : Finite F.mixed.sig.Outcome := inferInstanceAs (Finite E.History)
      have integrable : F.mixed.HasIntegrableUtility (M.agentUtility payoff) :=
        fun _ _ => payoffIntegrable_of_finite _ _
      have preferred := ((F.isPerturbedEq_iff _ _ _).mp (hequilibria (subseq n)).2).2
        (M.agentAt site) (repaired n) (respects n)
      have compared := (euPreference_iff _ _ _ _ (integrable _ _) (integrable _ _)).mp preferred
      have identity := M.agentGain_eq_mass_mul hrecall fallback certificate payoff
        (approximating (subseq n)) (full (subseq n)) site (repaired n)
      have massPositive :
          0 < (M.informationMass (behavior (subseq n)) i site).toReal := by
        have positive := M.informationMass_pos_of_fullSupport _ (mixed (subseq n)) i site
        rw [sequenceStrategy] at positive
        exact ENNReal.toReal_pos positive.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
          (M.informationMass_le_one _ i site (antichain i site)))
      rw [sequenceStrategy]
      have nonpositive := sub_nonpos.mpr compared
      set_option backward.isDefEq.respectTransparency false in
      rw [identity] at nonpositive
      exact nonpos_of_mul_nonpos_right nonpositive massPositive
    have value (replacement : ℕ → M.BehavioralPolicy i) (target : M.BehavioralPolicy i)
        (hreplacement : ∀ decision : M.InformationSite i,
          PMFConvergesPointwise (fun n => replacement n decision.1) (target decision.1)) :=
      M.continuationContext_value_tendsto_of_bounded_terminal certificate
        (fun j decision => converges.strategy j decision) i site (converges.belief i site)
        hreplacement (payoff i) (total i) ((abs_nonneg _).trans (totalBound i E.initHistory))
        (fun final _ => totalBound i final)
    have withLawLimit (decision : M.InformationSite i) :
        PMFConvergesPointwise
          (fun n => ((sequence (subseq n)).strategy i).withLaw site.1 (repaired n) decision.1)
          ((limit.strategy i).withLaw site.1 law decision.1) := by
      by_cases hsame : decision = site
      · subst decision
        simpa only [BehavioralPolicy.withLaw_self] using repairedConverges
      · have different : decision.1 ≠ site.1 := fun equal => hsame (Subtype.ext equal)
        simpa only [BehavioralPolicy.withLaw_of_ne _ _ _ different] using
          converges.strategy i decision
    exact sub_nonpos.mp (le_of_tendsto_of_tendsto'
      ((value _ _ withLawLimit).sub (value _ _ (converges.strategy i))) tendsto_const_nhds gain)
  refine ⟨limit, strategyAt, ?_⟩
  exact (BehavioralAssessment.isSequentialEquilibrium_iff_locallyOptimal M hrecall limit
    certificate payoff).mpr ⟨converges.isSequentiallyConsistent antichain
      (fun n => mixed (subseq n)) (fun n => bayes (subseq n)), localOptimal⟩

end GameTheory.Protocol.InformationModel
