/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

import GameTheory.Analysis.ComponentCompletion
import GameTheory.Analysis.Protocol.ExtensiveFormPerfection
import GameTheory.Analysis.Protocol.PassageBayes
import GameTheory.Math.Probability.Bounds

/-! # Consistent assessments from component mixtures

Each played agent chooses a mixture of finitely many fully supported component
laws, possibly sharing its weights with other agents. Completion chooses the
shared mixture weights of every group together. Inverse site-reach importance turns the
aggregate unilateral gains into sums of Bayes continuation gains.

One common subsequence converges to a sequentially consistent assessment.
At sites with converging components, the limiting strategy is a mixture of the
limiting laws; vanishing component-deviation errors imply limiting optimality.
With one agent per group the errors are zero. No common information-history
depth is required, and aggregate optimality does not imply every member's optimality.
-/

noncomputable section
namespace GameTheory
open Math.Probability
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : GameForm ι}

/-- The components that recover `pinnedTremble`: a free player has one
component per choice, the choice trembled toward the reference; every
component of another player is its pinned law. -/
def pinnedTrembleComponent (free : Finset ι) (pinned reference : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) (who : ι)
    (choice : F.sig.Strategy who) : PMF (F.sig.Strategy who) :=
  if who ∈ free then mix epsilon nonnegative small (reference who) (PMF.pure choice)
  else pinned who

omit [Fintype ι] in
/-- Mixing the pinned-tremble components with residual weights is the pinned
tremble of the residual laws. -/
theorem bind_pinnedTrembleComponent (free : Finset ι)
    (pinned reference residual : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) (who : ι) :
    (residual who).bind (pinnedTrembleComponent free pinned reference epsilon nonnegative small
        who) =
      pinnedTremble free pinned reference residual epsilon nonnegative small who := by
  change (residual who).bind (fun choice =>
    if who ∈ free then mix epsilon nonnegative small (reference who) (PMF.pure choice)
    else pinned who) = _
  by_cases active : who ∈ free
  · simp only [pinnedTremble, active, ↓reduceIte, bind_mix_pure]
  · simp only [pinnedTremble, active, ↓reduceIte, PMF.bind_const]

end GameTheory

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ExecutionProtocol ι}
  (M : InformationModel E) [Fintype E.History] [∀ i, DecidableEq (M.InfoState i)]

omit [DecidableEq ι] [Fintype E.History] [∀ i, DecidableEq (M.InfoState i)] in
/-- The expected passage indicator of a decision site is its information mass. -/
private theorem expect_passage {i : ι} (site : M.InformationSite i)
    (antichain : site.IsHistoryAntichain) (certificate : E.WellFoundedHistories)
    (strategy : ∀ player, M.BehavioralPolicy player) :
    expect (M.runBehavioralTerminalFrom certificate strategy E.initHistory)
        (fun final => if (site.ancestor? M final).isSome then (1 : ℝ) else 0) =
      (M.informationMass strategy i site).toReal := by
  classical
  have indicator := expect_indicator (M.runBehavioralTerminalFrom certificate strategy
    E.initHistory) {final | (site.ancestor? M final).isSome = true}
  rw [← site.terminal_ancestor_passage M antichain certificate strategy, PMF.map_comp]
  convert indicator using 2
  · funext final
    by_cases passes : (site.ancestor? M final).isSome = true <;> simp [passes]
  rw [PMF.map_apply, PMF.toOuterMeasure_apply]
  refine tsum_congr fun final => ?_
  by_cases passes : (site.ancestor? M final).isSome = true
  · simp [Set.indicator, passes]
  · simp_all [Set.indicator]

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- **Consistent completion with shared mixture weights.** Every agent plays a mixture of its fully
supported components with the weights of its group; the weights of all groups are
chosen together by `exists_bestResponses_with_shared_mixture_weights`, with each member weighed by
the inverse of its site's probability. The assembled assessments are fully
mixed and Bayes consistent; at every index no common replacement of a group's
weights raises the sum of its members' gains in Bayes continuation value. One
common subsequence converges to a consistent assessment. Wherever the
components of a site converge, the limit law is a mixture of the limit
components, and it is optimal among such mixtures as soon as the site's
component-mixture gains are bounded along the sequence by errors that vanish. -/
theorem exists_consistent_completion_with_shared_mixture_weights (hrecall : M.DecisionRecall)
    (fallback : (i : ι) → M.Policy i) (certificate : E.WellFoundedHistories)
    (payoff : ι → E.History → ℝ)
    {WeightGroup : Type*} [Finite WeightGroup] [DecidableEq WeightGroup]
    (groupOf : M.InformationAgent M.playedInformation → WeightGroup)
    {Part : WeightGroup → Type*} [∀ p, Finite (Part p)] [∀ p, Nonempty (Part p)]
    (component : ℕ → ∀ agent, Part (groupOf agent) →
      PMF ((M.agentForm fallback certificate).sig.Strategy agent))
    (componentFull : ∀ n agent part, FullSupport (component n agent part)) :
    ∃ (weights : ℕ → ∀ p, PMF (Part p))
      (sequence : ℕ → M.BehavioralAssessment) (limit : M.BehavioralAssessment)
      (index : ℕ → ℕ),
      (∀ n, (sequence n).strategy = M.agentBehavior M.playedInformation fallback
        fun agent => (weights n (groupOf agent)).bind (component n agent)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n)
        hrecall.decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent hrecall.decisionInformationAntichain ∧
      (∀ n (alternative : ∀ p, PMF (Part p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => groupOf agent = p),
          (if decision : M.IsDecisionInfo agent.1 agent.2.1 then
            ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                (payoff agent.1)).value
                (((sequence n).strategy agent.1).withLaw agent.2.1
                  ((alternative (groupOf agent)).bind (component n agent))) -
              ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                (payoff agent.1)).value ((sequence n).strategy agent.1)
          else 0) ≤ 0) ∧
      ∀ i (site : M.InformationSite i)
        (limitComponent : Part (groupOf (M.agentAt site)) → PMF (M.Choice i site.1)),
        (∀ part, PMFConvergesPointwise (fun n => component n (M.agentAt site) part)
          (limitComponent part)) →
        (∃ limitWeights : PMF (Part (groupOf (M.agentAt site))),
          limit.strategy i site.1 = limitWeights.bind limitComponent) ∧
        ∀ (error : ℕ → ℝ), Filter.Tendsto error Filter.atTop (nhds 0) →
          (∀ n (alternative : PMF (Part (groupOf (M.agentAt site)))),
            ((sequence n).continuationContext certificate site (payoff i)).value
                (((sequence n).strategy i).withLaw site.1
                  (alternative.bind (component n (M.agentAt site)))) ≤
              ((sequence n).continuationContext certificate site (payoff i)).value
                ((sequence n).strategy i) + error n) →
          ∀ alternative : PMF (Part (groupOf (M.agentAt site))),
            (limit.continuationContext certificate site (payoff i)).value
                ((limit.strategy i).withLaw site.1 (alternative.bind limitComponent)) ≤
              (limit.continuationContext certificate site (payoff i)).value
                (limit.strategy i) := by
  classical
  let F := M.agentForm fallback certificate
  have : Finite F.sig.Outcome := inferInstanceAs (Finite E.History)
  let _ (p : WeightGroup) : Fintype (Part p) := Fintype.ofFinite _
  let antichain := hrecall.decisionInformationAntichain
  obtain ⟨horizon, -, bounded⟩ := E.exists_pos_boundedHorizon
  have realize (profile : Profile F.sig.mixed) : F.mixed.play profile =
      M.runBehavioralTerminalFrom certificate
        (M.agentBehavior M.playedInformation fallback profile) E.initHistory :=
    M.informationAgentForm_mixed_play M.playedInformation fallback certificate bounded
      hrecall.actsOnceWhereItMatters (M.coversInformationSites_playedInformation horizon) profile
  -- the passage indicator of every decision agent
  let passage (final : E.History) (agent : M.InformationAgent M.playedInformation) : ℝ :=
    if decision : M.IsDecisionInfo agent.1 agent.2.1 then
      if (InformationSite.ancestor? M (⟨agent.2.1, decision⟩ : M.InformationSite agent.1)
          final).isSome then 1
      else 0
    else 0
  -- the reach of an agent as a polynomial in the part weights
  let reach (n : ℕ) (weights : ∀ agent, Part (groupOf agent) → ℝ)
      (agent : M.InformationAgent M.playedInformation) : ℝ :=
    GameTheory.payoff
      (F.substituteStrategies (component n))
      passage agent weights
  let mixtureOf (weights : ∀ agent, Part (groupOf agent) → ℝ)
      (inside : ∀ agent, weights agent ∈ simplexWeights (Part (groupOf agent)))
      (agent : M.InformationAgent M.playedInformation) : PMF (Part (groupOf agent)) :=
    PMF.ofSimplex (inside agent)
  have reachMass (n : ℕ) (weights : ∀ agent, Part (groupOf agent) → ℝ)
      (inside : ∀ agent, weights agent ∈ simplexWeights (Part (groupOf agent)))
      {i : ι} (site : M.InformationSite i) :
      reach n weights (M.agentAt site) =
        (M.informationMass (M.agentBehavior M.playedInformation fallback
          fun agent => (mixtureOf weights inside agent).bind (component n agent)) i
            site).toReal := by
    let G := F.substituteStrategies (component n)
    let _ (agent : M.InformationAgent M.playedInformation) : Fintype (G.sig.Strategy agent) :=
      Fintype.ofFinite (Part (groupOf agent))
    have : Finite G.sig.Outcome := inferInstanceAs (Finite E.History)
    have probsEq : probs G.sig (mixtureOf weights inside) = weights := by
      funext agent
      exact PMF.ofSimplex_toReal (inside agent)
    change GameTheory.payoff G passage (M.agentAt site) weights = _
    have key := payoff_probs (G.hasIntegrableUtility_of_finiteOutcome passage)
      (mixtureOf weights inside) (M.agentAt site)
    rw [probsEq] at key
    rw [key, GameForm.substituteStrategies_mixed_play, realize]
    change expect _ (fun final => passage final (M.agentAt site)) = _
    have decision : M.IsDecisionInfo i site.1 := site.2
    simp only [passage, decision, ↓reduceDIte]
    exact expect_passage M site (antichain i site) certificate _
  have mixtureFull (n : ℕ) (laws : ∀ agent, PMF (Part (groupOf agent))) :
      ∀ i (site : M.InformationSite i) (choice : M.Choice i site.1),
        choice ∈ (M.agentBehavior M.playedInformation fallback
          (fun agent => (laws agent).bind (component n agent)) i site.1).support := by
    intro i site choice
    rw [M.agentBehavior_at M.playedInformation fallback _ (M.agentAt site)]
    obtain ⟨part, member⟩ := (laws (M.agentAt site)).support_nonempty
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨part, member, componentFull n _ part choice⟩
  let importance (n : ℕ) (weights : ∀ agent, Part (groupOf agent) → ℝ)
      (agent : M.InformationAgent M.playedInformation) : ℝ :=
    if M.IsDecisionInfo agent.1 agent.2.1 then (reach n weights agent)⁻¹ else 0
  have importanceContinuous (n : ℕ) (agent : M.InformationAgent M.playedInformation) :
      ContinuousOn (fun weights => importance n weights agent)
        {weights | ∀ player, weights player ∈ simplexWeights (Part (groupOf player))} := by
    let G := F.substituteStrategies (component n)
    let _ (agent : M.InformationAgent M.playedInformation) : Fintype (G.sig.Strategy agent) :=
      Fintype.ofFinite (Part (groupOf agent))
    by_cases decision : M.IsDecisionInfo agent.1 agent.2.1
    · simp only [importance, decision, ↓reduceIte]
      refine ContinuousOn.inv₀ (f := fun weights => reach n weights agent)
        (continuous_payoff (F := G) (utility := passage) agent).continuousOn ?_
      intro weights inside
      have positive := reachMass n weights inside (i := agent.1) ⟨agent.2.1, decision⟩
      change reach n weights agent = _ at positive
      rw [positive]
      refine (ENNReal.toReal_pos ?_ ?_).ne'
      · exact (M.informationMass_pos_of_fullSupport _ (mixtureFull n _) agent.1
          ⟨agent.2.1, decision⟩).ne'
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top
          (M.informationMass_le_one _ agent.1 _ (antichain agent.1 ⟨agent.2.1, decision⟩))
    · simp only [importance, decision, ↓reduceIte]
      exact continuousOn_const
  choose weights optimal using fun n =>
    exists_bestResponses_with_shared_mixture_weights (F := F) groupOf (M.agentUtility payoff) (component n)
      (fun _ _ => payoffIntegrable_of_finite _ _) (importance n) (importanceContinuous n)
  let played (n : ℕ) : Profile F.sig.mixed := fun agent =>
    (weights n (groupOf agent)).bind (component n agent)
  let behavior (n : ℕ) := M.agentBehavior M.playedInformation fallback (played n)
  have full (n : ℕ) : ∀ i (site : M.InformationSite i) (choice : M.Choice i site.1),
      choice ∈ (behavior n i site.1).support :=
    mixtureFull n fun agent => weights n (groupOf agent)
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
  have term (n : ℕ) (alternative : ∀ p, PMF (Part p))
      (agent : M.InformationAgent M.playedInformation) :
      importance n (fun player part => (weights n (groupOf player) part).toReal) agent *
        (expectedUtility (M.agentUtility payoff) agent
            (F.mixed.play (Profile.update (sig := F.sig.mixed) (played n) agent
              ((alternative (groupOf agent)).bind (component n agent)))) -
          expectedUtility (M.agentUtility payoff) agent (F.mixed.play (played n))) =
      if decision : M.IsDecisionInfo agent.1 agent.2.1 then
        ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
            (payoff agent.1)).value
            (((sequence n).strategy agent.1).withLaw agent.2.1
              ((alternative (groupOf agent)).bind (component n agent))) -
          ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
            (payoff agent.1)).value ((sequence n).strategy agent.1)
      else 0 := by
    by_cases decision : M.IsDecisionInfo agent.1 agent.2.1
    · let site : M.InformationSite agent.1 := ⟨agent.2.1, decision⟩
      have mass := reachMass n (fun player part => (weights n (groupOf player) part).toReal)
        (fun player => PMF.toReal_mem_simplexWeights _) site
      have lawsEq : (fun player => (mixtureOf (fun player part =>
            (weights n (groupOf player) part).toReal)
          (fun player => PMF.toReal_mem_simplexWeights _) player).bind (component n player)) =
          played n := by
        funext player
        simp only [mixtureOf, PMF.ofSimplex_toReal_weights, played]
      have mass := mass.trans (congrArg
        (fun laws : Profile F.sig.mixed =>
          (M.informationMass (M.agentBehavior M.playedInformation fallback laws) agent.1 site).toReal)
        lawsEq)
      have gain := M.agentGain_eq_mass_mul hrecall fallback certificate payoff (played n)
        (full n) site ((alternative (groupOf agent)).bind (component n agent))
      have positive : 0 < (M.informationMass (behavior n) agent.1 site).toReal := by
        refine ENNReal.toReal_pos ?_ ?_
        · exact (M.informationMass_pos_of_fullSupport _ (full n) agent.1 site).ne'
        · exact ne_top_of_le_ne_top ENNReal.one_ne_top
            (M.informationMass_le_one _ agent.1 site (antichain agent.1 site))
      simp only [importance, decision, ↓reduceIte, ↓reduceDIte]
      change (reach n _ (M.agentAt site))⁻¹ * _ = _
      rw [mass]
      change _ * (expectedUtility (M.agentUtility payoff) (M.agentAt site) _ -
        expectedUtility (M.agentUtility payoff) (M.agentAt site) _) = _
      rw [gain, ← mul_assoc, inv_mul_cancel₀ positive.ne', one_mul]
      simp only [sequence, M.bayesAssessment_strategy]
      rfl
    · simp only [importance, decision, ↓reduceIte, ↓reduceDIte, zero_mul]
  refine ⟨weights, sequence, limit, index, sequenceStrategy, mixed, bayes, increasing, converges,
    converges.isSequentiallyConsistent antichain (fun n => mixed (index n))
      (fun n => bayes (index n)), fun n alternative p => ?_, ?_⟩
  · refine le_trans (le_of_eq (Finset.sum_congr rfl fun agent _ =>
      (term n alternative agent).symm)) ?_
    exact optimal n alternative p
  intro i site limitComponent componentConverges
  have strategyAt (n : ℕ) : (sequence n).strategy i site.1 =
      (weights n (groupOf (M.agentAt site))).bind (component n (M.agentAt site)) := by
    rw [sequenceStrategy]
    exact M.agentBehavior_at M.playedInformation fallback _ (M.agentAt site)
  constructor
  · obtain ⟨limitWeights, inner, innerIncreasing, weightsConverge⟩ :=
      exists_subseq_pmfConvergesPointwise
        (fun n => weights (index n) (groupOf (M.agentAt site)))
    refine ⟨limitWeights, ((converges.strategy i site).subseq innerIncreasing).unique ?_⟩
    have mixture := weightsConverge.bind
      (kernel := fun n => component (index (inner n)) (M.agentAt site))
      (fun part => (componentConverges part).subseq (increasing.comp innerIncreasing))
    have same : (fun n => (sequence (index (inner n))).strategy i site.1) =
        (fun n => (weights (index (inner n)) (groupOf (M.agentAt site))).bind
          (component (index (inner n)) (M.agentAt site))) :=
      funext fun n => strategyAt (index (inner n))
    rw [same]
    exact mixture
  · intro error vanishes nearOptimal alternative
    let total : ℝ := ∑ history : E.History, |payoff i history|
    have totalBound (history : E.History) : |payoff i history| ≤ total :=
      Finset.single_le_sum (fun other _ => abs_nonneg (payoff i other)) (Finset.mem_univ history)
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
    have alternativeConverges : PMFConvergesPointwise
        (fun n => alternative.bind (component (index n) (M.agentAt site)))
        (alternative.bind limitComponent) :=
      (pmfConvergesPointwise_const alternative).bind
        (kernel := fun n => component (index n) (M.agentAt site))
        (fun part => (componentConverges part).subseq increasing)
    have upper := (value _ _ (converges.strategy i)).add
      (vanishes.comp increasing.tendsto_atTop)
    rw [add_zero] at upper
    exact le_of_tendsto_of_tendsto' (value _ _ (withLawLimit _ _ alternativeConverges)) upper
      fun n => nearOptimal (index n) alternative

/-- **Consistent completion over component laws.** Every agent plays a mixture
of its fully supported components; the weights of all agents are chosen
together by rational completion. The assembled assessments are fully mixed
and Bayes consistent, and at every index each agent's weights are optimal among
its own component mixtures for the Bayes continuation value. One common
subsequence converges to a consistent assessment. At every decision site whose
components converge, the limit law is a mixture of the limit components and is
optimal among such mixtures. This specializes completion with shared mixture
weights to one agent per group. -/
theorem exists_consistent_component_completion (hrecall : M.DecisionRecall)
    (fallback : (i : ι) → M.Policy i) (certificate : E.WellFoundedHistories)
    (payoff : ι → E.History → ℝ)
    {Component : M.InformationAgent M.playedInformation → Type*}
    [∀ agent, Finite (Component agent)] [∀ agent, Nonempty (Component agent)]
    (component : ℕ → ∀ agent, Component agent →
      PMF ((M.agentForm fallback certificate).sig.Strategy agent))
    (componentFull : ∀ n agent part, FullSupport (component n agent part)) :
    ∃ (weights : ℕ → ∀ agent, PMF (Component agent))
      (sequence : ℕ → M.BehavioralAssessment) (limit : M.BehavioralAssessment)
      (index : ℕ → ℕ),
      (∀ n, (sequence n).strategy = M.agentBehavior M.playedInformation fallback
        fun agent => (weights n agent).bind (component n agent)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n)
        hrecall.decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent hrecall.decisionInformationAntichain ∧
      (∀ n i (site : M.InformationSite i) (alternative : PMF (Component (M.agentAt site))),
        ((sequence n).continuationContext certificate site (payoff i)).value
            (((sequence n).strategy i).withLaw site.1
              (alternative.bind (component n (M.agentAt site)))) ≤
          ((sequence n).continuationContext certificate site (payoff i)).value
            ((sequence n).strategy i)) ∧
      ∀ i (site : M.InformationSite i)
        (limitComponent : Component (M.agentAt site) → PMF (M.Choice i site.1)),
        (∀ part, PMFConvergesPointwise (fun n => component n (M.agentAt site) part)
          (limitComponent part)) →
        (∃ limitWeights : PMF (Component (M.agentAt site)),
          limit.strategy i site.1 = limitWeights.bind limitComponent) ∧
        ∀ alternative : PMF (Component (M.agentAt site)),
          (limit.continuationContext certificate site (payoff i)).value
              ((limit.strategy i).withLaw site.1 (alternative.bind limitComponent)) ≤
            (limit.continuationContext certificate site (payoff i)).value
              (limit.strategy i) := by
  classical
  obtain ⟨weights, sequence, limit, index, played, mixed, bayes, increasing, converges,
      consistent, aggregateOptimal, limitFacts⟩ :=
    M.exists_consistent_completion_with_shared_mixture_weights hrecall fallback certificate payoff (Part := Component)
      id component componentFull
  have stepOptimal (n : ℕ) (i : ι) (site : M.InformationSite i)
      (alternative : PMF (Component (M.agentAt site))) :
      ((sequence n).continuationContext certificate site (payoff i)).value
          (((sequence n).strategy i).withLaw site.1
            (alternative.bind (component n (M.agentAt site)))) ≤
        ((sequence n).continuationContext certificate site (payoff i)).value
          ((sequence n).strategy i) := by
    let componentSig : GameSignature (M.InformationAgent M.playedInformation) :=
      { Strategy := Component, Outcome := Unit }
    have single := aggregateOptimal n (Profile.update (sig := componentSig.mixed) (weights n) (M.agentAt site) alternative)
      (M.agentAt site)
    rw [show Finset.univ.filter (fun agent => id agent = M.agentAt site) = {M.agentAt site} by
      ext agent; simp, Finset.sum_singleton,
      show Profile.update (sig := componentSig.mixed) (weights n) (M.agentAt site) alternative
        (id (M.agentAt site)) = alternative from Profile.update_same ..] at single
    simp only [show M.IsDecisionInfo (M.agentAt site).1 (M.agentAt site).2.1 from site.2,
      ↓reduceDIte] at single
    exact sub_nonpos.mp single
  refine ⟨weights, sequence, limit, index, played, mixed, bayes, increasing, converges,
    consistent, stepOptimal, fun i site limitComponent componentConverges => ?_⟩
  obtain ⟨mixture, optimal⟩ := limitFacts i site limitComponent componentConverges
  exact ⟨mixture, optimal (fun _ => 0) tendsto_const_nhds fun n alternative => by
    rw [add_zero]
    exact stepOptimal n i site alternative⟩

end GameTheory.Protocol.InformationModel
