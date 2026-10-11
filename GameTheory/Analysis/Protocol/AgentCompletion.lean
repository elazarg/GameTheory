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

import GameTheory.Analysis.Protocol.ComponentCompletion

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type*} [DecidableEq ι] {E : ExecutionProtocol ι}
  (M : InformationModel E) [Fintype E.History] [∀ i, DecidableEq (M.InfoState i)]
variable [Fintype ι]

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
  have inhabited (agent : M.InformationAgent M.playedInformation) : Nonempty (F.sig.Strategy agent) :=
    M.nonempty_choice_of_played agent.2.2
  let component (n : ℕ) := pinnedTrembleComponent (F := F) free (pinned n) reference
    (epsilon n) (positive n).le (small n).le
  have full : ∀ n agent part, FullSupport (component n agent part) := by
    intro n agent part choice
    by_cases active : agent ∈ free
    · change choice ∈ (if agent ∈ free then mix _ _ _ _ _ else _).support
      rw [ite_eq_left active]
      exact mem_support_mix_left _ _ _ (positive n) (referenceFull agent choice)
    · change choice ∈ (if agent ∈ free then _ else pinned n agent).support
      rw [ite_eq_right active]
      exact pinnedFull n agent active choice
  obtain ⟨residual, sequence, limit, index, played, mixed, bayes, increasing, converges,
      consistent, _, limitFacts⟩ :=
    M.exists_consistent_component_completion hrecall fallback certificate payoff component full
  refine ⟨residual, sequence, limit, index, ?_, mixed, bayes, increasing, converges, consistent, ?_⟩
  · intro n
    rw [played]
    apply congrArg (M.agentBehavior M.playedInformation fallback)
    funext agent
    exact bind_pinnedTrembleComponent free (pinned n) reference (residual n) (epsilon n)
      (positive n).le (small n).le agent
  · intro i site active law
    have componentConverges (part : F.sig.Strategy (M.agentAt site)) :
        PMFConvergesPointwise (fun n => component n (M.agentAt site) part) (PMF.pure part) := by
      have same : (fun n => component n (M.agentAt site) part) =
          (fun n => mix (epsilon n) (positive n).le (small n).le (reference (M.agentAt site)) (PMF.pure part)) := by
        funext n
        exact ite_eq_left active
      rw [same]
      exact pmfConvergesPointwise_mix_zero epsilon (fun n => (positive n).le)
        (fun n => (small n).le) vanishes _ _
    obtain ⟨_, optimal⟩ := limitFacts i site (fun part => PMF.pure part) componentConverges
    have bound := optimal law
    exact ((congrArg (fun candidate : PMF (M.Choice i site.1) =>
      (limit.continuationContext certificate site (payoff i)).value
        ((limit.strategy i).withLaw site.1 candidate)) (PMF.bind_pure law)).symm).le.trans bound

end GameTheory.Protocol.InformationModel
