/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

import GameTheory.Analysis.Protocol.ComponentCompletion
import GameTheory.Analysis.Protocol.LocalSimulationLimit

/-! # Shared component completion with copied sites

Shared pool weights yield a consistent assessment subsequence. To obtain a
sequential equilibrium, free sites must have spanning limit component menus
and vanishing member gains; copied sites must have vanishing local gains.
Aggregate pool optimality is available to prove these certificates, but does
not replace them. Observed-law preservation is a separate certificate.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {Player : Type*} [Fintype Player] [DecidableEq Player]
  {T : ExecutionProtocol Player} (N : InformationModel T)
  [Fintype T.History] [∀ who, DecidableEq (N.InfoState who)]

open Classical in
/-- Complete shared pool weights, retaining their assembled strategies and a
common assessment subsequence. A certificate only needs to control local
lotteries at copied sites and component mixtures at free sites. At free sites,
the limiting menu must span all legal lotteries. The certificate may use the
aggregate pooled optimality supplied by completion; individual member bounds
remain explicit. No observation-preservation claim follows from shared weights. -/
theorem exists_sequentialEquilibrium_of_pooled_local_certificates
    (decisionRecall : N.DecisionRecall) (fallback : ∀ who, N.Policy who)
    (certificate : T.WellFoundedHistories) (payoff : Player → T.History → ℝ)
    {Pool : Type*} [Finite Pool] [DecidableEq Pool]
    (pool : N.InformationAgent N.playedInformation → Pool)
    {Part : Pool → Type*} [∀ p, Finite (Part p)] [∀ p, Nonempty (Part p)]
    (component : ℕ → ∀ agent, Part (pool agent) →
      PMF ((N.agentForm fallback certificate).sig.Strategy agent))
    (componentFull : ∀ n agent part, FullSupport (component n agent part))
    (copied : ∀ who, N.InformationSite who → Prop)
    (limitComponent : ∀ who (site : N.InformationSite who),
      Part (pool (N.agentAt site)) → PMF (N.Choice who site.1))
    (componentConverges : ∀ who site, ¬ copied who site → ∀ part,
      PMFConvergesPointwise (fun n => component n (N.agentAt site) part)
        (limitComponent who site part))
    (spanning : ∀ who site, ¬ copied who site → ∀ law : PMF (N.Choice who site.1),
      ∃ alternative : PMF (Part (pool (N.agentAt site))),
        alternative.bind (limitComponent who site) = law)
    (certify : ∀ (weights : ℕ → ∀ p, PMF (Part p))
        (sequence : ℕ → N.BehavioralAssessment),
      (∀ n, (sequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (pool agent)).bind (component n agent)) →
      (∀ n, (sequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (sequence n)
        decisionRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (Part p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pool agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                (payoff agent.1)).value
                (((sequence n).strategy agent.1).withLaw agent.2.1
                  ((alternative (pool agent)).bind (component n agent))) -
              ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                (payoff agent.1)).value ((sequence n).strategy agent.1)
          else 0) ≤ 0) →
      ∃ error : ℕ → ∀ who, N.InformationSite who → ℝ,
        (∀ who site, Tendsto (fun n => error n who site) atTop (nhds 0)) ∧
        (∀ n who site, copied who site → ∀ law,
          ((sequence n).continuationContext certificate site (payoff who)).value
              (((sequence n).strategy who).withLaw site.1 law) -
            ((sequence n).continuationContext certificate site (payoff who)).value
              ((sequence n).strategy who) ≤ error n who site) ∧
        (∀ n who site, ¬ copied who site →
          ∀ alternative : PMF (Part (pool (N.agentAt site))),
            ((sequence n).continuationContext certificate site (payoff who)).value
                (((sequence n).strategy who).withLaw site.1
                  (alternative.bind (component n (N.agentAt site)))) ≤
              ((sequence n).continuationContext certificate site (payoff who)).value
                ((sequence n).strategy who) + error n who site)) :
    ∃ (weights : ℕ → ∀ p, PMF (Part p))
      (sequence : ℕ → N.BehavioralAssessment) (limit : N.BehavioralAssessment)
      (index : ℕ → ℕ),
      (∀ n, (sequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (pool agent)).bind (component n agent)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent N (sequence n)
        decisionRecall.decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain certificate payoff ∧
      (∀ who site, ¬ copied who site →
        ∃ limitWeights : PMF (Part (pool (N.agentAt site))),
          limit.strategy who site.1 = limitWeights.bind (limitComponent who site)) := by
  classical
  obtain ⟨weights, sequence, limit, index, played, mixed, bayes, increasing,
      converges, consistent, pooled, limitFacts⟩ :=
    N.exists_consistent_pooled_completion decisionRecall fallback certificate payoff pool
      component componentFull
  obtain ⟨error, vanishes, copiedBound, memberBound⟩ :=
    certify weights sequence played mixed bayes pooled
  refine ⟨weights, sequence, limit, index, played, mixed, bayes, increasing, converges, ?_, ?_⟩
  · apply converges.sequentialEquilibrium_of_copied_gain_bounds decisionRecall certificate payoff
      copied consistent (fun n who site _ => error (index n) who site)
      (fun who site _ _ => (vanishes who site).comp increasing.tendsto_atTop)
      (fun n who site kept law => copiedBound (index n) who site kept law)
    intro who site free law
    obtain ⟨alternative, represents⟩ := spanning who site free law
    obtain ⟨_, optimal⟩ := limitFacts who site (limitComponent who site)
      (componentConverges who site free)
    rw [← represents]
    exact optimal (fun n => error n who site) (vanishes who site)
      (fun n candidate => memberBound n who site free candidate) alternative
  · intro who site free
    exact (limitFacts who site (limitComponent who site)
      (componentConverges who site free)).1

end GameTheory.Protocol.InformationModel
