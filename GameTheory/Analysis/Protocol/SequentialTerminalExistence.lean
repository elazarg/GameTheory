/-
# Terminal sequential equilibrium from tight perturbed assessments

Uniform tightness supplies a common assessment subsequence. Bounded terminal
payoffs and converging whole-policy repairs pass approximate optimality to
its limit; fully mixed Bayes approximants witness its sequential consistency.
-/

import GameTheory.Analysis.Protocol.AssessmentCompactness
import GameTheory.Analysis.Protocol.SequentialTerminalLimits

noncomputable section

namespace GameTheory.Protocol.InformationModel

open Filter GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {E : ExecutionProtocol.{uι, us, ua} ι}
    (M : InformationModel.{uι, us, ua, up, uq, uk} E)
    [∀ i, Countable (M.InformationSite i)]

/-- A tight sequence of fully mixed Bayes assessments whose incumbents are
approximately optimal against every repaired whole-policy deviation has a fuel-free terminal
sequential-equilibrium limit. The hypotheses explicitly supply the perturbed
assessments and their approximate optimality; this theorem extracts their
common limit and proves its two assessment properties. -/
theorem exists_sequentialEquilibriumTerminal_of_uniformlyTight
    (certificate : E.WellFoundedPlay)
    (hantichain : M.DecisionInformationAntichain)
    (sequence : ℕ → M.BehavioralAssessment)
    (hstrategyTight : ∀ i (site : M.InformationSite i),
      UniformlyTight (fun n => (sequence n).strategy i site.1))
    (hbeliefTight : ∀ i (site : M.InformationSite i),
      UniformlyTight (fun n => (sequence n).belief i site))
    (hfull : ∀ n, (sequence n).IsFullyMixed)
    (hbayes : ∀ n, BehavioralAssessment.IsBayesConsistent M
      (sequence n) hantichain)
    (repair : ℕ → (i : ι) → M.BehavioralPolicy i → M.BehavioralPolicy i)
    (hrepair : ∀ i alternative (site : M.InformationSite i),
      PMFConvergesPointwise
        (fun n => repair n i alternative site.1) (alternative site.1))
    (payoff : ι → E.History → ℝ)
    (bound : ι → ℝ) (hC : ∀ i, 0 ≤ bound i)
    (hbound : ∀ i final, E.terminal final.state → |payoff i final| ≤ bound i)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hoptimal : ∀ n i site alternative,
      (((sequence n).terminalContinuationContext
        certificate site (payoff i)).value (repair n i alternative)
        ((sequence n).terminalContinuationContext_integrable_of_bounded_terminal
          certificate site (payoff i) (bound i)
          (hbound i) (repair n i alternative))) ≤
      (((sequence n).terminalContinuationContext
        certificate site (payoff i)).value ((sequence n).strategy i)
        ((sequence n).terminalContinuationContext_integrable_of_bounded_terminal
          certificate site (payoff i) (bound i)
          (hbound i) ((sequence n).strategy i))) + error n) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.IsSequentiallyRationalTerminal certificate payoff ∧
        assessment.IsSequentiallyConsistent hantichain := by
  obtain ⟨assessment, subseq, hsubseq, hconvergence⟩ :=
    M.exists_subseq_behavioralAssessmentConvergesPointwise_atSites_of_uniformlyTight
      sequence hstrategyTight hbeliefTight
  refine ⟨assessment, ?_, ?_⟩
  · exact BehavioralAssessment.isSequentiallyRationalTerminal_of_converging_deviations_bounded
      M
      certificate (fun i site => hconvergence.strategy i site)
      (fun i site => hconvergence.belief i site)
      (fun n i alternative => repair (subseq n) i alternative)
      (fun i alternative site => (hrepair i alternative site).subseq hsubseq)
      payoff bound hC hbound (fun n => error (subseq n))
      (herror.comp hsubseq.tendsto_atTop)
      (fun n i site alternative => hoptimal (subseq n) i site alternative)
  · exact hconvergence.isSequentiallyConsistent hantichain
      (fun n => hfull (subseq n)) (fun n => hbayes (subseq n))

end GameTheory.Protocol.InformationModel
