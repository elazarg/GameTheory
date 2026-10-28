module

/-
# Finite-history weak perfect Bayesian equilibrium existence

Decision recall and finitely many legal histories supply a sequential
equilibrium. Its beliefs obey Bayes' rule at reached sites, giving a weak PBE
without an additional fixed-point construction.
-/

public import GameTheory.Analysis.Protocol.WeakPBE
public import GameTheory.Analysis.Protocol.SequentialExistence

@[expose] public section

noncomputable section

namespace GameTheory.Protocol.InformationModel

universe uι us ua up uq uk

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {E : ExecutionProtocol.{uι, us, ua} ι}
    (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Finite-history decision-recall protocols with total legal fallback policies
have a weak PBE. No finite state, action, or raw information carrier is needed. -/
theorem exists_weakPBE [Finite E.History]
    (hrecall : M.DecisionRecall) (fallback : (i : ι) → M.Policy i)
    (payoff : ι → E.History → ℝ) (certificate : E.WellFoundedHistories) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.IsWeakPBE hrecall.decisionInformationAntichain certificate payoff := by
  obtain ⟨assessment, rational, consistent⟩ :=
    M.exists_sequentialEquilibrium hrecall fallback payoff certificate
  exact ⟨assessment, rational, consistent.isBayesConsistent hrecall.decisionInformationAntichain⟩

end GameTheory.Protocol.InformationModel
