module

/-
# Finite-history conditional-probability PBE existence

Finite-history sequential existence supplies both optimal continuation play
and a joint perturbation limit. The latter yields a common conditional system
on terminal histories, with no separate equilibrium or CPS witness assumed.
-/

public import GameTheory.Analysis.Protocol.ConditionalPBE
public import GameTheory.Analysis.Protocol.SequentialExistence

@[expose] public section

noncomputable section

namespace GameTheory.Protocol.InformationModel

universe uι us ua up uq uk

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {E : ExecutionProtocol.{uι, us, ua} ι}
    (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Finitely many legal histories, explicit chance and recall at decision sites
supply a conditional-probability perfect Bayesian equilibrium. States, raw action and
information carriers need not be finite; the fallback inhabits legal menus. -/
theorem exists_conditionalPBE [Finite E.History]
    (hrecall : M.DecisionRecall) (fallback : (i : ι) → M.Policy i)
    (payoff : ι → E.History → ℝ) (certificate : E.WellFoundedHistories)
    (explicitChance : E.HasExplicitChance) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.IsConditionalPBE M certificate payoff := by
  obtain ⟨assessment, rational, consistent⟩ :=
    M.exists_sequentialEquilibrium hrecall fallback payoff certificate
  exact ⟨assessment, rational,
    consistent.isConditionalProbabilityConsistent M hrecall.decisionInformationAntichain
      certificate, explicitChance⟩

end GameTheory.Protocol.InformationModel
