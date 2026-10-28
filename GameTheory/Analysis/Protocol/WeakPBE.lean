module

/-
# Weak perfect Bayesian equilibrium and root incentives

Sequential consistency forces Bayes' rule at reached information sites when
their history fibers are finite. The rationality requirement is the same
whole-policy terminal comparison in both concepts. With decision recall,
weak PBE also implies every behavioral root comparison for a utility factoring
through a finite observation carrier.
-/

public import GameTheory.Protocol.WeakPBE
public import GameTheory.Analysis.Protocol.BeliefTransport

@[expose] public section

noncomputable section

namespace GameTheory.Protocol.InformationModel

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι} {M : InformationModel E}
    [E.FiniteMovers] [DecidableEq ι]

/-- Sequential equilibrium is a weak PBE. The finite-fiber hypothesis is the
one needed by the existing limit-to-Bayes theorem. -/
theorem BehavioralAssessment.IsSequentialEquilibrium.isWeakPBE
    {A : M.BehavioralAssessment}
    [∀ who (site : M.InformationSite who), Finite (M.InformationHistory who site.1)]
    (antichain : M.DecisionInformationAntichain)
    (certificate : E.WellFoundedHistories) (payoff : ι → E.History → ℝ)
    (equilibrium : A.IsSequentialEquilibrium antichain certificate payoff) :
    A.IsWeakPBE antichain certificate payoff :=
  ⟨equilibrium.1, equilibrium.2.isBayesConsistent antichain⟩

/-- A weak PBE respects every behavioral root incentive comparison under
decision recall and a finite observation of terminal utility. No finite
history or information-fiber hypothesis is needed for this direction. -/
theorem BehavioralAssessment.IsWeakPBE.holds_root
    {Observation : Type*} [Fintype Observation] {A : M.BehavioralAssessment}
    (hrecall : M.DecisionRecall) (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation) (utility : Observation → ι → ℝ)
    (equilibrium : A.IsWeakPBE hrecall.decisionInformationAntichain certificate
      (fun who history => utility (observe history) who)) :
    ∀ who deviation,
      (M.behavioralRootComparison certificate observe A.strategy who deviation).Holds
        (utility · who) :=
  M.holds_root_of_assessment certificate observe A hrecall equilibrium.2 utility
    ((M.isSequentiallyRational_iff_holds certificate observe A utility).mp equilibrium.1)

end GameTheory.Protocol.InformationModel
