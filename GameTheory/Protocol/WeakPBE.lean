module

/-
# Weak perfect Bayesian equilibrium

A weak perfect Bayesian equilibrium is a behavioral assessment that is
sequentially rational on terminal play and obeys Bayes' rule at every decision
information site reached with positive probability. At an unreached site its
belief remains supported on that information set, and the continuation policy
must still be optimal given that belief. No consistency between different
unreached sites is imposed.

The qualifier `Weak` is essential: this condition need not imply proper-subgame
perfection. Stronger perfect Bayesian notions impose additional restrictions
on off-path beliefs; sequential equilibrium uses limits of fully mixed Bayes
assessments.
-/

public import GameTheory.Protocol.BehavioralBayes
public import GameTheory.Protocol.BehavioralTerminal

@[expose] public section

noncomputable section

namespace GameTheory.Protocol.InformationModel

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι} {M : InformationModel E}
    [E.FiniteMovers] [DecidableEq ι]

/-- Whole-policy sequential rationality and Bayes' rule at positive-mass sites.
Beliefs at zero-mass sites are constrained only by their information-history
carrier and sequential rationality. -/
def BehavioralAssessment.IsWeakPBE (A : M.BehavioralAssessment)
    (antichain : M.DecisionInformationAntichain)
    (certificate : E.WellFoundedHistories) (payoff : ι → E.History → ℝ) : Prop :=
  A.IsSequentiallyRational certificate payoff ∧
    BehavioralAssessment.IsBayesConsistent M A antichain

/-- The definition uses the existing terminal rationality and Bayes predicates. -/
theorem BehavioralAssessment.isWeakPBE_iff (A : M.BehavioralAssessment)
    (antichain : M.DecisionInformationAntichain)
    (certificate : E.WellFoundedHistories) (payoff : ι → E.History → ℝ) :
    A.IsWeakPBE antichain certificate payoff ↔
      A.IsSequentiallyRational certificate payoff ∧
        BehavioralAssessment.IsBayesConsistent M A antichain :=
  Iff.rfl

end GameTheory.Protocol.InformationModel
