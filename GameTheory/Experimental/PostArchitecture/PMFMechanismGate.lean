/-
# EXP-139: ordinary-PMF mechanism guard gate

Infinite posterior splitting, cancellation in the principal's net payoff,
message-local integration, and undefined actual alternatives exercise the
mechanism interfaces without imposing finite outcome carriers.
-/

import GameTheory.Mechanism.PosteriorSignals
import GameTheory.Mechanism.PrincipalAgent
import GameTheory.Mechanism.InformationDesign
import GameTheory.Experimental.PostArchitecture.PMFRestorationProbe

noncomputable section

namespace GameTheory.Experimental.PMFMechanismGate

open GameTheory GameTheory.Mechanism GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration

private theorem exploding_not_integrable :
    ¬ PayoffIntegrable geometric exploding := by
  intro h
  apply exploding_not_summable
  have hnonneg (n : ℕ) : 0 ≤ exploding n := by
    unfold exploding
    positivity
  simpa only [PayoffIntegrable, abs_of_nonneg (hnonneg _)] using h

/-- A fully revealing posterior law splits an infinite-support prior. -/
def posteriorLaw : PosteriorLaw ℕ := PosteriorLaw.fullRevelation geometric

theorem posteriorLaw_infinite_support : posteriorLaw.support.Infinite := by
  have hpure : Function.Injective (PMF.pure : ℕ → PMF ℕ) := by
    intro first second heq
    by_contra hne
    have hmass := congrArg (fun belief : PMF ℕ => belief first) heq
    simp [PMF.pure_apply, hne] at hmass
  rw [posteriorLaw, PosteriorLaw.fullRevelation,
    PMF.support_map, geometric_support]
  simpa only [Set.image_univ] using Set.infinite_range_of_injective hpure

theorem posteriorLaw_isBayesPlausible :
    posteriorLaw.IsBayesPlausible geometric :=
  PosteriorLaw.isBayesPlausible_fullRevelation geometric

theorem posteriorLaw_has_signal :
    ∃ (signal : SignalStructure ℕ (PMF ℕ))
      (posterior : PMF ℕ → PMF ℕ),
      signal.IsPosteriorAssignment geometric posterior ∧
        signal.inducedPosteriorLaw geometric posterior = posteriorLaw :=
  SignalStructure.exists_signalStructure_of_isBayesPlausible
    geometric posteriorLaw posteriorLaw_isBayesPlausible

/-- Reward and full commission each diverge, while their net cancels. -/
def principal : PrincipalAgent Unit ℕ where
  outcomeLaw _ := geometric
  reward := exploding
  cost _ := 0

theorem principal_reward_undefined :
    ¬ PayoffIntegrable (principal.outcomeLaw ()) principal.reward :=
  exploding_not_integrable

theorem principal_payment_undefined :
    ¬ PayoffIntegrable (principal.outcomeLaw ())
      (principal.linearPayment 1) := by
  have hpayment : principal.linearPayment 1 = exploding := by
    funext n
    simp [principal, PrincipalAgent.linearPayment]
  rw [hpayment]
  exact exploding_not_integrable

theorem principal_net_defined :
    ∃ hnet : PayoffIntegrable (principal.outcomeLaw ())
        (fun outcome => principal.reward outcome -
          principal.linearPayment 1 outcome),
      principal.principalUtility (principal.linearPayment 1) () hnet = 0 :=
  principal.principalUtility_linearPayment_one ()

/-- The `true` message occurs only at state zero. -/
def localSignal : SignalStructure ℕ Bool where
  kernel n := PMF.pure (decide (n = 0))

theorem local_true_message_positive :
    0 < (localSignal.messageMarginal geometric true).toReal := by
  have hsupport : true ∈ (localSignal.messageMarginal geometric).support := by
    rw [localSignal.messageMarginal_eq_bind, PMF.support_bind]
    apply Set.mem_iUnion₂.mpr
    refine ⟨0, ?_, ?_⟩
    · rw [geometric_support]
      trivial
    · simp [localSignal]
  exact ENNReal.toReal_pos
    ((localSignal.messageMarginal geometric).mem_support_iff true |>.mp hsupport)
    ((localSignal.messageMarginal geometric).apply_ne_top true)

def localProblem : PersuasionProblem ℕ Bool Bool where
  prior := geometric
  signal := localSignal
  receiverUtility n action := if action then exploding n else 0
  senderUtility _ _ := 0

theorem local_weighted_score_integrable :
    PayoffIntegrable localProblem.prior
      (localProblem.receiverWeighted true true) := by
  apply payoffIntegrable_of_bounded _ _ (C := 2)
  intro n
  by_cases hn : n = 0
  · subst n
    norm_num [localProblem, localSignal,
      PersuasionProblem.receiverWeighted, exploding, PMF.pure_apply]
  · simp [localProblem, localSignal,
      PersuasionProblem.receiverWeighted, PMF.pure_apply, hn]

theorem local_unweighted_payoff_undefined :
    ¬ PayoffIntegrable localProblem.prior
      (fun n => localProblem.receiverUtility n true) := by
  simpa only [localProblem, reduceIte] using exploding_not_integrable

/-- The safe action cannot be optimal when its actual alternative diverges. -/
def undefinedAlternative : PersuasionProblem ℕ Unit Bool where
  prior := geometric
  signal := SignalStructure.uninformative ℕ
  receiverUtility n action := if action then exploding n else 0
  senderUtility _ _ := 0

theorem undefined_receiver_alternative_refutes_optimality :
    ¬ undefinedAlternative.IsReceiverOptimal () false := by
  rintro ⟨hscore, _⟩
  apply exploding_not_integrable
  have hweighted :
      undefinedAlternative.receiverWeighted () true = exploding := by
    funext n
    simp [undefinedAlternative, SignalStructure.uninformative,
      PersuasionProblem.receiverWeighted, PMF.pure_apply]
  have htrue := hscore true
  rw [hweighted] at htrue
  exact htrue

/-- An undefined payment at a real alternative refutes agent optimality. -/
def agentAlternative : PrincipalAgent Bool ℕ where
  outcomeLaw action := if action then geometric else PMF.pure 0
  reward _ := 0
  cost _ := 0

theorem undefined_agent_alternative_refutes_incentives :
    ¬ agentAlternative.IsIncentivized exploding false := by
  rintro ⟨hpayment, _⟩
  apply exploding_not_integrable
  simpa [agentAlternative] using hpayment true

end GameTheory.Experimental.PMFMechanismGate
