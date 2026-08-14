/-
Hostile joint-posterior regression.

Two players commonly learn a fair Boolean state.  Their joint posterior law
supports two distinct belief profiles, is feasible through the common-state
coupling, and therefore has Bayes-plausible marginals for both players.
-/

import GameTheory.Mechanism.JointFeasiblePosteriors

noncomputable section

namespace GameTheory.Tests.JointFeasiblePosteriors

open Probability

def prior : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

def law : JointPosteriorLaw Bool Bool :=
  JointPosteriorLaw.fullRevelation prior

def falseBeliefs : Bool → FinDist Bool :=
  fun _ => FinDist.pure false

def trueBeliefs : Bool → FinDist Bool :=
  fun _ => FinDist.pure true

theorem law_isFeasible : law.IsFeasible prior :=
  JointPosteriorLaw.isFeasible_fullRevelation prior

theorem law_isBayesPlausible : law.IsBayesPlausible prior :=
  law_isFeasible.isBayesPlausible

theorem law_supports_two_belief_profiles :
    falseBeliefs ∈ law.support ∧ trueBeliefs ∈ law.support := by
  constructor
  · rw [law, JointPosteriorLaw.fullRevelation, FinDist.support_map]
    refine ⟨false, ?_, rfl⟩
    rw [← FinDist.prob_pos_iff]
    norm_num [prior, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
  · rw [law, JointPosteriorLaw.fullRevelation, FinDist.support_map]
    refine ⟨true, ?_, rfl⟩
    rw [← FinDist.prob_pos_iff]
    norm_num [prior, FinDist.prob_mix, FinDist.prob_pure_eq_ite]

theorem player_false_marginal_isBayesPlausible :
    (law.agentMarginal false).IsBayesPlausible prior :=
  law_isFeasible.agentMarginal_isBayesPlausible false

theorem player_true_marginal_isBayesPlausible :
    (law.agentMarginal true).IsBayesPlausible prior :=
  law_isFeasible.agentMarginal_isBayesPlausible true

end GameTheory.Tests.JointFeasiblePosteriors
