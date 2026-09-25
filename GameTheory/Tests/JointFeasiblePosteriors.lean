/-
Hostile joint-posterior regression.

Two players commonly learn a fair Boolean state.  Their joint posterior law
supports two distinct belief profiles, is feasible through the common-state
coupling, and therefore has Bayes-plausible marginals for both players.
-/

import GameTheory.Mechanism.JointFeasiblePosteriors
import GameTheory.Math.Probability.ExpectationMixture

noncomputable section

namespace GameTheory.Tests.JointFeasiblePosteriors

open GameTheory.Math.Probability

def prior : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure false) (PMF.pure true)

def law : JointPosteriorLaw Bool Bool :=
  JointPosteriorLaw.fullRevelation prior

def falseBeliefs : Bool → PMF Bool :=
  fun _ => PMF.pure false

def trueBeliefs : Bool → PMF Bool :=
  fun _ => PMF.pure true

theorem law_isFeasible : law.IsFeasible prior :=
  JointPosteriorLaw.isFeasible_fullRevelation prior

theorem law_isBayesPlausible : law.IsBayesPlausible prior :=
  law_isFeasible.isBayesPlausible

theorem law_supports_two_belief_profiles :
    falseBeliefs ∈ law.support ∧ trueBeliefs ∈ law.support := by
  constructor
  · rw [law, JointPosteriorLaw.fullRevelation, PMF.support_map]
    refine ⟨false, ?_, rfl⟩
    show prior false ≠ 0
    norm_num [prior, mix_apply, PMF.pure_apply]
  · rw [law, JointPosteriorLaw.fullRevelation, PMF.support_map]
    refine ⟨true, ?_, rfl⟩
    show prior true ≠ 0
    norm_num [prior, mix_apply, PMF.pure_apply]

theorem player_false_marginal_isBayesPlausible :
    (law.agentMarginal false).IsBayesPlausible prior :=
  law_isFeasible.agentMarginal_isBayesPlausible false

theorem player_true_marginal_isBayesPlausible :
    (law.agentMarginal true).IsBayesPlausible prior :=
  law_isFeasible.agentMarginal_isBayesPlausible true

end GameTheory.Tests.JointFeasiblePosteriors
