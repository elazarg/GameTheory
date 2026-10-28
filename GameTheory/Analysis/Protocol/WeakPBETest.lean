module

/-
# Weak PBE at a reached hidden-information site

Nature's fair hidden bit gives a genuinely mixed equilibrium for a nonconstant
matching payoff. A dogmatic assessment fails rationality under that payoff.
With zero payoff rationality holds automatically, but the same dogmatic belief
still fails Bayes' rule at the reached site, independently of rationality.
-/

public import GameTheory.Analysis.Protocol.WeakPBE
public import GameTheory.Analysis.Protocol.EFGTest
public import GameTheory.Analysis.Protocol.WeakPBEExistence
public import GameTheory.Analysis.Protocol.DecisionRecallExistenceTest
public import GameTheory.Languages.EFG.WeakPBE

@[expose] public section

noncomputable section

namespace GameTheory.Tests.WeakPBE

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Tests.EFG

local instance : Fintype execution.History := game.historyFintype

/-- The nonconstant matching-payoff sequential equilibrium is a weak PBE via
the analytic refinement theorem, with the same assessment and payoff. -/
theorem matching_isWeakPBE :
    game.IsWeakPBE information_decisionInformationAntichain fullyMixedAssessment
      wellFoundedHistories matchingPayoff :=
  InformationModel.BehavioralAssessment.IsSequentialEquilibrium.isWeakPBE
    information_decisionInformationAntichain wellFoundedHistories matchingPayoff
    fullyMixedAssessment_isSequentialEquilibrium_matchingPayoff

/-- A profitable continuation-policy replacement refutes weak PBE even before
checking Bayes consistency. -/
theorem irrational_not_isWeakPBE :
    ¬ wrongAssessment.IsWeakPBE information_decisionInformationAntichain
      wellFoundedHistories matchingPayoff :=
  fun equilibrium => wrongAssessment_not_isSequentiallyRational_matchingPayoff equilibrium.1

/-- Preserve the fully mixed strategy and replace only the hidden-state belief
by certainty of `true`. The site remains reached with mass one. -/
def nonBayesianAssessment : information.BehavioralAssessment where
  strategy := fullyMixedBehavioralProfile
  belief := trueBelief

theorem nonBayesian_mass :
    information.informationMass nonBayesianAssessment.strategy .player actingSite = 1 :=
  informationMass_fullyMixed_acting

/-- This assessment is rational for zero payoff, isolating the Bayes condition
from the rationality condition. -/
theorem nonBayesian_isSequentiallyRational_zero :
    nonBayesianAssessment.IsSequentiallyRational wellFoundedHistories (fun _ _ => 0) :=
  nonBayesianAssessment.isSequentiallyRational_zero wellFoundedHistories

/-- Positive reach forces probability one half on `false`; the dogmatic belief
assigns zero there and therefore fails Bayes consistency. -/
theorem nonBayesian_not_isBayesConsistent :
    ¬ InformationModel.BehavioralAssessment.IsBayesConsistent information
      nonBayesianAssessment information_decisionInformationAntichain := by
  intro consistent
  have positive : 0 < information.informationMass
      nonBayesianAssessment.strategy .player actingSite := by
    rw [nonBayesian_mass]
    norm_num
  have equality := consistent .player actingSite positive (decisionInformationHistory false)
  change (PMF.pure (decisionInformationHistory true)) (decisionInformationHistory false) =
    information.historyReachWeight fullyMixedBehavioralProfile
      (decisionInformationHistory false).1 /
        information.informationMass fullyMixedBehavioralProfile .player actingSite at equality
  rw [historyReachProbability_decision, informationMass_fullyMixed_acting] at equality
  rw [PMF.pure_apply, ite_eq_right decisionInformationHistory_ne] at equality
  norm_num [ENNReal.ofReal_eq_zero] at equality

/-- Sequential rationality alone does not give weak PBE at a reached site. -/
theorem nonBayesian_not_isWeakPBE_zero :
    ¬ nonBayesianAssessment.IsWeakPBE information_decisionInformationAntichain
      wellFoundedHistories (fun _ _ => 0) :=
  fun equilibrium => nonBayesian_not_isBayesConsistent equilibrium.2

end GameTheory.Tests.WeakPBE

namespace GameTheory.Tests.WeakPBEFiniteExistence

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Tests.Randomized
open GameTheory.Analysis.Protocol.DecisionRecallExistenceTest

/-- Finite existence applies to a nonconstant voting payoff even though the
model forgets its own action after voting and fails perfect recall. -/
theorem exists_weakPBE :
    ∃ assessment : singleModel.BehavioralAssessment,
      assessment.IsWeakPBE single_decisionRecall.decisionInformationAntichain
        once.wellFoundedHistories_of_fintype payoff :=
  singleModel.exists_weakPBE single_decisionRecall fallback payoff _

/-- The root utility observes only the final voting state. -/
def observedUtility (state : Single) (_ : Unit) : ℝ :=
  match state with
  | .voted .up => 1
  | _ => 0

/-- The constructed weak PBE obeys all whole-policy comparisons at the root,
through the finite-observation root-incentive bridge. -/
theorem exists_root_obedient_weakPBE :
    ∃ assessment : singleModel.BehavioralAssessment,
      assessment.IsWeakPBE single_decisionRecall.decisionInformationAntichain
        once.wellFoundedHistories_of_fintype payoff ∧
      ∀ who deviation,
        (singleModel.behavioralRootComparison once.wellFoundedHistories_of_fintype
          (fun history => history.state) assessment.strategy who deviation).Holds
            (observedUtility · who) := by
  obtain ⟨assessment, equilibrium⟩ := exists_weakPBE
  exact ⟨assessment, equilibrium,
    equilibrium.holds_root single_decisionRecall once.wellFoundedHistories_of_fintype
      (fun history => history.state) observedUtility⟩

end GameTheory.Tests.WeakPBEFiniteExistence
