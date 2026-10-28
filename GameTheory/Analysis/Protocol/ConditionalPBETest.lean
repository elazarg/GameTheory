module

/-
# Conditional-probability PBE consumers

A hidden fair bit and a nonconstant matching payoff exercise the refinement
from sequential equilibrium. A one-vote game also consumes finite existence
under decision recall while failing perfect recall after play has stopped.
-/

public import GameTheory.Analysis.Protocol.ConditionalPBEExistence
public import GameTheory.Analysis.Protocol.EFGTest
public import GameTheory.Analysis.Protocol.DecisionRecallExistenceTest

@[expose] public section

noncomputable section

namespace GameTheory.Tests.ConditionalPBE

open GameTheory GameTheory.Protocol GameTheory.Tests.EFG

local instance : Fintype execution.History := game.historyFintype

/-- Nature's hidden draw is explicit; the player's decision has a pure successor. -/
theorem hiddenBit_hasExplicitChance : execution.HasExplicitChance := by
  intro history active joint
  rcases history with ⟨state, _trace⟩
  cases state with
  | initial => obtain ⟨_, active⟩ := active; exact False.elim active
  | decision latent arrival => exact ⟨.terminal latent arrival joint.1, rfl⟩
  | terminal latent arrival action =>
      obtain ⟨_, active⟩ := active
      exact False.elim active

/-- A genuinely Bayesian assessment with nonconstant utility satisfies CPPBE. -/
theorem matching_isConditionalPBE :
    fullyMixedAssessment.IsConditionalPBE information wellFoundedHistories matchingPayoff := by
  apply InformationModel.BehavioralAssessment.IsSequentialEquilibrium.isConditionalPBE
    information information_decisionInformationAntichain wellFoundedHistories
      hiddenBit_hasExplicitChance matchingPayoff
  exact (game.isSequentialEquilibrium_iff information_decisionInformationAntichain
    fullyMixedAssessment wellFoundedHistories matchingPayoff).mp
      fullyMixedAssessment_isSequentialEquilibrium_matchingPayoff

/-- The same continuation evaluator rejects an assessment that chooses the worse action. -/
theorem irrational_not_isConditionalPBE :
    ¬ wrongAssessment.IsConditionalPBE information wellFoundedHistories matchingPayoff :=
  fun equilibrium => wrongAssessment_not_isSequentiallyRational_matchingPayoff equilibrium.1

end GameTheory.Tests.ConditionalPBE

namespace GameTheory.Tests.ConditionalPBEFiniteExistence

open GameTheory GameTheory.Protocol GameTheory.Tests.Randomized
open GameTheory.Analysis.Protocol.DecisionRecallExistenceTest

/-- Voting moves deterministically from the unique decision history. -/
theorem vote_hasExplicitChance : once.HasExplicitChance := by
  intro history _ joint
  obtain ⟨_, vote, _, deterministic⟩ := legal_start joint.2
  exact ⟨.voted vote, deterministic⟩

/-- CPPBE existence needs recall at decision sites, even when terminal observation
forgets the player's vote. -/
theorem exists_conditionalPBE :
    ∃ assessment : singleModel.BehavioralAssessment,
      assessment.IsConditionalPBE singleModel once.wellFoundedHistories_of_fintype payoff :=
  singleModel.exists_conditionalPBE single_decisionRecall fallback payoff _
    vote_hasExplicitChance

end GameTheory.Tests.ConditionalPBEFiniteExistence
