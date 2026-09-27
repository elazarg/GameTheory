/-
# Terminal semantics recovers the sufficient-horizon boundary

The finite hostile fixture has no two-step sequentially rational assessment,
but its certified three-step horizon has an equilibrium. Terminal-law
rationality recovers that equilibrium without changing consistency.
-/

import GameTheory.Analysis.Protocol.SequentialExistenceTest
import GameTheory.Protocol.BehavioralTerminal

noncomputable section

namespace GameTheory.Tests.SequentialTerminalFinite

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Protocol.InformationModel.BehavioralAssessment
open GameTheory.Math.Probability
open GameTheory.Tests.SequentialExistenceBoundary

/-- A phase rank decreases along each nonterminal transition. -/
def rank : State → ℕ
  | .root => 3
  | .choice => 2
  | .waiting => 1
  | .short | .long => 0

theorem rank_decreases {source target : State}
    (hsuccessor : execution.Successor target source) : rank target < rank source := by
  obtain ⟨joint, legal, realized⟩ := hsuccessor
  obtain ⟨action, rfl, hallowed⟩ := legal_joint legal
  have hnonterminal := legal.1
  simp only [execution, PMF.mem_support_iff, Option.getD_some] at realized
  cases source <;> cases action <;>
    simp_all [execution, State.running, State.allowed, next, rank]

/-- The finite boundary fixture satisfies the well-founded-play certificate. -/
theorem wellFounded : execution.WellFoundedPlay :=
  execution.wellFoundedPlay_of_rank rank (fun _ _ h => rank_decreases h)

/-- A terminal assessment exists at the certified full horizon, while every
assessment fails the insufficient two-step continuation predicate. -/
theorem terminal_equilibrium_at_full_horizon :
    ∃ assessment : information.BehavioralAssessment,
      assessment.IsSequentiallyRationalTerminal wellFounded payoff ∧
        game.IsSequentiallyConsistent antichain assessment ∧
        ¬ assessment.IsSequentiallyRationalWithin payoff 2 := by
  obtain ⟨assessment, hequilibrium⟩ :=
    GameTheory.Tests.SequentialExistence.boundary_exists_at_full_horizon
  have hdecomp := game.isSequentialEquilibriumWithin_iff antichain assessment payoff 3
  have ⟨hrational, hconsistent⟩ := hdecomp.mp hequilibrium
  have hterminal :=
    isSequentiallyRationalTerminal_iff_within_of_bounded
      (M := information) assessment wellFounded bounded_three payoff
  refine ⟨assessment, hterminal.mpr hrational, hconsistent, ?_⟩
  exact no_sequentially_rational_assessment assessment

end GameTheory.Tests.SequentialTerminalFinite
