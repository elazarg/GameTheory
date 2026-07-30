/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticPlayerNeutralOccupationAlternative
import Math.Probability.AnalyticOwnerChargedOccupationFlow

/-!
# Common-pole analytic player-neutral alternative

Apply the finite-owner charged occupation-flow alternative simultaneously
to every player's moving family of prescribed transitions and
continuation-neutral actual actions.

For a fixed bias, either one player has an analytic positive charged
circulation in that player's operational family, or all players have
analytic scaled occupation potentials sharing one pole-clearing order.
This remains a finite flow certificate and does not construct a strategy.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- A common-pole family of analytic scaled charged-occupation potentials,
one for each player's continuation-neutral operational system. -/
abbrev PlayerNeutralAnalyticScaledPotentialSystem
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) :=
  AnalyticOwnerScaledChargedOccupationPotential
    (fun who => germ.PlayerNeutralOccupationIndex who)
    (fun who => germ.rawPlayerNeutralOccupationColumn who)
    (fun who => germ.rawPlayerNeutralOccupationCharge B who)

/-- Across all players, either some player has a pole-cleared analytic
positive charged circulation using only prescribed and player-owned neutral
actions, or every player has a scaled analytic occupation potential with
one common pole-clearing order. -/
theorem
    exists_player_rawPlayerNeutralPositiveChargedCirculation_or_commonPotential
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) :
    (∃ who,
      Nonempty
        (AnalyticPositiveChargedCirculation
          (germ.rawPlayerNeutralOccupationColumn who)
          (germ.rawPlayerNeutralOccupationCharge B who))) ∨
    Nonempty
      (germ.PlayerNeutralAnalyticScaledPotentialSystem B) := by
  exact
    exists_owner_analyticPositiveChargedCirculation_or_commonScaledPotential
      (fun who => germ.PlayerNeutralOccupationIndex who)
      (fun who => germ.rawPlayerNeutralOccupationColumn who)
      (fun who => germ.rawPlayerNeutralOccupationCharge B who)
      (fun who =>
        germ.analytic_rawPlayerNeutralOccupationColumn who)
      (fun who =>
        germ.analytic_rawPlayerNeutralOccupationCharge B who)

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
