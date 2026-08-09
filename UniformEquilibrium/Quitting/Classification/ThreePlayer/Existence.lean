/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ThreePlayer.AnalyticPacket
import UniformEquilibrium.Quitting.Classification.ThreePlayer.SingletonDispatch

/-!
# Unconditional existence for three-player quitting games

This is the capstone of the three-player proof.  Starting from the
unconditional analytic Bellman germ for the punishment-normalized auxiliary
game, it separates the endpoint into two cases.

* A jointly absorbing endpoint is translated back to the original reward and
  closed by the punishment-admissible completed-cycle theorem.
* An all-Continue endpoint is classified by its first nonzero analytic order.
  The cemetery-dominant case gives the Never equilibrium.  The matching and
  real-absorption-dominant cases give a normalized singleton source packet,
  which the explicit three-dimensional alternative dispatches either to a
  complementary face circulation or to one of the two strict singleton-cycle
  compilers.

Every existence input in this argument is a theorem: in particular,
the analytic germ comes from unconditional real polynomial curve selection.
No game-theoretic existence axiom is assumed.
-/

noncomputable section

namespace GameTheory

open StochasticGame

/-- **Unconditional three-player quitting-game existence.**  Every quitting
game with player type `Fin 3` has an ordinary uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_threePlayer
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)) :
    ∃ payoff : Payoff (Fin 3),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨g⟩ :=
    nonempty_analyticBellmanGerm_quittingGame (quittingAuxiliaryReward reward)
  by_cases habsorbs :
      quittingStationaryContinueMass (g.endpointProfile none) < 1
  · exact ⟨quittingAuxiliaryTarget reward (quittingGermValue g 0),
      isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint
        reward g habsorbs⟩
  · have hcontinue :
        quittingStationaryContinueMass (g.endpointProfile none) = 1 := by
      apply le_antisymm
      · exact quittingStationaryContinueMass_le_one _
      · exact not_lt.mp habsorbs
    rcases quittingAuxiliaryGerm_allContinueAlternative reward g hcontinue with
      hnever | hpacket
    · exact ⟨0, hnever.2⟩
    · obtain ⟨packet⟩ := hpacket
      exact exists_uniformEquilibriumPayoff_of_threeSingletonSource
        reward packet.target packet.mass
          ⟨packet.mass_nonneg, packet.mass_sum⟩
          packet.mix_ge_target packet.positive_mass_pins_target
          packet.solo_le_target packet.punishment_le_target

end GameTheory
