/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ThreePlayer.AnalyticPacket

/-!
# The analytic waist for finite quitting games

The general finite-player analytic waist theorem.  For every quitting game
over an arbitrary finite player type, at least one of the following holds.

* The game has an ordinary uniform-equilibrium payoff.
* The analytic construction exports a normalized singleton source packet:
  simplex weights over the players together with a target payoff vector such
  that every coordinate of the target is dominated by the corresponding
  coordinate of the singleton-reward mixture of the weights (the source
  inequality), the target dominates every player's own singleton reward and
  every player's punishment value from below, and every owner carrying
  positive weight has its target coordinate pinned to its own singleton
  reward (diagonal complementarity on the support).

The proof is the pre-dispatch segment of the unconditional three-player
capstone, which is polymorphic in the player type throughout.  The analytic
Bellman germ of the punishment-normalized auxiliary game exists
unconditionally by real polynomial curve selection.  If its endpoint is not
jointly absorbing free of the all-Continue profile, the completed-cycle
compiler already produces a uniform-equilibrium payoff of the original game.
Otherwise the endpoint is all-Continue and the first-nonzero-analytic-order
classification applies: the cemetery-dominant branch yields the Never
uniform equilibrium, while the matching and real-absorption-dominant
branches export the normalized singleton source packet.

**Fence.**  This reduction does NOT prove arbitrary-player existence.  The
packet's support can be any subset of the players, and supports larger than
three cannot be cut down to smaller ones by Caratheodory-style mass
reallocation: an owner carrying positive weight contributes a pinning
*equality* while every outsider contributes deviation *inequalities*, and
these constraints must be preserved jointly, which linear reallocation of
the weights does not do.  What the theorem does show is that no additional
analytic or compactness input is needed beyond this point: the remaining
obstruction to general finite-player existence is the purely
finite-dimensional problem of decoding a normalized singleton source packet
into an equilibrium.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The analytic waist.**  Every quitting game over a finite player type
either has an ordinary uniform-equilibrium payoff or exports a normalized
singleton source packet.

This is the three-player capstone argument with the final three-dimensional
singleton dispatch deleted: the absorbing-endpoint branch and the
cemetery-dominant all-Continue branch close to a uniform payoff exactly as
there, and the remaining all-Continue branches return the packet itself
instead of dispatching it. -/
theorem quittingGame_uniformPayoff_or_normalizedSingletonSourcePacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
    Nonempty (QuittingNormalizedSingletonSourcePacket reward) := by
  obtain ⟨g⟩ :=
    nonempty_analyticBellmanGerm_quittingGame (quittingAuxiliaryReward reward)
  by_cases habsorbs :
      quittingStationaryContinueMass (g.endpointProfile none) < 1
  · exact Or.inl ⟨quittingAuxiliaryTarget reward (quittingGermValue g 0),
      isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint
        reward g habsorbs⟩
  · have hcontinue :
        quittingStationaryContinueMass (g.endpointProfile none) = 1 := by
      apply le_antisymm
      · exact quittingStationaryContinueMass_le_one _
      · exact not_lt.mp habsorbs
    rcases quittingAuxiliaryGerm_allContinueAlternative reward g hcontinue with
      hnever | hpacket
    · exact Or.inl ⟨0, hnever.2⟩
    · exact Or.inr hpacket

end GameTheory
