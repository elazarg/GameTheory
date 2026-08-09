/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeToggles
import UniformEquilibrium.Quitting.Classification.TwoPlayer.Existence
import UniformEquilibrium.Quitting.Classification.ThreePlayer.Existence
import UniformEquilibrium.Quitting.Classification.PlayerReindex
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot

/-!
# The counterexample regime is empty at small player types

The combined counterexample regime of `CounterexampleRegime` packages exactly
the structure any finite quitting game without a uniform-equilibrium payoff
must carry.  This module shows outright that the regime is *empty* over the
empty, one-element, `Bool`, and `Fin 3` player types, so a search for an
inhabitant may start at four players.

The empty case needs no existence theorem at all: the terminal-exploitability
field of the regime demands an improving player for every behavioral profile,
and with no players there is a profile but no player.  The one-player case is
settled here by a previously missing existence theorem, stated for an
arbitrary `Unique` player type: when the single player's solo-quit reward is
nonpositive the weight is zero-solo and all-continue delivers the zero payoff;
when it is positive, quitting surely is an owner-solo stationary equilibrium
whose inactive-player conditions are vacuous.  The `Bool` and `Fin 3` cases
invoke the machine-checked unconditional two- and three-player existence
theorems.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## One-player existence -/

/-- **Every one-player finite quitting game has a uniform-equilibrium
payoff.**  Stated for an arbitrary `Unique` player type.  If the single
player's solo-quit reward is nonpositive, the weight is zero-solo and the
all-continue profile delivers the zero vector.  Otherwise the player quits
surely: the owner-solo certification applies with the sure hazard, and its
inactive-player inequalities are vacuous because there is no other player. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_onePlayer
    [Unique ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_cases hsolo : quittingSoloReward reward default default ≤ 0
  · refine exists_uniformEquilibriumPayoff_of_zeroSolo reward ?_
    intro who
    rw [Unique.eq_default who]
    exact hsolo
  · rw [not_le] at hsolo
    exact ⟨quittingSoloReward reward default,
      isUniformEquilibriumPayoff_soloReward_of_inactive reward default
        (quittingHazardCoin 1 zero_le_one le_rfl)
        (by rw [quittingHazardCoin_true_toReal]; exact one_pos)
        hsolo.le
        (fun other hother ↦ absurd (Unique.eq_default other) hother)⟩

/-! ## Emptiness of the regime at small player types -/

namespace QuittingCounterexampleRegime

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The regime is empty over an empty player type: its terminal
exploitability field promises an improving player for every behavioral
profile, but the empty type supplies a profile and no player. -/
theorem elim_isEmpty [IsEmpty ι]
    (regime : QuittingCounterexampleRegime reward) : False := by
  obtain ⟨who, -, -⟩ :=
    regime.terminalExploitability fun i ↦ isEmptyElim i
  exact isEmptyElim who

/-- The regime is empty over any one-element player type, by the one-player
existence theorem. -/
theorem elim_unique [Unique ι]
    (regime : QuittingCounterexampleRegime reward) : False :=
  regime.not_exists_uniformEquilibriumPayoff
    (quittingGame_exists_uniformEquilibriumPayoff_onePlayer reward)

/-- The regime is empty over `Bool`, by the unconditional two-player
existence theorem. -/
theorem elim_twoPlayer
    {reward : {S : Finset Bool // S.Nonempty} → Payoff Bool}
    (regime : QuittingCounterexampleRegime reward) : False :=
  regime.not_exists_uniformEquilibriumPayoff
    (QuittingTwoPlayerExistence.quittingGame_exists_uniformEquilibriumPayoff_twoPlayer
      reward)

/-- The regime is empty over `Fin 3`, by the unconditional three-player
existence theorem. -/
theorem elim_threePlayer
    {reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)}
    (regime : QuittingCounterexampleRegime reward) : False :=
  regime.not_exists_uniformEquilibriumPayoff
    (quittingGame_exists_uniformEquilibriumPayoff_threePlayer reward)

/-- **Any counterexample has at least four players.**  Fewer than two players
is impossible by the toggle-instability consequences of the terminal gap, and
exactly two or three players is impossible by transporting the unconditional
`Bool` and `Fin 3` existence theorems along a player equivalence. -/
theorem three_lt_card (regime : QuittingCounterexampleRegime reward) :
    3 < Fintype.card ι := by
  by_contra hle
  rw [not_lt] at hle
  have htwo := regime.one_lt_card
  have hcase : Fintype.card ι = 2 ∨ Fintype.card ι = 3 := by omega
  rcases hcase with hcard | hcard
  · exact regime.not_exists_uniformEquilibriumPayoff
      (quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_two
        hcard reward)
  · exact regime.not_exists_uniformEquilibriumPayoff
      (quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three
        hcard reward)

end QuittingCounterexampleRegime

end GameTheory
