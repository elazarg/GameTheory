/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ThreePlayer.SolanTerminalAdapter
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Every three-player finite quitting game has a uniform equilibrium payoff

Solan's three-player absorbing-game theorem is specialized in
`SolanSourceStatement.lean` to one fixed terminal target with prescribed lower
bounds and unilateral-deviation upper bounds.  `SolanTerminalAdapter.lean`
turns those bounds into terminal approximate Nash profiles at every positive
accuracy.  This module performs the final, already formalized step through
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`.

The conditional theorem below exposes the complete Lean argument independently
of the external source declaration.  The headline theorem differs only by
supplying the precisely named Solan specialization.
-/

noncomputable section

namespace GameTheory

open StochasticGame

/-- **Conditional three-player classification from the exact Solan source
interface.**

This theorem is axiom-clean: any future formal proof of
`SolanThreePlayerQuittingConclusion reward` can be plugged in without changing
the terminal or uniformization layers. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_threePlayer_of_solanConclusion
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3))
    (hSolan : SolanThreePlayerQuittingConclusion reward) :
    ∃ payoff : Payoff (Fin 3),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
    reward hSolan.terminalNash_all_errors

/-- **Every three-player finite quitting game has a uniform equilibrium
payoff.**

`HEADLINE` — for every reward table on the seven nonempty coalitions of
`Fin 3`, there is an ordinary repository
`StochasticGame.IsUniformEquilibriumPayoff` from the live state.  The profile
may depend on the requested accuracy; deviations range over all behavior
strategies; one target works for all sufficiently long finite horizons.

The proof invokes exactly one external mathematical result:
`solan1999_threePlayerQuitting_terminalTargetBounds`.  Everything after that
source boundary, including terminal approximate Nash production and fixed
uniform-payoff selection, is proved in Lean. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_threePlayer
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)) :
    ∃ payoff : Payoff (Fin 3),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_threePlayer_of_solanConclusion
    reward (solan1999_threePlayerQuitting_terminalTargetBounds reward)

end GameTheory
