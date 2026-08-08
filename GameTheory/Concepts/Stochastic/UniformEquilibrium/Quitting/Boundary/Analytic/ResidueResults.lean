/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Repair.LocalMechanismResidueWitness
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Analytic.SwitchingResidueExactRoot

/-!
# Stationary certificates and local-mechanism residues

This module is the public entrypoint for exact stationary certification and
the three-player reward tables that test local equilibrium mechanisms.

`QuittingStationaryEndpointCompiler`, imported through the exact-root
development, turns a stationary fixed point and finite endpoint conditions
into Nash against every behavioral deviation and then into a uniform payoff.

The switching-residue regression table has no sure exit set but admits two
distinct exact stationary uniform-equilibrium payoffs.  The parametric table
in `QuittingLocalMechanismResidueWitness` extends that example: its value at
`L = 0` is the regression table, while every `L > 18/5` also defeats the
interior two-owner/one-sure-blocker mechanism.  Those parameters retain an
exact equilibrium in the omitted double-sure-quitter cell.

Together the examples locate the obstruction in an incomplete local branch
grammar rather than in equilibrium existence.
-/

namespace GameTheory

/-- The switching-residue regression table is the `L = 0` member of the
parametric local-mechanism residue family. -/
theorem quittingLocalMechanismReward_zero_eq_switchingResidueReward :
    QuittingLocalMechanismResidueWitness.reward 0 =
      QuittingSwitchingResidueRegression.reward := by
  rfl

/-- The associated quitting-game rewards also agree at `L = 0`. -/
theorem quittingLocalMechanismGameReward_zero_eq_switchingResidueGameReward :
    QuittingLocalMechanismResidueWitness.gameReward 0 =
      QuittingSwitchingResidueRegressionBridge.gameReward := by
  rfl

end GameTheory
