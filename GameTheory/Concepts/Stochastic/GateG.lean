/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.BellmanCurveGate
import Math.GateGSelectionCapstone

/-!
# Analytic Bellman-germ existence

This file closes Gate G: every finite stochastic game with nonempty finite
action sets admits a coupled analytic germ of discounted stationary Bellman
equilibria at discount one.

The mathematical input is unconditional analytic curve selection in a
complete real polynomial sign cell.  `BellmanCurveGate` supplies a
zero-discount Bellman endpoint and reduces the game-theoretic construction
to that geometric theorem.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

/--
**Gate G.** Every finite stochastic game with finite nonempty action sets
admits one coupled analytic germ of discounted stationary Bellman
equilibria at discount one.
-/
def GateG : Prop :=
  ∀ (ι : Type) (G : StochasticGame ι)
      [Fintype G.State]
      [Fintype ι]
      [DecidableEq ι]
      [∀ i, Fintype (G.Act i)]
      [∀ i, DecidableEq (G.Act i)]
      [∀ i, Nonempty (G.Act i)],
    Nonempty G.AnalyticBellmanGerm

/--
The direct consumer form of Gate G.  No further mathematical hypothesis is
needed once `GateG` has been proved.
-/
theorem GateG.forGame
    (h : GateG)
    {ι : Type} (G : StochasticGame ι)
    [Fintype G.State]
    [Fintype ι]
    [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    [∀ i, DecidableEq (G.Act i)]
    [∀ i, Nonempty (G.Act i)] :
    Nonempty G.AnalyticBellmanGerm :=
  h ι G

/--
Gate G, obtained from unconditional analytic curve selection in the
polynomial Bellman sign cell.
-/
theorem gateG : GateG := by
  intro ι G _ _ _ _ _ _
  apply G.exists_analyticBellmanGerm
  intro assign₀ τ hdisc hclosure
  simpa [bellmanDiscountCoordinate] using
    Math.GateGSelectionCapstone.hasPositiveCoordinateAnalyticArcAt_signCell
      G.bellmanConstraintPoly τ BellmanVar.disc
      assign₀ hdisc hclosure

end StochasticGame
end GameTheory
