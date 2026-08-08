/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Bellman.CurveGate
import Math.CurveSelection.PolynomialSignCellArc

/-!
# Analytic Bellman-germ existence

This file proves analytic Bellman-germ existence: every finite stochastic
game with nonempty finite action sets admits a coupled analytic germ of
discounted stationary Bellman equilibria at discount one.

The mathematical input is unconditional analytic curve selection in a
complete real polynomial sign cell.  `BellmanCurveGate` supplies a
zero-discount Bellman endpoint and reduces the game-theoretic construction
to that geometric theorem.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

/--
**Analytic Bellman-germ existence.** Every finite stochastic game with
finite nonempty action sets admits one coupled analytic germ of discounted
stationary Bellman equilibria at discount one.
-/
def AnalyticBellmanGermExistence : Prop :=
  ∀ (ι : Type) (G : StochasticGame ι)
      [Fintype G.State]
      [Fintype ι]
      [DecidableEq ι]
      [∀ i, Fintype (G.Act i)]
      [∀ i, DecidableEq (G.Act i)]
      [∀ i, Nonempty (G.Act i)],
    Nonempty G.AnalyticBellmanGerm

/--
The direct consumer form of analytic Bellman-germ existence.  No further
mathematical hypothesis is needed once `AnalyticBellmanGermExistence` has
been proved.
-/
theorem AnalyticBellmanGermExistence.forGame
    (h : AnalyticBellmanGermExistence)
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
Analytic Bellman-germ existence, obtained from unconditional analytic
curve selection in the polynomial Bellman sign cell.
-/
theorem analyticBellmanGermExistence : AnalyticBellmanGermExistence := by
  intro ι G _ _ _ _ _ _
  apply G.exists_analyticBellmanGerm
  intro assign₀ τ hdisc hclosure
  simpa [bellmanDiscountCoordinate] using
    Math.CurveSelection.PolynomialSignCellArc.hasPositiveCoordinateAnalyticArcAt_signCell
      G.bellmanConstraintPoly τ BellmanVar.disc
      assign₀ hdisc hclosure

end StochasticGame
end GameTheory
