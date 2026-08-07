/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AffineEqualityFarkas

/-!
# Resolved projective chart and arc-lifting interface

`Math.AffineEqualityFarkas` starts after a finite affine tangent system

`A h = b`, `G h ≥ 0`

has been supplied. A quitting-game producer needs additional geometric data:
resolved projective points, finite chart labels, the matrices attached to each
chart, and—most importantly—a proof that every feasible lexicographic tangent
lifts to an actual positive analytic or Puiseux successor.

A linear tangent need not integrate to a real arc: the real variety
`x^2 + y^2 = 0` has the whole plane as its linearized tangent space at the
origin but no nonconstant real arc. Arc lifting must therefore be an explicit
hypothesis or a separately proved theorem; it cannot be inferred from Farkas
duality.

`QuittingResolvedProjectiveChartInterface` records the exact contract over an
arbitrary ordered field. The field `lift_feasible` is the missing
resolution/regularity theorem. Once an instance has been constructed,
`physicalSuccessor_or_farkas` composes that field with the finite affine
Farkas alternative.

This module does **not** construct an instance from the quitting Bellman
variety. An arbitrary-game producer must still prove chart coverage,
regularity or higher-jet lifting, and compatibility of the resulting physical
successor with the strategic state carried by the chart.
-/

noncomputable section

namespace GameTheory

variable {𝕜 Point Cell EqRow IneqRow : Type*} {n : ℕ}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Fintype Cell] [DecidableEq Cell]
  [Fintype EqRow] [DecidableEq EqRow]
  [Fintype IneqRow] [DecidableEq IneqRow]

/-- A finite resolved-chart contract for projective quitting Bellman data.
The ambient tangent dimension and row types are fixed; varying chart dimensions
may be padded by zero rows and columns. -/
structure QuittingResolvedProjectiveChartInterface
    (𝕜 Point Cell EqRow IneqRow : Type*)
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [Fintype Cell] [DecidableEq Cell]
    [Fintype EqRow] [DecidableEq EqRow]
    [Fintype IneqRow] [DecidableEq IneqRow]
    (n : ℕ) where
  /-- Finite resolved label of a projective point. -/
  cell : Point → Cell
  /-- Strategic or geometric output points at which pivoting stops. -/
  isOutput : Point → Prop
  /-- Frozen equality matrix in a resolved chart. -/
  A : Cell → EqRow → Fin n → 𝕜
  /-- Frozen affine equality right-hand side. -/
  b : Cell → EqRow → 𝕜
  /-- Frozen physical-orientation and slack inequalities. -/
  G : Cell → IneqRow → Fin n → 𝕜
  /-- An actual successor relation on resolved projective points. -/
  IsPhysicalSuccessor : Point → Point → Prop
  /-- **Arc-lifting obligation.** Every feasible tangent at a non-output
  point integrates to an actual positive physical successor. -/
  lift_feasible : ∀ point,
    ¬isOutput point →
      Math.LinearAlgebra.IsAffineEqualityInequalityFeasible
        (𝕜 := 𝕜) (EqRow := EqRow) (IneqRow := IneqRow) (n := n)
        (A (cell point)) (b (cell point)) (G (cell point)) →
      ∃ next, IsPhysicalSuccessor point next

/-- The game-facing Farkas row attached to a resolved point. This is still
only an algebraic obstruction; a semantic decoder is a separate theorem. -/
def IsQuittingResolvedProjectiveFarkasObstruction
    (chart : QuittingResolvedProjectiveChartInterface
      𝕜 Point Cell EqRow IneqRow n)
    (point : Point) (y : EqRow → 𝕜) (lambda : IneqRow → 𝕜) : Prop :=
  Math.LinearAlgebra.IsAffineEqualityFarkasCertificate
    (𝕜 := 𝕜) (EqRow := EqRow) (IneqRow := IneqRow) (n := n)
    (chart.A (chart.cell point))
    (chart.b (chart.cell point))
    (chart.G (chart.cell point)) y lambda

/-- **Resolved physical-successor-or-Farkas theorem.** Once chart realization
and arc lifting have been supplied, every non-output resolved point either has
an actual physical successor or carries a normalized/rescalable affine Farkas
obstruction. -/
theorem QuittingResolvedProjectiveChartInterface.physicalSuccessor_or_farkas
    (chart : QuittingResolvedProjectiveChartInterface
      𝕜 Point Cell EqRow IneqRow n)
    (point : Point) (hnotOutput : ¬chart.isOutput point) :
    (∃ next, chart.IsPhysicalSuccessor point next) ∨
      ∃ y : EqRow → 𝕜, ∃ lambda : IneqRow → 𝕜,
        IsQuittingResolvedProjectiveFarkasObstruction chart point y lambda := by
  rcases Math.LinearAlgebra.affineEqualityInequality_feasible_or_farkas
      (𝕜 := 𝕜) (EqRow := EqRow) (IneqRow := IneqRow) (n := n)
      (chart.A (chart.cell point))
      (chart.b (chart.cell point))
      (chart.G (chart.cell point)) with hfeasible | hobstruction
  · exact Or.inl (chart.lift_feasible point hnotOutput hfeasible)
  · exact Or.inr hobstruction

end GameTheory
