/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Interval.PolynomialLipschitz
import Math.KrawczykBridge

/-!
# Exact polynomial Krawczyk certificates

This module composes dyadic automatic-differentiation bounds for a reflected
polynomial system with the closed-ball Krawczyk existence bridge.  Certificate
data only need to establish coordinatewise box containment, an exact row-sum
contraction bound, the center correction bound, and injectivity of the chosen
preconditioner.
-/

namespace Math.Interval.RationalPolynomial

open Function Metric Set
open scoped NNReal

variable {precision variableCount : ℕ}

/-- End-to-end polynomial Krawczyk certificate: if the reflected polynomial
system is the preconditioned residual step, then exact dyadic row-sum and
box-containment checks supply the analytic hypotheses of the closed-ball
existence bridge. -/
theorem exists_zero_in_closedBall_of_evalDualDyadic_absRowSum
    (residual : (Fin variableCount → ℝ) → (Fin variableCount → ℝ))
    (preconditioner :
      (Fin variableCount → ℝ) →ₗ[ℝ] (Fin variableCount → ℝ))
    (expressions : Fin variableCount →
      RationalPolynomial variableCount)
    (box : Fin variableCount → DyadicInterval precision)
    (center : Fin variableCount → ℝ) (radius : ℝ)
    (contraction : ℝ≥0)
    (hradius : 0 ≤ radius) (hcontraction : contraction < 1)
    (hpreconditioner : Injective preconditioner)
    (hstep :
      (fun point output ↦ evalReal point (expressions output)) =
        fun point ↦ point - preconditioner (residual point))
    (hendpoints : ∀ coordinate,
      (box coordinate).Contains (center coordinate - radius) ∧
        (box coordinate).Contains (center coordinate + radius))
    (hrow : ∀ output,
      ∑ input,
          dyadicAbsBound
            ((evalDualDyadic box
              (expressions output)).derivative input) ≤
        (contraction : ℝ))
    (hcorrection : norm (preconditioner (residual center)) ≤
      (1 - (contraction : ℝ)) * radius) :
    ∃ root ∈ closedBall center radius, residual root = 0 := by
  apply Math.exists_zero_in_closedBall_of_preconditioned_contraction
    residual preconditioner center radius contraction hradius hcontraction
    hpreconditioner
  · rw [← hstep]
    exact
      lipschitzOnWith_evalRealVector_closedBall_of_evalDualDyadic_absRowSum
        expressions box center radius contraction hendpoints hrow
  · exact hcorrection

end Math.Interval.RationalPolynomial
