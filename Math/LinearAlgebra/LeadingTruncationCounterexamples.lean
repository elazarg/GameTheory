/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.ExactBlockElimination
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Exact cancellation regressions against leading-only truncation

These finite algebra examples record the verified C1 and C4 obstructions from
Q109.  They use rational functions in one indeterminate, a field already large
enough for the examples.  A proper two-block elimination leaves the retained
coordinate unchanged; rebasing then cancels every displayed low-order term and
exposes the first omitted term.

This is deliberately not a definition of a general leading-term algorithm and
does not state schedule confluence, an initial-form criterion, or any Puiseux
effectivity claim.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

namespace Math
namespace LeadingTruncationCounterexamples

/-- The finite string `x + x² + ... + x^(N+1)`. -/
def cancellationRhs {R : Type*} [Semiring R] (x : R) (N : ℕ) : R :=
  ∑ j ∈ Finset.range (N + 1), x ^ (j + 1)

/-- The cancelling rebase `1 + x + ... + x^(N-1)`. -/
def cancellationRebase {R : Type*} [Semiring R] (x : R) (N : ℕ) : R :=
  ∑ j ∈ Finset.range N, x ^ j

/-- Rebasing cancels all `N` visible terms and exposes exactly the next one. -/
theorem cancellationRhs_sub_mul_cancellationRebase
    {R : Type*} [CommRing R] (x : R) (N : ℕ) :
    cancellationRhs x N - x * cancellationRebase x N = x ^ (N + 1) := by
  rw [cancellationRhs, cancellationRebase, Finset.sum_range_succ,
    Finset.mul_sum]
  simp_rw [← pow_succ']
  abel

abbrev RationalParameterField := RatFunc ℚ

/-- The exact parameter used in the rational-function regressions. -/
def parameter : RationalParameterField :=
  RatFunc.X

theorem parameter_ne_zero : parameter ≠ 0 :=
  RatFunc.X_ne_zero

/-- The scalar `t` pivot in the two-state diagonal system. -/
def pivot : Matrix Unit Unit RationalParameterField :=
  Matrix.diagonal fun _ => parameter

@[implicit_reducible]
private noncomputable def pivotInvertible : Invertible pivot :=
  invertibleOfLeftInverse pivot (Matrix.diagonal fun _ => parameter⁻¹) <| by
    rw [pivot, Matrix.diagonal_mul_diagonal]
    ext (_ : Unit) (_ : Unit)
    simp [parameter_ne_zero]

/-- Exact reduced-and-rebased right-hand side in the two-state C4 family. -/
def exactRebasedRhs (N : ℕ) : Unit → RationalParameterField :=
  letI : Invertible pivot := pivotInvertible
  ExactBlockElimination.reducedRhs pivot 0 (fun _ => 0)
      (fun _ => cancellationRhs parameter N) -
    ExactBlockElimination.schurComplement pivot 0 0 pivot *ᵥ
      (fun _ => cancellationRebase parameter N)

/-- The proper elimination followed by rebase exposes precisely `t^(N+1)`. -/
theorem exactRebasedRhs_eq (N : ℕ) :
    exactRebasedRhs N = fun _ => parameter ^ (N + 1) := by
  letI : Invertible pivot := pivotInvertible
  funext coordinate
  cases coordinate
  simp only [exactRebasedRhs, ExactBlockElimination.reducedRhs,
    ExactBlockElimination.schurComplement, pivot, Matrix.zero_mul,
    Matrix.mul_zero, sub_zero, Matrix.zero_mulVec,
    Matrix.diagonal_const_mulVec, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  exact cancellationRhs_sub_mul_cancellationRebase parameter N

theorem exactRebasedRhs_ne_zero (N : ℕ) : exactRebasedRhs N ≠ 0 := by
  rw [exactRebasedRhs_eq]
  intro hzero
  have := congrFun hzero ()
  simp only [Pi.zero_apply] at this
  exact (pow_ne_zero _ parameter_ne_zero) this

/-- C1 after the proper first-state elimination, but with `t+t²` replaced by
its leading-only surrogate `t` before rebasing. -/
def c1LeadingOnlyRebasedRhs : Unit → RationalParameterField :=
  letI : Invertible pivot := pivotInvertible
  ExactBlockElimination.reducedRhs pivot 0 (fun _ => 0) (fun _ => parameter) -
    ExactBlockElimination.schurComplement pivot 0 0 pivot *ᵥ (fun _ => 1)

theorem c1LeadingOnlyRebasedRhs_eq_zero : c1LeadingOnlyRebasedRhs = 0 := by
  letI : Invertible pivot := pivotInvertible
  funext coordinate
  cases coordinate
  simp [c1LeadingOnlyRebasedRhs, ExactBlockElimination.reducedRhs,
    ExactBlockElimination.schurComplement, pivot]

/-- The proper two-state elimination regression: exact data leave `t²`, while
leading-only data leave zero. -/
theorem c1_properElimination_exact_ne_leadingOnly :
    exactRebasedRhs 1 ≠ c1LeadingOnlyRebasedRhs := by
  rw [c1LeadingOnlyRebasedRhs_eq_zero]
  exact exactRebasedRhs_ne_zero 1

/-- C1's exact retained right-hand side `t+t²`, rebased by `h=1`, leaves
`t²`. -/
theorem c1_exact_rebase :
    (parameter + parameter ^ 2) - parameter * 1 = parameter ^ 2 := by
  ring

/-- If `t+t²` is first truncated to `t`, the same rebase instead returns
zero. -/
theorem c1_leadingOnly_rebase : parameter - parameter * 1 = 0 := by
  ring

/-- The discarded C1 term is genuinely revived: the exact and leading-only
rebased right-hand sides differ. -/
theorem c1_exact_ne_leadingOnly :
    (parameter + parameter ^ 2) - parameter * 1 ≠
      parameter - parameter * 1 := by
  rw [c1_exact_rebase, c1_leadingOnly_rebase]
  exact pow_ne_zero 2 parameter_ne_zero

end LeadingTruncationCounterexamples
end Math
