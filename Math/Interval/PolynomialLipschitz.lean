/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Interval.DyadicPolynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# Sup-norm Lipschitz certificates for reflected polynomial systems

This module turns the derivative intervals computed by dyadic automatic
differentiation into a Lipschitz certificate for a square system of reflected
rational polynomials.  The ambient finite Pi spaces carry their standard sup
norm, so a maximum row-sum bound on the Jacobian controls the operator norm.

The calculus layer is independent of interval arithmetic: it first proves the
corresponding row-sum estimate for continuous linear maps and then applies the
mean-value inequality on convex sets.  The final theorems discharge those
hypotheses using the existing soundness theorem for `evalDualDyadic`.
-/

namespace Math

open Function Metric Set
open scoped NNReal

/-- The standard coordinate vector in a finite real Pi space. -/
def piBasisVector {n : ℕ} (coordinate : Fin n) : Fin n → ℝ :=
  fun index => if coordinate = index then 1 else 0

/-- A maximum row-sum bound on the standard-basis entries of a continuous
linear map between finite real Pi spaces bounds its sup-to-sup operator norm.
-/
theorem continuousLinearMap_norm_le_of_entrywise_rowSum
    {n m : ℕ} (linear : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))
    (bound : Fin m → Fin n → ℝ) (constant : ℝ)
    (hrow : ∀ output, ∑ input, bound output input ≤ constant)
    (hconstant : 0 ≤ constant)
    (hentry : ∀ output input,
      ‖linear (piBasisVector input) output‖ ≤ bound output input) :
    ‖linear‖ ≤ constant := by
  apply linear.opNorm_le_bound hconstant
  intro vector
  rw [pi_norm_le_iff_of_nonneg
    (mul_nonneg hconstant (norm_nonneg vector))]
  intro output
  have hdecomposition :=
    LinearMap.pi_apply_eq_sum_univ linear.toLinearMap vector
  have hcoordinate := congrFun hdecomposition output
  simp only [ContinuousLinearMap.coe_coe, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at hcoordinate
  rw [hcoordinate]
  calc
    ‖∑ input, vector input * linear (piBasisVector input) output‖ ≤
        ∑ input, ‖vector input * linear (piBasisVector input) output‖ :=
      norm_sum_le _ _
    _ = ∑ input,
        ‖vector input‖ * ‖linear (piBasisVector input) output‖ := by
      apply Finset.sum_congr rfl
      intro input _
      exact norm_mul _ _
    _ ≤ ∑ input, ‖vector‖ * bound output input := by
      apply Finset.sum_le_sum
      intro input _
      exact mul_le_mul (norm_le_pi_norm vector input)
        (hentry output input) (norm_nonneg _) (norm_nonneg vector)
    _ = ‖vector‖ * (∑ input, bound output input) := by
      rw [Finset.mul_sum]
    _ ≤ ‖vector‖ * constant :=
      mul_le_mul_of_nonneg_left (hrow output) (norm_nonneg vector)
    _ = constant * ‖vector‖ := mul_comm _ _

/-- On a convex set, maximum row-sum bounds on the entries of a specified
Fréchet derivative imply a sup-norm Lipschitz bound. -/
theorem lipschitzOnWith_pi_of_hasFDerivAt_entrywise_rowSum
    {n m : ℕ} {domain : Set (Fin n → ℝ)}
    (function : (Fin n → ℝ) → (Fin m → ℝ))
    (derivative : (Fin n → ℝ) →
      ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))
    (bound : Fin m → Fin n → ℝ) (constant : ℝ≥0)
    (hconvex : Convex ℝ domain)
    (hderivative : ∀ point ∈ domain,
      HasFDerivAt function (derivative point) point)
    (hrow : ∀ output,
      ∑ input, bound output input ≤ (constant : ℝ))
    (hentry : ∀ point ∈ domain, ∀ output input,
      ‖derivative point (piBasisVector input) output‖ ≤
        bound output input) :
    LipschitzOnWith constant function domain := by
  apply hconvex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun point hpoint =>
      (hderivative point hpoint).hasFDerivWithinAt)
  intro point hpoint
  exact_mod_cast continuousLinearMap_norm_le_of_entrywise_rowSum
    (derivative point) bound constant hrow constant.coe_nonneg
    (hentry point hpoint)

namespace Interval.RationalPolynomial

variable {precision variableCount : ℕ}

/-- The formal gradient, interpreted as a continuous linear functional on
the finite sup-norm coordinate space. -/
noncomputable def differential
    (point : Fin variableCount → ℝ)
    (expression : RationalPolynomial variableCount) :
    (Fin variableCount → ℝ) →L[ℝ] ℝ :=
  ∑ coordinate,
    (evalReal point (formalPartial coordinate expression)) •
      ContinuousLinearMap.proj coordinate

@[simp] theorem differential_apply
    (point direction : Fin variableCount → ℝ)
    (expression : RationalPolynomial variableCount) :
    differential point expression direction =
      ∑ coordinate,
        evalReal point (formalPartial coordinate expression) *
          direction coordinate := by
  simp [differential, smul_eq_mul]

@[simp] theorem differential_constant
    (point : Fin variableCount → ℝ) (value : ℚ) :
    differential point (.constant value) = 0 := by
  ext direction
  simp [differential, formalPartial, evalReal]

@[simp] theorem differential_var
    (point : Fin variableCount → ℝ) (index : Fin variableCount) :
    differential point (.var index) =
      ContinuousLinearMap.proj index := by
  ext direction
  rw [differential_apply]
  symm
  rw [Finset.sum_eq_single index]
  · simp [formalPartial, evalReal]
  · intro coordinate _ hne
    simp [formalPartial, hne, evalReal]
  · simp

@[simp] theorem differential_add
    (point : Fin variableCount → ℝ)
    (first second : RationalPolynomial variableCount) :
    differential point (.add first second) =
      differential point first + differential point second := by
  ext direction
  rw [add_apply, differential_apply, differential_apply,
    differential_apply]
  simp only [formalPartial, evalReal]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

@[simp] theorem differential_neg
    (point : Fin variableCount → ℝ)
    (expression : RationalPolynomial variableCount) :
    differential point (.neg expression) =
      -differential point expression := by
  ext direction
  rw [neg_apply, differential_apply, differential_apply]
  simp only [formalPartial, evalReal]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

@[simp] theorem differential_mul
    (point : Fin variableCount → ℝ)
    (first second : RationalPolynomial variableCount) :
    differential point (.mul first second) =
      evalReal point first • differential point second +
        evalReal point second • differential point first := by
  ext direction
  simp only [differential_apply, formalPartial, evalReal,
    add_apply, smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

/-- The formal partials of a reflected rational polynomial are the
coordinates of the Fréchet derivative of its real evaluation. -/
theorem hasFDerivAt_evalReal
    (expression : RationalPolynomial variableCount)
    (point : Fin variableCount → ℝ) :
    HasFDerivAt (fun input => evalReal input expression)
      (differential point expression) point := by
  induction expression with
  | constant value =>
      rw [differential_constant]
      change HasFDerivAt (fun _ => (value : ℝ)) 0 point
      exact hasFDerivAt_const (x := point) (value : ℝ)
  | var index =>
      rw [differential_var]
      change HasFDerivAt (fun input => input index)
        (ContinuousLinearMap.proj index) point
      exact hasFDerivAt_apply index point
  | add first second hfirst hsecond =>
      rw [differential_add]
      change HasFDerivAt
        ((fun input => evalReal input first) +
          (fun input => evalReal input second))
        (differential point first + differential point second) point
      exact hfirst.add hsecond
  | neg expression hexpression =>
      rw [differential_neg]
      change HasFDerivAt (-(fun input => evalReal input expression))
        (-differential point expression) point
      exact hexpression.neg
  | mul first second hfirst hsecond =>
      rw [differential_mul]
      change HasFDerivAt
        ((fun input => evalReal input first) *
          (fun input => evalReal input second))
        (evalReal point first • differential point second +
          evalReal point second • differential point first) point
      exact hfirst.mul hsecond

/-- The real rectangular set represented by a dyadic input box. -/
def dyadicBoxSet
    (box : Fin variableCount → DyadicInterval precision) :
    Set (Fin variableCount → ℝ) :=
  {point | ∀ coordinate, (box coordinate).Contains (point coordinate)}

theorem convex_dyadicBoxSet
    (box : Fin variableCount → DyadicInterval precision) :
    Convex ℝ (dyadicBoxSet box) := by
  intro first hfirst second hsecond a b ha hb hab coordinate
  change (∀ index, (box index).Contains (first index)) at hfirst
  change (∀ index, (box index).Contains (second index)) at hsecond
  change (box coordinate).Contains
    ((a • first + b • second) coordinate)
  have hfirstCoordinate := hfirst coordinate
  have hsecondCoordinate := hsecond coordinate
  rw [DyadicInterval.Contains, DyadicInterval.toRationalInterval,
    RationalInterval.Contains] at hfirstCoordinate hsecondCoordinate ⊢
  constructor
  · change (((box coordinate).lower /
        DyadicInterval.scale precision : ℚ) : ℝ) ≤
      a * first coordinate + b * second coordinate
    have hscale :
        a * (((box coordinate).lower /
            DyadicInterval.scale precision : ℚ) : ℝ) +
          b * (((box coordinate).lower /
            DyadicInterval.scale precision : ℚ) : ℝ) =
        (((box coordinate).lower /
            DyadicInterval.scale precision : ℚ) : ℝ) := by
      rw [← add_mul, hab, one_mul]
    rw [← hscale]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hfirstCoordinate.1 ha)
      (mul_le_mul_of_nonneg_left hsecondCoordinate.1 hb)
  · change a * first coordinate + b * second coordinate ≤
      (((box coordinate).upper /
        DyadicInterval.scale precision : ℚ) : ℝ)
    have hscale :
        a * (((box coordinate).upper /
            DyadicInterval.scale precision : ℚ) : ℝ) +
          b * (((box coordinate).upper /
            DyadicInterval.scale precision : ℚ) : ℝ) =
        (((box coordinate).upper /
            DyadicInterval.scale precision : ℚ) : ℝ) := by
      rw [← add_mul, hab, one_mul]
    rw [← hscale]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hfirstCoordinate.2 ha)
      (mul_le_mul_of_nonneg_left hsecondCoordinate.2 hb)

/-- Applying the formal differential to a standard coordinate direction
recovers the corresponding formal partial. -/
theorem differential_piBasisVector
    (point : Fin variableCount → ℝ)
    (expression : RationalPolynomial variableCount)
    (coordinate : Fin variableCount) :
    differential point expression (piBasisVector coordinate) =
      evalReal point (formalPartial coordinate expression) := by
  rw [differential_apply, Finset.sum_eq_single coordinate]
  · simp [piBasisVector]
  · intro other _ hne
    rw [piBasisVector, if_neg hne.symm]
    simp
  · simp

/-- A value enclosed by a dyadic interval has absolute value bounded by any
common upper bound for the absolute endpoint values. -/
theorem abs_le_of_dyadicContains_of_endpoints_le
    (interval : DyadicInterval precision) (value bound : ℝ)
    (hcontains : interval.Contains value)
    (hlower :
      |((interval.toRationalInterval.lower : ℚ) : ℝ)| ≤ bound)
    (hupper :
      |((interval.toRationalInterval.upper : ℚ) : ℝ)| ≤ bound) :
    |value| ≤ bound := by
  rw [DyadicInterval.Contains, RationalInterval.Contains] at hcontains
  rw [abs_le]
  constructor
  · exact (abs_le.mp hlower).1.trans hcontains.1
  · exact hcontains.2.trans (le_trans (le_abs_self _) hupper)

/-- Dyadic automatic-differentiation bounds for every formal partial,
combined by row sums, prove the sup-norm Lipschitz estimate used by a
Krawczyk certificate. -/
theorem lipschitzOnWith_evalRealVector_of_evalDualDyadic_rowSum
    (expressions : Fin variableCount →
      RationalPolynomial variableCount)
    (box : Fin variableCount → DyadicInterval precision)
    (bound : Fin variableCount → Fin variableCount → ℝ)
    (contraction : ℝ≥0)
    (hrow : ∀ output,
      ∑ input, bound output input ≤ (contraction : ℝ))
    (hlower : ∀ output input,
      |((((evalDualDyadic box
          (expressions output)).derivative input).toRationalInterval.lower :
            ℚ) : ℝ)| ≤ bound output input)
    (hupper : ∀ output input,
      |((((evalDualDyadic box
          (expressions output)).derivative input).toRationalInterval.upper :
            ℚ) : ℝ)| ≤ bound output input) :
    LipschitzOnWith contraction
      (fun point output => evalReal point (expressions output))
      (dyadicBoxSet box) := by
  let derivative : (Fin variableCount → ℝ) →
      ((Fin variableCount → ℝ) →L[ℝ]
        (Fin variableCount → ℝ)) :=
    fun point => ContinuousLinearMap.pi fun output =>
      differential point (expressions output)
  refine lipschitzOnWith_pi_of_hasFDerivAt_entrywise_rowSum
    (function := fun point output => evalReal point (expressions output))
    (derivative := derivative) (bound := bound) (constant := contraction)
    (domain := dyadicBoxSet box) (convex_dyadicBoxSet box) ?_ hrow ?_
  · intro point _
    exact hasFDerivAt_pi.mpr fun output =>
      hasFDerivAt_evalReal (expressions output) point
  · intro point hpoint output input
    change ‖differential point (expressions output)
      (piBasisVector input)‖ ≤ bound output input
    rw [differential_piBasisVector, Real.norm_eq_abs]
    exact abs_le_of_dyadicContains_of_endpoints_le _ _ _
      ((evalDualDyadic_sound
        (expressions output) box point hpoint).2 input)
      (hlower output input) (hupper output input)

/-- Absolute endpoint envelope of one dyadic interval, viewed in `ℝ`. -/
def dyadicAbsBound (interval : DyadicInterval precision) : ℝ :=
  max |((interval.toRationalInterval.lower : ℚ) : ℝ)|
    |((interval.toRationalInterval.upper : ℚ) : ℝ)|

/-- Executable row-sum form of the polynomial Lipschitz certificate.  It is
enough to check that the row sums of the absolute endpoint envelopes returned
by dyadic automatic differentiation are at most the desired constant. -/
theorem lipschitzOnWith_evalRealVector_of_evalDualDyadic_absRowSum
    (expressions : Fin variableCount →
      RationalPolynomial variableCount)
    (box : Fin variableCount → DyadicInterval precision)
    (contraction : ℝ≥0)
    (hrow : ∀ output,
      ∑ input,
          dyadicAbsBound
            ((evalDualDyadic box
              (expressions output)).derivative input) ≤
        (contraction : ℝ)) :
    LipschitzOnWith contraction
      (fun point output => evalReal point (expressions output))
      (dyadicBoxSet box) := by
  apply lipschitzOnWith_evalRealVector_of_evalDualDyadic_rowSum
    expressions box
    (fun output input =>
      dyadicAbsBound
        ((evalDualDyadic box (expressions output)).derivative input))
    contraction hrow
  · intro output input
    exact le_max_left _ _
  · intro output input
    exact le_max_right _ _

end Interval.RationalPolynomial

end Math
