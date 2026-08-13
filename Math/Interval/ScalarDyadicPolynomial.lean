/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Interval.DyadicPolynomial

/-!
# Scalar partial evaluation with dyadic intervals

This module projects dyadic interval automatic differentiation onto one
requested partial derivative.  The scalar evaluator traverses the reflected
polynomial while carrying only its value interval and that partial interval.
Its projection theorem identifies the result with the corresponding
coordinate of `evalDualDyadic`, so the scalar representation inherits the
existing value and derivative soundness theorems.
-/

namespace Math
namespace Interval

namespace RationalPolynomial

open Math.Interval

/-! ## Scalar dual arithmetic -/

/-- A fixed-precision interval value and one requested partial interval. -/
structure ScalarDyadicDual (precision : ℕ) where
  value : DyadicInterval precision
  derivative : DyadicInterval precision

namespace ScalarDyadicDual

variable {precision variableCount : ℕ}

/-- Embed a rational constant as a scalar dyadic dual number. -/
def constant (value : ℚ) : ScalarDyadicDual precision :=
  ⟨DyadicInterval.ofRat value, DyadicInterval.ofInt 0⟩

/-- Embed a boxed variable while selecting one derivative coordinate. -/
def ofVariable (box : Fin variableCount → DyadicInterval precision)
    (coordinate index : Fin variableCount) : ScalarDyadicDual precision :=
  ⟨box index,
    DyadicInterval.ofRat (if coordinate = index then (1 : ℚ) else 0)⟩

/-- Add scalar dyadic dual numbers componentwise. -/
def add (first second : ScalarDyadicDual precision) :
    ScalarDyadicDual precision :=
  ⟨first.value.add second.value, first.derivative.add second.derivative⟩

/-- Negate both components of a scalar dyadic dual number. -/
def neg (dual : ScalarDyadicDual precision) : ScalarDyadicDual precision :=
  ⟨dual.value.neg, dual.derivative.neg⟩

/-- Multiply scalar dyadic dual numbers using the product rule. -/
def mul (first second : ScalarDyadicDual precision) :
    ScalarDyadicDual precision :=
  ⟨first.value.mul second.value,
    (first.derivative.mul second.value).add
      (first.value.mul second.derivative)⟩

end ScalarDyadicDual

/-! ## Reflected polynomial evaluation -/

variable {precision variableCount : ℕ}

/-- Evaluate a reflected rational polynomial while retaining only one
partial-derivative interval. -/
def evalScalar
    (box : Fin variableCount → DyadicInterval precision)
    (coordinate : Fin variableCount) :
    RationalPolynomial variableCount → ScalarDyadicDual precision
  | .constant value => ScalarDyadicDual.constant value
  | .var index => ScalarDyadicDual.ofVariable box coordinate index
  | .add first second =>
      ScalarDyadicDual.add (evalScalar box coordinate first)
        (evalScalar box coordinate second)
  | .neg expression =>
      ScalarDyadicDual.neg (evalScalar box coordinate expression)
  | .mul first second =>
      ScalarDyadicDual.mul (evalScalar box coordinate first)
        (evalScalar box coordinate second)

/-- Scalar evaluation is exactly the selected coordinate of full dyadic
automatic differentiation. -/
theorem evalScalar_eq_projection
    (box : Fin variableCount → DyadicInterval precision)
    (coordinate : Fin variableCount)
    (expression : RationalPolynomial variableCount) :
    evalScalar box coordinate expression =
      { value := (evalDualDyadic box expression).value
        derivative := (evalDualDyadic box expression).derivative coordinate } := by
  induction expression with
  | constant value => rfl
  | var index =>
      simp only [evalScalar, ScalarDyadicDual.ofVariable,
        evalDualDyadic, DyadicDual.ofVariable]
  | add first second hfirst hsecond =>
      simp only [evalScalar, ScalarDyadicDual.add,
        evalDualDyadic, DyadicDual.add, hfirst, hsecond]
  | neg expression hexpression =>
      simp only [evalScalar, ScalarDyadicDual.neg,
        evalDualDyadic, DyadicDual.neg, hexpression]
  | mul first second hfirst hsecond =>
      simp only [evalScalar, ScalarDyadicDual.mul,
        evalDualDyadic, DyadicDual.mul, hfirst, hsecond]

/-- The value interval returned by scalar evaluation contains the real
polynomial value at every point in the input box. -/
theorem evalScalar_value_contains
    (box : Fin variableCount → DyadicInterval precision)
    (coordinate : Fin variableCount)
    (expression : RationalPolynomial variableCount)
    (point : Fin variableCount → ℝ)
    (hpoint : ∀ index, (box index).Contains (point index)) :
    (evalScalar box coordinate expression).value.Contains
      (evalReal point expression) := by
  rw [evalScalar_eq_projection]
  exact (evalDualDyadic_sound expression box point hpoint).1

/-- The derivative interval returned by scalar evaluation contains the real
formal partial at every point in the input box. -/
theorem evalScalar_derivative_contains
    (box : Fin variableCount → DyadicInterval precision)
    (coordinate : Fin variableCount)
    (expression : RationalPolynomial variableCount)
    (point : Fin variableCount → ℝ)
    (hpoint : ∀ index, (box index).Contains (point index)) :
    (evalScalar box coordinate expression).derivative.Contains
      (evalReal point (formalPartial coordinate expression)) := by
  rw [evalScalar_eq_projection]
  exact (evalDualDyadic_sound expression box point hpoint).2 coordinate

end RationalPolynomial

end Interval
end Math
