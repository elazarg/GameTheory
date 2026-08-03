/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Interval.RationalInterval

/-!
# Reflected rational polynomials with interval automatic differentiation

The syntax tree is intentionally unnormalized.  This preserves the sparse,
factored shape of the 31-variable period-eleven equations.  A single dual
evaluation computes exact interval enclosures for both values and every
formal partial derivative.
-/

set_option autoImplicit false

namespace Math
namespace Interval

/-- Factored rational polynomial expressions in `variableCount` variables. -/
inductive RationalPolynomial (variableCount : ℕ) where
  | constant (value : ℚ)
  | var (index : Fin variableCount)
  | add (first second : RationalPolynomial variableCount)
  | neg (expression : RationalPolynomial variableCount)
  | mul (first second : RationalPolynomial variableCount)
deriving DecidableEq, Repr

namespace RationalPolynomial

variable {variableCount : ℕ}

instance : Zero (RationalPolynomial variableCount) :=
  ⟨.constant 0⟩

instance : One (RationalPolynomial variableCount) :=
  ⟨.constant 1⟩

instance : Add (RationalPolynomial variableCount) :=
  ⟨.add⟩

instance : Neg (RationalPolynomial variableCount) :=
  ⟨.neg⟩

instance : Sub (RationalPolynomial variableCount) :=
  ⟨fun first second ↦ first + -second⟩

instance : Mul (RationalPolynomial variableCount) :=
  ⟨.mul⟩

/-- Real evaluation of a reflected rational polynomial. -/
def evalReal (point : Fin variableCount → ℝ) :
    RationalPolynomial variableCount → ℝ
  | .constant value => value
  | .var index => point index
  | .add first second => evalReal point first + evalReal point second
  | .neg expression => -evalReal point expression
  | .mul first second => evalReal point first * evalReal point second

/-- Formal partial derivative of a factored expression.  The certificate
checker does not materialize this tree; it is the semantic specification of
the derivative component computed by `evalDualInterval`. -/
def formalPartial (coordinate : Fin variableCount) :
    RationalPolynomial variableCount → RationalPolynomial variableCount
  | .constant _ => 0
  | .var index => if coordinate = index then 1 else 0
  | .add first second =>
      formalPartial coordinate first + formalPartial coordinate second
  | .neg expression => -formalPartial coordinate expression
  | .mul first second =>
      formalPartial coordinate first * second +
        first * formalPartial coordinate second

/-- An interval value together with interval enclosures for all gradient
coordinates. -/
structure IntervalDual (variableCount : ℕ) where
  value : RationalInterval
  derivative : Fin variableCount → RationalInterval

namespace IntervalDual

def constant (value : ℚ) : IntervalDual variableCount :=
  ⟨RationalInterval.point value, fun _ ↦ RationalInterval.point 0⟩

def ofVariable (box : Fin variableCount → RationalInterval)
    (index : Fin variableCount) : IntervalDual variableCount :=
  ⟨box index, fun coordinate ↦
    RationalInterval.point (if coordinate = index then 1 else 0)⟩

def add (first second : IntervalDual variableCount) :
    IntervalDual variableCount :=
  ⟨first.value.add second.value,
    fun coordinate ↦
      (first.derivative coordinate).add (second.derivative coordinate)⟩

def neg (dual : IntervalDual variableCount) : IntervalDual variableCount :=
  ⟨dual.value.neg, fun coordinate ↦ (dual.derivative coordinate).neg⟩

def mul (first second : IntervalDual variableCount) :
    IntervalDual variableCount :=
  ⟨first.value.mul second.value,
    fun coordinate ↦
      ((first.derivative coordinate).mul second.value).add
        (first.value.mul (second.derivative coordinate))⟩

end IntervalDual

/-- One-pass exact interval evaluation and automatic differentiation. -/
def evalDualInterval (box : Fin variableCount → RationalInterval) :
    RationalPolynomial variableCount → IntervalDual variableCount
  | .constant value => .constant value
  | .var index => .ofVariable box index
  | .add first second =>
      (evalDualInterval box first).add (evalDualInterval box second)
  | .neg expression => (evalDualInterval box expression).neg
  | .mul first second =>
      (evalDualInterval box first).mul (evalDualInterval box second)

/-- **Simultaneous soundness of the reflected checker.**  If a real point is
inside the input rational box, dual interval evaluation encloses both the
polynomial value and every formal partial derivative at that point. -/
theorem evalDualInterval_sound
    (expression : RationalPolynomial variableCount)
    (box : Fin variableCount → RationalInterval)
    (point : Fin variableCount → ℝ)
    (hpoint : ∀ index, (box index).Contains (point index)) :
    (evalDualInterval box expression).value.Contains
        (evalReal point expression) ∧
      ∀ coordinate,
        ((evalDualInterval box expression).derivative coordinate).Contains
          (evalReal point (formalPartial coordinate expression)) := by
  induction expression with
  | constant value =>
      constructor
      · exact RationalInterval.contains_point value
      · intro coordinate
        exact RationalInterval.contains_point 0
  | var index =>
      constructor
      · exact hpoint index
      · intro coordinate
        by_cases hcoordinate : coordinate = index
        · simpa only [evalDualInterval, IntervalDual.ofVariable,
            formalPartial, evalReal, if_pos hcoordinate] using
            RationalInterval.contains_point (1 : ℚ)
        · simpa only [evalDualInterval, IntervalDual.ofVariable,
            formalPartial, evalReal, if_neg hcoordinate] using
            RationalInterval.contains_point (0 : ℚ)
  | add first second hfirst hsecond =>
      obtain ⟨hfirstValue, hfirstDerivative⟩ := hfirst
      obtain ⟨hsecondValue, hsecondDerivative⟩ := hsecond
      constructor
      · exact hfirstValue.add hsecondValue
      · intro coordinate
        exact (hfirstDerivative coordinate).add
          (hsecondDerivative coordinate)
  | neg expression hexpression =>
      obtain ⟨hvalue, hderivative⟩ := hexpression
      constructor
      · exact hvalue.neg
      · intro coordinate
        exact (hderivative coordinate).neg
  | mul first second hfirst hsecond =>
      obtain ⟨hfirstValue, hfirstDerivative⟩ := hfirst
      obtain ⟨hsecondValue, hsecondDerivative⟩ := hsecond
      constructor
      · exact hfirstValue.mul hsecondValue
      · intro coordinate
        exact ((hfirstDerivative coordinate).mul hsecondValue).add
          (hfirstValue.mul (hsecondDerivative coordinate))

end RationalPolynomial

end Interval
end Math
