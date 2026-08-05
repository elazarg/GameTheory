/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Interval.DyadicInterval
import Math.Interval.RationalPolynomial

/-!
# Reflected polynomial automatic differentiation with dyadic intervals

This is the bounded-denominator executable counterpart of
`RationalPolynomial.evalDualInterval`.  It evaluates the very same syntax
tree, rounding outward after every multiplication.  The soundness theorem
therefore connects computed integer endpoints directly to the real value and
formal partial derivatives of the reflected polynomial.
-/

namespace Math
namespace Interval

namespace RationalPolynomial

variable {precision variableCount : ℕ}

/-- A fixed-precision interval value and all interval gradient coordinates. -/
structure DyadicDual (precision variableCount : ℕ) where
  value : DyadicInterval precision
  derivative : Fin variableCount → DyadicInterval precision

namespace DyadicDual

def constant (value : ℚ) : DyadicDual precision variableCount :=
  ⟨DyadicInterval.ofRat value,
    fun _ ↦ DyadicInterval.ofInt 0⟩

def ofVariable (box : Fin variableCount → DyadicInterval precision)
    (index : Fin variableCount) : DyadicDual precision variableCount :=
  ⟨box index, fun coordinate ↦
    DyadicInterval.ofRat (if coordinate = index then (1 : ℚ) else 0)⟩

def add (first second : DyadicDual precision variableCount) :
    DyadicDual precision variableCount :=
  ⟨first.value.add second.value,
    fun coordinate ↦
      (first.derivative coordinate).add (second.derivative coordinate)⟩

def neg (dual : DyadicDual precision variableCount) :
    DyadicDual precision variableCount :=
  ⟨dual.value.neg,
    fun coordinate ↦ (dual.derivative coordinate).neg⟩

def mul (first second : DyadicDual precision variableCount) :
    DyadicDual precision variableCount :=
  ⟨first.value.mul second.value,
    fun coordinate ↦
      ((first.derivative coordinate).mul second.value).add
        (first.value.mul (second.derivative coordinate))⟩

end DyadicDual

/-- One-pass dyadic interval evaluation and automatic differentiation. -/
def evalDualDyadic
    (box : Fin variableCount → DyadicInterval precision) :
    RationalPolynomial variableCount → DyadicDual precision variableCount
  | .constant value => .constant value
  | .var index => .ofVariable box index
  | .add first second =>
      (evalDualDyadic box first).add (evalDualDyadic box second)
  | .neg expression => (evalDualDyadic box expression).neg
  | .mul first second =>
      (evalDualDyadic box first).mul (evalDualDyadic box second)

/-- Simultaneous soundness of outward-rounded dyadic automatic
differentiation. -/
theorem evalDualDyadic_sound
    (expression : RationalPolynomial variableCount)
    (box : Fin variableCount → DyadicInterval precision)
    (point : Fin variableCount → ℝ)
    (hpoint : ∀ index, (box index).Contains (point index)) :
    (evalDualDyadic box expression).value.Contains
        (evalReal point expression) ∧
      ∀ coordinate,
        ((evalDualDyadic box expression).derivative coordinate).Contains
          (evalReal point (formalPartial coordinate expression)) := by
  induction expression with
  | constant value =>
      constructor
      · exact DyadicInterval.contains_ofRat value
      · intro coordinate
        exact DyadicInterval.contains_ofInt 0
  | var index =>
      constructor
      · exact hpoint index
      · intro coordinate
        by_cases hcoordinate : coordinate = index
        · simpa only [evalDualDyadic, DyadicDual.ofVariable,
            formalPartial, evalReal, if_pos hcoordinate] using
            (DyadicInterval.contains_ofRat (precision := precision) (1 : ℚ))
        · simpa only [evalDualDyadic, DyadicDual.ofVariable,
            formalPartial, evalReal, if_neg hcoordinate] using
            (DyadicInterval.contains_ofRat (precision := precision) (0 : ℚ))
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
