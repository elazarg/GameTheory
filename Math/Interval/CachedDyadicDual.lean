/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Interval.DyadicPolynomial
import Batteries.Data.Vector.Lemmas

/-!
# Eagerly cached dyadic automatic differentiation

`DyadicDual` exposes its gradient as a function.  That is ideal for semantic
statements, but a shared expression DAG can be traversed again for every
coordinate.  This executable carrier materializes the gradient as a vector at
each arithmetic node.  The `toDyadicDual` homomorphism proves that caching
does not change either the interval value or any gradient coordinate.
-/

namespace Math
namespace Interval

namespace RationalPolynomial

variable {precision variableCount : ℕ}

/-- A dyadic dual number whose whole gradient is eagerly materialized. -/
structure CachedDyadicDual (precision variableCount : ℕ) where
  value : DyadicInterval precision
  derivative : Vector (DyadicInterval precision) variableCount
deriving DecidableEq, Repr

namespace CachedDyadicDual

/-- Forget only the materialization strategy. -/
def toDyadicDual (dual : CachedDyadicDual precision variableCount) :
    DyadicDual precision variableCount :=
  ⟨dual.value, dual.derivative.get⟩

/-- Materializing the gradient loses no information. -/
theorem toDyadicDual_injective :
    Function.Injective
      (@toDyadicDual precision variableCount) := by
  intro first second hequal
  cases first with
  | mk firstValue firstDerivative =>
      cases second with
      | mk secondValue secondDerivative =>
          simp only [toDyadicDual, DyadicDual.mk.injEq] at hequal
          have hderivative : firstDerivative = secondDerivative :=
            Vector.ext fun index hindex =>
            congrFun hequal.2 ⟨index, hindex⟩
          cases hequal.1
          cases hderivative
          rfl

def constant (value : ℚ) : CachedDyadicDual precision variableCount :=
  ⟨DyadicInterval.ofRat value,
    Vector.replicate variableCount (DyadicInterval.ofInt 0)⟩

def ofVariable (box : Fin variableCount → DyadicInterval precision)
    (index : Fin variableCount) :
    CachedDyadicDual precision variableCount :=
  ⟨box index, Vector.ofFn fun coordinate ↦
    DyadicInterval.ofRat (if coordinate = index then (1 : ℚ) else 0)⟩

def add (first second : CachedDyadicDual precision variableCount) :
    CachedDyadicDual precision variableCount :=
  ⟨first.value.add second.value,
    Vector.ofFn fun coordinate ↦
      (first.derivative.get coordinate).add
        (second.derivative.get coordinate)⟩

def neg (dual : CachedDyadicDual precision variableCount) :
    CachedDyadicDual precision variableCount :=
  ⟨dual.value.neg, dual.derivative.map DyadicInterval.neg⟩

def mul (first second : CachedDyadicDual precision variableCount) :
    CachedDyadicDual precision variableCount :=
  ⟨first.value.mul second.value,
    Vector.ofFn fun coordinate ↦
      ((first.derivative.get coordinate).mul second.value).add
        (first.value.mul (second.derivative.get coordinate))⟩

private theorem dyadicDual_ext
    {first second : DyadicDual precision variableCount}
    (hvalue : first.value = second.value)
    (hderivative : ∀ coordinate,
      first.derivative coordinate = second.derivative coordinate) :
    first = second := by
  cases first
  cases second
  simp only [DyadicDual.mk.injEq]
  exact ⟨hvalue, funext hderivative⟩

@[simp] theorem toDyadicDual_constant (value : ℚ) :
    (constant value : CachedDyadicDual precision variableCount).toDyadicDual =
      DyadicDual.constant value := by
  apply dyadicDual_ext
  · rfl
  · intro coordinate
    exact Vector.get_replicate _ _ _

@[simp] theorem toDyadicDual_ofVariable
    (box : Fin variableCount → DyadicInterval precision)
    (index : Fin variableCount) :
    (ofVariable box index).toDyadicDual =
      DyadicDual.ofVariable box index := by
  apply dyadicDual_ext
  · rfl
  · intro coordinate
    simp only [toDyadicDual, ofVariable, DyadicDual.ofVariable]
    exact Vector.get_ofFn _ _

@[simp] theorem toDyadicDual_add
    (first second : CachedDyadicDual precision variableCount) :
    (first.add second).toDyadicDual =
      first.toDyadicDual.add second.toDyadicDual := by
  apply dyadicDual_ext
  · rfl
  · intro coordinate
    simp only [toDyadicDual, add, DyadicDual.add]
    exact Vector.get_ofFn _ _

@[simp] theorem toDyadicDual_neg
    (dual : CachedDyadicDual precision variableCount) :
    dual.neg.toDyadicDual = dual.toDyadicDual.neg := by
  apply dyadicDual_ext
  · rfl
  · intro coordinate
    simp only [toDyadicDual, neg, DyadicDual.neg]
    exact Vector.get_map _ _ _

@[simp] theorem toDyadicDual_mul
    (first second : CachedDyadicDual precision variableCount) :
    (first.mul second).toDyadicDual =
      first.toDyadicDual.mul second.toDyadicDual := by
  apply dyadicDual_ext
  · rfl
  · intro coordinate
    simp only [toDyadicDual, mul, DyadicDual.mul]
    exact Vector.get_ofFn _ _

end CachedDyadicDual

/-- Reflected evaluation with eager gradient materialization. -/
def evalCachedDyadic
    (box : Fin variableCount → DyadicInterval precision) :
    RationalPolynomial variableCount →
      CachedDyadicDual precision variableCount
  | .constant value => .constant value
  | .var index => .ofVariable box index
  | .add first second =>
      (evalCachedDyadic box first).add (evalCachedDyadic box second)
  | .neg expression => (evalCachedDyadic box expression).neg
  | .mul first second =>
      (evalCachedDyadic box first).mul (evalCachedDyadic box second)

/-- Eager evaluation is extensionally identical to the semantic dyadic
evaluator. -/
theorem toDyadicDual_evalCachedDyadic
    (box : Fin variableCount → DyadicInterval precision)
    (expression : RationalPolynomial variableCount) :
    (evalCachedDyadic box expression).toDyadicDual =
      evalDualDyadic box expression := by
  induction expression with
  | constant value => exact CachedDyadicDual.toDyadicDual_constant value
  | var index => exact CachedDyadicDual.toDyadicDual_ofVariable box index
  | add first second hfirst hsecond =>
      simp only [evalCachedDyadic, CachedDyadicDual.toDyadicDual_add,
        evalDualDyadic, hfirst, hsecond]
  | neg expression hexpression =>
      simp only [evalCachedDyadic, CachedDyadicDual.toDyadicDual_neg,
        evalDualDyadic, hexpression]
  | mul first second hfirst hsecond =>
      simp only [evalCachedDyadic, CachedDyadicDual.toDyadicDual_mul,
        evalDualDyadic, hfirst, hsecond]

end RationalPolynomial

end Interval
end Math
