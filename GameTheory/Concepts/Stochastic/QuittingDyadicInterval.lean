/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingRationalInterval
import Mathlib.Data.Int.DivMod

/-!
# Fixed-precision dyadic interval arithmetic

Endpoints are integers interpreted at one common scale `2 ^ precision`.
Addition and negation are exact.  Multiplication computes all four integer
corner products at double precision and rounds the lower endpoint down and
the upper endpoint up when returning to the common scale.  Consequently
intermediate numerator sizes remain bounded throughout a reflected numerical
certificate.
-/

set_option autoImplicit false

namespace GameTheory

/-- Integer endpoints representing the closed interval
`[lower / 2^precision, upper / 2^precision]`. -/
structure DyadicInterval (precision : ℕ) where
  lower : ℤ
  upper : ℤ
deriving DecidableEq, Repr

namespace DyadicInterval

variable {precision : ℕ}

/-- The positive common denominator used by every endpoint. -/
def scale (precision : ℕ) : ℤ := 2 ^ precision

@[simp] theorem scale_pos (precision : ℕ) : 0 < scale precision := by
  simp [scale]

@[simp] theorem scale_ne_zero (precision : ℕ) : scale precision ≠ 0 :=
  (scale_pos precision).ne'

/-- Interpret integer endpoints as an exact rational interval. -/
def toRationalInterval (interval : DyadicInterval precision) :
    RationalInterval :=
  ⟨interval.lower / scale precision, interval.upper / scale precision⟩

/-- Real semantic containment for a dyadic interval. -/
def Contains (interval : DyadicInterval precision) (value : ℝ) : Prop :=
  interval.toRationalInterval.Contains value

/-- Endpoint order, kept decidable for reflected certificate checks. -/
def Valid (interval : DyadicInterval precision) : Prop :=
  interval.lower ≤ interval.upper

instance (interval : DyadicInterval precision) : Decidable interval.Valid :=
  inferInstanceAs (Decidable (interval.lower ≤ interval.upper))

def valid (interval : DyadicInterval precision) : Bool :=
  decide interval.Valid

@[simp] theorem valid_eq_true_iff (interval : DyadicInterval precision) :
    interval.valid = true ↔ interval.Valid := by
  simp [valid]

/-- Smallest common-scale interval containing a rational number. -/
def ofRat (value : ℚ) : DyadicInterval precision :=
  ⟨Rat.floor (value * scale precision),
    Rat.ceil (value * scale precision)⟩

/-- Integers are exactly representable at every precision. -/
def ofInt (value : ℤ) : DyadicInterval precision :=
  ⟨value * scale precision, value * scale precision⟩

@[simp] theorem ofRat_intCast_eq_ofInt (value : ℤ) :
    (ofRat value : DyadicInterval precision) = ofInt value := by
  unfold ofRat ofInt
  congr 1
  · rw [← Int.cast_mul, Rat.floor_intCast]
  · rw [← Int.cast_mul, Rat.ceil_intCast]

@[simp] theorem ofRat_zero_eq_ofInt_zero :
    (ofRat 0 : DyadicInterval precision) = ofInt 0 := by
  simpa using ofRat_intCast_eq_ofInt (precision := precision) 0

@[simp] theorem ofRat_one_eq_ofInt_one :
    (ofRat 1 : DyadicInterval precision) = ofInt 1 := by
  simpa using ofRat_intCast_eq_ofInt (precision := precision) 1

def add (first second : DyadicInterval precision) :
    DyadicInterval precision :=
  ⟨first.lower + second.lower, first.upper + second.upper⟩

def neg (interval : DyadicInterval precision) : DyadicInterval precision :=
  ⟨-interval.upper, -interval.lower⟩

private def rectangleLower (first second : DyadicInterval precision) : ℤ :=
  min (first.lower * second.lower)
    (min (first.lower * second.upper)
      (min (first.upper * second.lower)
        (first.upper * second.upper)))

private def rectangleUpper (first second : DyadicInterval precision) : ℤ :=
  max (first.lower * second.lower)
    (max (first.lower * second.upper)
      (max (first.upper * second.lower)
        (first.upper * second.upper)))

/-- Four-corner multiplication followed by outward rounding back to the
common scale.  Integer division by the positive scale is Euclidean floor;
negating a floor of the negation implements ceiling. -/
def mul (first second : DyadicInterval precision) :
    DyadicInterval precision :=
  ⟨rectangleLower first second / scale precision,
    -((-rectangleUpper first second) / scale precision)⟩

@[simp] theorem add_ofInt_zero (interval : DyadicInterval precision) :
    interval.add (ofInt 0) = interval := by
  cases interval
  simp [add, ofInt]

@[simp] theorem ofInt_zero_add (interval : DyadicInterval precision) :
    (ofInt 0).add interval = interval := by
  cases interval
  simp [add, ofInt]

@[simp] theorem neg_ofInt_zero :
    (ofInt 0 : DyadicInterval precision).neg = ofInt 0 := by
  simp [neg, ofInt]

@[simp] theorem mul_ofInt_zero (interval : DyadicInterval precision) :
    interval.mul (ofInt 0) = ofInt 0 := by
  simp [mul, rectangleLower, rectangleUpper, ofInt]

@[simp] theorem ofInt_zero_mul (interval : DyadicInterval precision) :
    (ofInt 0).mul interval = ofInt 0 := by
  simp [mul, rectangleLower, rectangleUpper, ofInt]

private theorem floorDiv_scaled_le (value : ℤ) :
    ((((value / scale precision : ℤ) : ℚ) / scale precision)) ≤
      ((value : ℚ) / (scale precision * scale precision)) := by
  have hfloor :
      (value / scale precision) * scale precision ≤ value :=
    Int.ediv_mul_le value (scale_ne_zero precision)
  have hscaleQ : (0 : ℚ) < scale precision := by
    exact_mod_cast scale_pos precision
  rw [div_le_iff₀ hscaleQ]
  simp only [div_mul_eq_div_mul_one_div, one_div, mul_assoc,
    inv_mul_cancel₀ hscaleQ.ne', mul_one]
  rw [le_div_iff₀ hscaleQ]
  exact_mod_cast hfloor

private theorem scaled_le_ceilDiv (value : ℤ) :
    ((value : ℚ) / (scale precision * scale precision)) ≤
      (((-((-value) / scale precision) : ℤ) : ℚ) / scale precision) := by
  have hceil :
      value ≤ -((-value) / scale precision) * scale precision := by
    have hfloor := Int.ediv_mul_le (-value) (scale_ne_zero precision)
    simpa only [neg_mul, neg_neg] using neg_le_neg hfloor
  have hscaleQ : (0 : ℚ) < scale precision := by
    exact_mod_cast scale_pos precision
  rw [← div_div]
  rw [div_le_div_iff_of_pos_right hscaleQ]
  rw [div_le_iff₀ hscaleQ]
  exact_mod_cast hceil

private theorem quotient_mul_quotient (first second : ℤ) :
    ((first : ℚ) / scale precision) *
        ((second : ℚ) / scale precision) =
      ((first * second : ℤ) : ℚ) /
        (scale precision * scale precision) := by
  rw [div_mul_div_comm]
  norm_cast

private theorem roundedLower_le_corner
    (first second : DyadicInterval precision) (corner : ℤ)
    (hcorner : rectangleLower first second ≤ corner) :
    ((((rectangleLower first second / scale precision : ℤ) : ℚ) /
        scale precision)) ≤
      ((corner : ℚ) / (scale precision * scale precision)) := by
  refine (floorDiv_scaled_le (precision := precision)
    (rectangleLower first second)).trans ?_
  rw [div_le_div_iff_of_pos_right]
  · exact_mod_cast hcorner
  · exact_mod_cast mul_pos (scale_pos precision) (scale_pos precision)

private theorem corner_le_roundedUpper
    (first second : DyadicInterval precision) (corner : ℤ)
    (hcorner : corner ≤ rectangleUpper first second) :
    ((corner : ℚ) / (scale precision * scale precision)) ≤
      (((-((-rectangleUpper first second) / scale precision) : ℤ) : ℚ) /
        scale precision) := by
  refine (show
      ((corner : ℚ) / (scale precision * scale precision)) ≤
        ((rectangleUpper first second : ℚ) /
          (scale precision * scale precision)) from ?_).trans
    (scaled_le_ceilDiv (precision := precision)
      (rectangleUpper first second))
  rw [div_le_div_iff_of_pos_right]
  · exact_mod_cast hcorner
  · exact_mod_cast mul_pos (scale_pos precision) (scale_pos precision)

private theorem dyadicMulLower_le_rationalMulLower
    (first second : DyadicInterval precision) :
    (mul first second).toRationalInterval.lower ≤
      (first.toRationalInterval.mul
        second.toRationalInterval).lower := by
  change ((((rectangleLower first second / scale precision : ℤ) : ℚ) /
      scale precision)) ≤
    min (((first.lower : ℚ) / scale precision) *
        ((second.lower : ℚ) / scale precision))
      (min (((first.lower : ℚ) / scale precision) *
          ((second.upper : ℚ) / scale precision))
        (min (((first.upper : ℚ) / scale precision) *
            ((second.lower : ℚ) / scale precision))
          (((first.upper : ℚ) / scale precision) *
            ((second.upper : ℚ) / scale precision))))
  simp only [le_min_iff]
  constructor
  · rw [quotient_mul_quotient]
    exact roundedLower_le_corner first second _ (by
      simp [rectangleLower])
  · constructor
    · rw [quotient_mul_quotient]
      exact roundedLower_le_corner first second _ (by
        simp [rectangleLower])
    · constructor
      · rw [quotient_mul_quotient]
        exact roundedLower_le_corner first second _ (by
          simp [rectangleLower])
      · rw [quotient_mul_quotient]
        exact roundedLower_le_corner first second _ (by
          simp [rectangleLower])

private theorem rationalMulUpper_le_dyadicMulUpper
    (first second : DyadicInterval precision) :
    (first.toRationalInterval.mul
        second.toRationalInterval).upper ≤
      (mul first second).toRationalInterval.upper := by
  change max (((first.lower : ℚ) / scale precision) *
        ((second.lower : ℚ) / scale precision))
      (max (((first.lower : ℚ) / scale precision) *
          ((second.upper : ℚ) / scale precision))
        (max (((first.upper : ℚ) / scale precision) *
            ((second.lower : ℚ) / scale precision))
          (((first.upper : ℚ) / scale precision) *
            ((second.upper : ℚ) / scale precision)))) ≤
    (((-((-rectangleUpper first second) / scale precision) : ℤ) : ℚ) /
      scale precision)
  simp only [max_le_iff]
  constructor
  · rw [quotient_mul_quotient]
    exact corner_le_roundedUpper first second _ (by
      simp [rectangleUpper])
  · constructor
    · rw [quotient_mul_quotient]
      exact corner_le_roundedUpper first second _ (by
        simp [rectangleUpper])
    · constructor
      · rw [quotient_mul_quotient]
        exact corner_le_roundedUpper first second _ (by
          simp [rectangleUpper])
      · rw [quotient_mul_quotient]
        exact corner_le_roundedUpper first second _ (by
          simp [rectangleUpper])

theorem contains_ofRat (value : ℚ) :
    (ofRat value : DyadicInterval precision).Contains value := by
  have hscaleQ : (0 : ℚ) < scale precision := by
    exact_mod_cast scale_pos precision
  have hlower : (((Rat.floor (value * scale precision) : ℤ) : ℚ) /
      scale precision : ℚ) ≤ value := by
    rw [div_le_iff₀ hscaleQ]
    exact Rat.floor_le _
  have hupper : (value : ℚ) ≤
      ((Rat.ceil (value * scale precision) : ℤ) : ℚ) /
        scale precision := by
    rw [le_div_iff₀ hscaleQ]
    exact Rat.le_ceil
  rw [Contains, toRationalInterval, RationalInterval.Contains]
  constructor
  · exact_mod_cast hlower
  · exact_mod_cast hupper

theorem contains_ofInt (value : ℤ) :
    (ofInt value : DyadicInterval precision).Contains value := by
  have heq : (((value * scale precision : ℤ) : ℚ) /
      scale precision : ℚ) = value := by
    push_cast
    exact mul_div_cancel_right₀ (value : ℚ)
      (by exact_mod_cast scale_ne_zero precision)
  rw [Contains, toRationalInterval, RationalInterval.Contains]
  constructor
  · exact_mod_cast heq.le
  · exact_mod_cast heq.ge

theorem Contains.add {first second : DyadicInterval precision} {x y : ℝ}
    (hx : first.Contains x) (hy : second.Contains y) :
    (first.add second).Contains (x + y) := by
  simpa [Contains, toRationalInterval, DyadicInterval.add,
    RationalInterval.Contains,
    RationalInterval.add, add_div] using
    RationalInterval.Contains.add hx hy

theorem Contains.neg {interval : DyadicInterval precision} {x : ℝ}
    (hx : interval.Contains x) : interval.neg.Contains (-x) := by
  rw [Contains, toRationalInterval, RationalInterval.Contains] at hx ⊢
  constructor
  · simpa only [DyadicInterval.neg, Rat.cast_div, Rat.cast_neg,
      Int.cast_neg, neg_div] using neg_le_neg hx.2
  · simpa only [DyadicInterval.neg, Rat.cast_div, Rat.cast_neg,
      Int.cast_neg, neg_div] using neg_le_neg hx.1

/-- Soundness of outward-rounded dyadic multiplication. -/
theorem Contains.mul {first second : DyadicInterval precision} {x y : ℝ}
    (hx : first.Contains x) (hy : second.Contains y) :
    (first.mul second).Contains (x * y) := by
  have hproduct := RationalInterval.Contains.mul hx hy
  have hlower :
      (((first.mul second).toRationalInterval.lower : ℚ) : ℝ) ≤
        (((first.toRationalInterval.mul
          second.toRationalInterval).lower : ℚ) : ℝ) := by
    exact_mod_cast dyadicMulLower_le_rationalMulLower first second
  have hupper :
      (((first.toRationalInterval.mul
          second.toRationalInterval).upper : ℚ) : ℝ) ≤
        (((first.mul second).toRationalInterval.upper : ℚ) : ℝ) := by
    exact_mod_cast rationalMulUpper_le_dyadicMulUpper first second
  constructor
  · exact hlower.trans hproduct.1
  · exact hproduct.2.trans hupper

end DyadicInterval

end GameTheory
