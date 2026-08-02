/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Exact rational interval evaluation for quitting certificates

This is a deliberately small reflected checker.  Interval endpoints and all
checker computations live in `ℚ`; `Contains` is the sole semantic bridge to
`ℝ`.  Polynomial automatic differentiation is evaluated directly, avoiding
the expression blow-up caused by materializing every symbolic derivative.
-/

set_option autoImplicit false

namespace GameTheory

/-- A pair of exact rational endpoints.  Certificate checkers separately
verify that `lower ≤ upper`; semantic containment itself does not need that
invariant bundled into every arithmetic operation. -/
structure RationalInterval where
  lower : ℚ
  upper : ℚ
deriving DecidableEq, Repr

namespace RationalInterval

/-- Endpoint order, kept as a decidable proposition for reflective checks. -/
def Valid (interval : RationalInterval) : Prop :=
  interval.lower ≤ interval.upper

instance (interval : RationalInterval) : Decidable interval.Valid :=
  inferInstanceAs (Decidable (interval.lower ≤ interval.upper))

/-- Boolean form used by generated certificate checks. -/
def valid (interval : RationalInterval) : Bool :=
  decide interval.Valid

@[simp] theorem valid_eq_true_iff (interval : RationalInterval) :
    interval.valid = true ↔ interval.Valid := by
  simp [valid]

/-- A real number is represented by an exact rational interval. -/
def Contains (interval : RationalInterval) (value : ℝ) : Prop :=
  (interval.lower : ℝ) ≤ value ∧ value ≤ (interval.upper : ℝ)

/-- Degenerate interval containing one rational number. -/
def point (value : ℚ) : RationalInterval := ⟨value, value⟩

/-- Exact interval addition. -/
def add (first second : RationalInterval) : RationalInterval :=
  ⟨first.lower + second.lower, first.upper + second.upper⟩

/-- Exact interval negation. -/
def neg (interval : RationalInterval) : RationalInterval :=
  ⟨-interval.upper, -interval.lower⟩

private def rectangleMulLower (a b c d : ℝ) : ℝ :=
  min (a * c) (min (a * d) (min (b * c) (b * d)))

private def rectangleMulUpper (a b c d : ℝ) : ℝ :=
  max (a * c) (max (a * d) (max (b * c) (b * d)))

/-- The lower four-corner product bounds every product in a real rectangle. -/
private theorem rectangleMulLower_le
    {a b c d x y : ℝ} (hax : a ≤ x) (hxb : x ≤ b)
    (hcy : c ≤ y) (hyd : y ≤ d) :
    rectangleMulLower a b c d ≤ x * y := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · by_cases ha : 0 ≤ a
      · calc
          rectangleMulLower a b c d ≤ a * c := by
            simp [rectangleMulLower]
          _ ≤ a * y := mul_le_mul_of_nonneg_left hcy ha
          _ ≤ x * y := mul_le_mul_of_nonneg_right hax hy
      · have ha' : a ≤ 0 := le_of_not_ge ha
        calc
          rectangleMulLower a b c d ≤ a * d := by
            simp [rectangleMulLower]
          _ ≤ a * y := mul_le_mul_of_nonpos_left hyd ha'
          _ ≤ x * y := mul_le_mul_of_nonneg_right hax hy
    · have hy' : y ≤ 0 := le_of_not_ge hy
      have hc : c ≤ 0 := hcy.trans hy'
      calc
        rectangleMulLower a b c d ≤ b * c := by
          simp [rectangleMulLower]
        _ ≤ x * c := mul_le_mul_of_nonpos_right hxb hc
        _ ≤ x * y := mul_le_mul_of_nonneg_left hcy hx
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have ha : a ≤ 0 := hax.trans hx'
    by_cases hy : 0 ≤ y
    · have hd : 0 ≤ d := hy.trans hyd
      calc
        rectangleMulLower a b c d ≤ a * d := by
          simp [rectangleMulLower]
        _ ≤ x * d := mul_le_mul_of_nonneg_right hax hd
        _ ≤ x * y := mul_le_mul_of_nonpos_left hyd hx'
    · have hy' : y ≤ 0 := le_of_not_ge hy
      by_cases hb : b ≤ 0
      · by_cases hd : d ≤ 0
        · calc
            rectangleMulLower a b c d ≤ b * d := by
              simp [rectangleMulLower]
            _ ≤ x * d := mul_le_mul_of_nonpos_right hxb hd
            _ ≤ x * y := mul_le_mul_of_nonpos_left hyd hx'
        · have hd0 : 0 ≤ d := le_of_lt (lt_of_not_ge hd)
          calc
            rectangleMulLower a b c d ≤ a * d := by
              simp [rectangleMulLower]
            _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha hd0
            _ ≤ x * y := mul_nonneg_of_nonpos_of_nonpos hx' hy'
      · have hb0 : 0 ≤ b := le_of_lt (lt_of_not_ge hb)
        have hc : c ≤ 0 := hcy.trans hy'
        calc
          rectangleMulLower a b c d ≤ b * c := by
            simp [rectangleMulLower]
          _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb0 hc
          _ ≤ x * y := mul_nonneg_of_nonpos_of_nonpos hx' hy'

/-- The upper four-corner product bounds every product in a real rectangle. -/
private theorem le_rectangleMulUpper
    {a b c d x y : ℝ} (hax : a ≤ x) (hxb : x ≤ b)
    (hcy : c ≤ y) (hyd : y ≤ d) :
    x * y ≤ rectangleMulUpper a b c d := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · have hb : 0 ≤ b := hx.trans hxb
      calc
        x * y ≤ b * y := mul_le_mul_of_nonneg_right hxb hy
        _ ≤ b * d := mul_le_mul_of_nonneg_left hyd hb
        _ ≤ rectangleMulUpper a b c d := by
          simp [rectangleMulUpper]
    · have hy' : y ≤ 0 := le_of_not_ge hy
      by_cases ha : 0 ≤ a
      · calc
          x * y ≤ a * y := mul_le_mul_of_nonpos_right hax hy'
          _ ≤ a * d := mul_le_mul_of_nonneg_left hyd ha
          _ ≤ rectangleMulUpper a b c d := by
            simp [rectangleMulUpper]
      · have ha' : a ≤ 0 := le_of_not_ge ha
        have hc : c ≤ 0 := hcy.trans hy'
        calc
          x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx hy'
          _ ≤ a * c := mul_nonneg_of_nonpos_of_nonpos ha' hc
          _ ≤ rectangleMulUpper a b c d := by
            simp [rectangleMulUpper]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have ha : a ≤ 0 := hax.trans hx'
    by_cases hy : 0 ≤ y
    · by_cases hc : 0 ≤ c
      · calc
          x * y ≤ x * c := mul_le_mul_of_nonpos_left hcy hx'
          _ ≤ b * c := mul_le_mul_of_nonneg_right hxb hc
          _ ≤ rectangleMulUpper a b c d := by
            simp [rectangleMulUpper]
      · have hc' : c ≤ 0 := le_of_not_ge hc
        calc
          x * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx' hy
          _ ≤ a * c := mul_nonneg_of_nonpos_of_nonpos ha hc'
          _ ≤ rectangleMulUpper a b c d := by
            simp [rectangleMulUpper]
    · have hy' : y ≤ 0 := le_of_not_ge hy
      calc
        x * y ≤ a * y := mul_le_mul_of_nonpos_right hax hy'
        _ ≤ a * c := mul_le_mul_of_nonpos_left hcy ha
        _ ≤ rectangleMulUpper a b c d := by
          simp [rectangleMulUpper]

/-- Full four-corner interval multiplication. -/
def mul (first second : RationalInterval) : RationalInterval :=
  ⟨min (first.lower * second.lower)
      (min (first.lower * second.upper)
        (min (first.upper * second.lower)
          (first.upper * second.upper))),
    max (first.lower * second.lower)
      (max (first.lower * second.upper)
        (max (first.upper * second.lower)
          (first.upper * second.upper)))⟩

theorem contains_point (value : ℚ) : Contains (point value) value := by
  simp [Contains, point]

theorem valid_point (value : ℚ) : (point value).Valid := by
  exact le_rfl

theorem Valid.add {first second : RationalInterval}
    (hfirst : first.Valid) (hsecond : second.Valid) :
    (first.add second).Valid := by
  exact add_le_add hfirst hsecond

theorem Valid.neg {interval : RationalInterval} (hinterval : interval.Valid) :
    interval.neg.Valid := by
  exact neg_le_neg hinterval

/-- Four-corner multiplication always produces ordered endpoints. -/
theorem valid_mul (first second : RationalInterval) :
    (first.mul second).Valid := by
  exact (min_le_left _ _).trans (le_max_left _ _)

theorem Contains.add {first second : RationalInterval} {x y : ℝ}
    (hx : first.Contains x) (hy : second.Contains y) :
    (first.add second).Contains (x + y) := by
  change (((first.lower + second.lower : ℚ) : ℝ) ≤ x + y) ∧
    (x + y ≤ ((first.upper + second.upper : ℚ) : ℝ))
  constructor
  · simpa only [Rat.cast_add] using add_le_add hx.1 hy.1
  · simpa only [Rat.cast_add] using add_le_add hx.2 hy.2

theorem Contains.neg {interval : RationalInterval} {x : ℝ}
    (hx : interval.Contains x) : interval.neg.Contains (-x) := by
  change (((-interval.upper : ℚ) : ℝ) ≤ -x) ∧
    (-x ≤ ((-interval.lower : ℚ) : ℝ))
  constructor
  · simpa only [Rat.cast_neg] using neg_le_neg hx.2
  · simpa only [Rat.cast_neg] using neg_le_neg hx.1

/-- Soundness of exact four-corner rational interval multiplication. -/
theorem Contains.mul {first second : RationalInterval} {x y : ℝ}
    (hx : first.Contains x) (hy : second.Contains y) :
    (first.mul second).Contains (x * y) := by
  change (((min (first.lower * second.lower)
      (min (first.lower * second.upper)
        (min (first.upper * second.lower)
          (first.upper * second.upper))) : ℚ) : ℝ) ≤ x * y) ∧
    (x * y ≤ ((max (first.lower * second.lower)
      (max (first.lower * second.upper)
        (max (first.upper * second.lower)
          (first.upper * second.upper))) : ℚ) : ℝ))
  constructor
  · simpa only [Rat.cast_min, Rat.cast_mul,
      rectangleMulLower] using
      rectangleMulLower_le hx.1 hx.2 hy.1 hy.2
  · simpa only [Rat.cast_max, Rat.cast_mul,
      rectangleMulUpper] using
      le_rectangleMulUpper hx.1 hx.2 hy.1 hy.2

end RationalInterval

end GameTheory
