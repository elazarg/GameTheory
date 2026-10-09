import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Clipped subtraction implements a minimum

Two affine subtraction steps, each clipped to the unit interval, compute the minimum of a unit
weight and a nonnegative signal. Clipping is nonexpansive, so imperfect inputs and bounded step
errors give an explicit output error bound. Approximate inputs may lie outside the unit interval.
-/

namespace GameTheory.Math
variable {F : Type*} [CommRing F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Literal clipping to the unit interval does not increase absolute differences. -/
theorem unitClamp_nonexpansive (x y : F) :
    |max 0 (min 1 x) - max 0 (min 1 y)| ≤ |x - y| := by
  have hmax := abs_max_sub_max_le_max (0 : F) (min 1 x) 0 (min 1 y)
  have hmin := abs_min_sub_min_le_max (1 : F) x 1 y
  simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (min 1 x - min 1 y))] at hmax
  simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (x - y))] at hmin
  exact hmax.trans hmin

omit [IsStrictOrderedRing F] in
/-- Clipping fixes each point in the closed unit interval. -/
theorem unitClamp_eq_self {x : F} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    max 0 (min 1 x) = x := by rw [min_eq_right hx1, max_eq_right hx0]

/-- Two clipped affine subtractions compute the minimum of a unit weight
and a nonnegative signal. -/
theorem min_eq_clipped_sub {w z : F} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hz0 : 0 ≤ z) :
    min w z = max 0 (min 1 (w - max 0 (min 1 (w - z)))) := by
  rcases le_total w z with h | h
  · have hc : max 0 (min 1 (w - z)) = 0 :=
      max_eq_left ((min_le_right _ _).trans (sub_nonpos.mpr h))
    rw [min_eq_left h, hc, sub_zero, unitClamp_eq_self hw0 hw1]
  · have hd0 : 0 ≤ w - z := sub_nonneg.mpr h
    have hd1 : w - z ≤ 1 := by linarith
    rw [min_eq_right h, unitClamp_eq_self hd0 hd1]
    have he : w - (w - z) = z := by ring
    rw [he, unitClamp_eq_self hz0 (h.trans hw1)]

/-- Two approximate clipped subtractions propagate weight, signal and step errors. -/
theorem clippedSub_min_error (w z w' z' t out η ε δ : F)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hz0 : 0 ≤ z)
    (hw : |w' - w| ≤ η) (hz : |z' - z| ≤ ε)
    (ht : |t - max 0 (min 1 (w' - z'))| ≤ δ)
    (hout : |out - max 0 (min 1 (w' - t))| ≤ δ) :
    |out - min w z| ≤ 2 * δ + 2 * η + ε := by
  have hin : |t - max 0 (min 1 (w - z))| ≤ δ + η + ε := by
    have hc := unitClamp_nonexpansive (w' - z') (w - z)
    have he : (w' - z') - (w - z) = (w' - w) - (z' - z) := by ring
    rw [he] at hc
    have hd := abs_sub_le (w' - w) (0 : F) (z' - z)
    simp only [sub_zero, zero_sub, abs_neg] at hd
    have hs := abs_sub_le t (max 0 (min 1 (w' - z'))) (max 0 (min 1 (w - z)))
    linarith
  rw [min_eq_clipped_sub hw0 hw1 hz0]
  have hc := unitClamp_nonexpansive (w' - t) (w - max 0 (min 1 (w - z)))
  have he : (w' - t) - (w - max 0 (min 1 (w - z))) =
      (w' - w) - (t - max 0 (min 1 (w - z))) := by ring
  rw [he] at hc
  have hd := abs_sub_le (w' - w) (0 : F) (t - max 0 (min 1 (w - z)))
  simp only [sub_zero, zero_sub, abs_neg] at hd
  have hs := abs_sub_le out (max 0 (min 1 (w' - t)))
    (max 0 (min 1 (w - max 0 (min 1 (w - z)))))
  linarith

end GameTheory.Math
