import GameTheory.Math.GridBrouwerFourCorners
import GameTheory.Math.BooleanThreshold
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

/-!
# Approximate color signals for four-corner interpolation

Weighted color-one and color-two indicators reconstruct the canonical displacement vectors.
Taking a minimum with each interpolation weight avoids multiplying two variable scalars and
preserves indicator error. The coordinate error is at most twelve times the sum of weight and
indicator errors; arbitrary nonnegative indicator streams also give a bounded signal.
-/

namespace GameTheory.Math.Brouwer
open scoped BigOperators

/-- Weighted approximate color indicators reconstruct the canonical displacement coordinates. -/
def fourCornerColorSignal (w z1 z2 : Fin 4 → ℝ) : ℝ × ℝ :=
  (1 - 2 * ∑ i, min (w i) (z1 i) - ∑ i, min (w i) (z2 i),
   1 - ∑ i, min (w i) (z1 i) - 2 * ∑ i, min (w i) (z2 i))

theorem colorDisplacement_fst_indicator (c : Fin 3) :
    ((colorDisplacement c).1 : ℝ) =
      1 - 2 * (if c = 1 then 1 else 0) - (if c = 2 then 1 else 0) := by
  fin_cases c <;> norm_num [colorDisplacement]

theorem colorDisplacement_snd_indicator (c : Fin 3) :
    ((colorDisplacement c).2 : ℝ) =
      1 - (if c = 1 then 1 else 0) - 2 * (if c = 2 then 1 else 0) := by
  fin_cases c <;> norm_num [colorDisplacement]

private theorem sum_min_indicator_error (w w' z : Fin 4 → ℝ) (c : Fin 4 → Fin 3)
    (a : Fin 3) (ε η : ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hw : ∀ i, |w' i - w i| ≤ η)
    (hz : ∀ i, |z i - (if c i = a then 1 else 0)| ≤ ε) :
    |(∑ i, min (w' i) (z i)) - ∑ i, if c i = a then w i else 0| ≤ 4 * (η + ε) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |min (w' i) (z i) - (if c i = a then w i else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, (η + ε) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [decide_eq_true_eq] using
        booleanThreshold_min_weight_approx (decide (c i = a))
          (w i) (w' i) (z i) ε η (hw0 i) (hw1 i) (hw i)
          (by simpa only [decide_eq_true_eq] using hz i)
    _ = 4 * (η + ε) := by simp; ring
theorem weightedColorDisplacement_fst (w : Fin 4 → ℝ) (c : Fin 4 → Fin 3)
    (hsum : ∑ i, w i = 1) :
    (∑ i, w i * ((colorDisplacement (c i)).1 : ℝ)) =
      1 - 2 * (∑ i, if c i = 1 then w i else 0) - ∑ i, if c i = 2 then w i else 0 := by
  have hpoint (i : Fin 4) : w i * ((colorDisplacement (c i)).1 : ℝ) =
      w i - 2 * (if c i = 1 then w i else 0) - (if c i = 2 then w i else 0) := by
    generalize c i = a
    fin_cases a <;> norm_num [colorDisplacement]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]

theorem weightedColorDisplacement_snd (w : Fin 4 → ℝ) (c : Fin 4 → Fin 3)
    (hsum : ∑ i, w i = 1) :
    (∑ i, w i * ((colorDisplacement (c i)).2 : ℝ)) =
      1 - (∑ i, if c i = 1 then w i else 0) - 2 * ∑ i, if c i = 2 then w i else 0 := by
  have hpoint (i : Fin 4) : w i * ((colorDisplacement (c i)).2 : ℝ) =
      w i - (if c i = 1 then w i else 0) - 2 * (if c i = 2 then w i else 0) := by
    generalize c i = a
    fin_cases a <;> norm_num [colorDisplacement]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]

/-- Imperfect interpolation weights and indicators add their errors in each coordinate. -/
theorem fourCornerColorSignal_error_approx (w w' z1 z2 : Fin 4 → ℝ) (c : Fin 4 → Fin 3)
    (ε η : ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (hsum : ∑ i, w i = 1)
    (hw : ∀ i, |w' i - w i| ≤ η)
    (hz1 : ∀ i, |z1 i - (if c i = 1 then 1 else 0)| ≤ ε)
    (hz2 : ∀ i, |z2 i - (if c i = 2 then 1 else 0)| ≤ ε) :
    |(fourCornerColorSignal w' z1 z2).1 -
      (∑ i, w i * ((colorDisplacement (c i)).1 : ℝ))| ≤ 12 * (η + ε) ∧
    |(fourCornerColorSignal w' z1 z2).2 -
      (∑ i, w i * ((colorDisplacement (c i)).2 : ℝ))| ≤ 12 * (η + ε) := by
  have h1 := sum_min_indicator_error w w' z1 c 1 ε η hw0 hw1 hw hz1
  have h2 := sum_min_indicator_error w w' z2 c 2 ε η hw0 hw1 hw hz2
  rw [abs_le] at h1 h2
  rw [weightedColorDisplacement_fst w c hsum, weightedColorDisplacement_snd w c hsum]
  simp only [fourCornerColorSignal, abs_le]
  constructor <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Exact interpolation weights leave only the common indicator error. -/
theorem fourCornerColorSignal_error (w z1 z2 : Fin 4 → ℝ) (c : Fin 4 → Fin 3)
    (ε : ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (hsum : ∑ i, w i = 1)
    (hz1 : ∀ i, |z1 i - (if c i = 1 then 1 else 0)| ≤ ε)
    (hz2 : ∀ i, |z2 i - (if c i = 2 then 1 else 0)| ≤ ε) :
    |(fourCornerColorSignal w z1 z2).1 -
      (∑ i, w i * ((colorDisplacement (c i)).1 : ℝ))| ≤ 12 * ε ∧
    |(fourCornerColorSignal w z1 z2).2 -
      (∑ i, w i * ((colorDisplacement (c i)).2 : ℝ))| ≤ 12 * ε := by
  simpa only [zero_add] using fourCornerColorSignal_error_approx w w z1 z2 c ε 0
    hw0 hw1 hsum (fun i => by simp) hz1 hz2
private theorem weighted_sum_abs_le_one (w f : Fin 4 → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (hf : ∀ i, |f i| ≤ 1) : |∑ i, w i * f i| ≤ 1 := by
  calc
    _ ≤ ∑ i, |w i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |f i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (hw0 i)]
    _ ≤ ∑ i, w i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_of_le_one_right (hw0 i) (hf i)
    _ = 1 := hsum

/-- A convex combination of the canonical color vectors stays in the coordinate unit box. -/
theorem weightedColorDisplacement_abs_le_one (w : Fin 4 → ℝ) (c : Fin 4 → Fin 3)
    (hw0 : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    |∑ i, w i * ((colorDisplacement (c i)).1 : ℝ)| ≤ 1 ∧
    |∑ i, w i * ((colorDisplacement (c i)).2 : ℝ)| ≤ 1 := by
  constructor
  · apply weighted_sum_abs_le_one w _ hw0 hsum
    intro i
    generalize c i = a
    fin_cases a <;> norm_num [colorDisplacement]
  · apply weighted_sum_abs_le_one w _ hw0 hsum
    intro i
    generalize c i = a
    fin_cases a <;> norm_num [colorDisplacement]

/-- Canonical four-corner interpolation weights satisfy the signal error bound. -/
theorem fourCornerWeights_colorSignal_error {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (z1 z2 : Fin 4 → ℝ) (c : Fin 4 → Fin 3) (ε : ℝ)
    (hz1 : ∀ i, |z1 i - (if c i = 1 then 1 else 0)| ≤ ε)
    (hz2 : ∀ i, |z2 i - (if c i = 2 then 1 else 0)| ≤ ε) :
    |(fourCornerColorSignal (fourCornerWeights u v) z1 z2).1 -
      (∑ i, fourCornerWeights u v i * ((colorDisplacement (c i)).1 : ℝ))| ≤ 12 * ε ∧
    |(fourCornerColorSignal (fourCornerWeights u v) z1 z2).2 -
      (∑ i, fourCornerWeights u v i * ((colorDisplacement (c i)).2 : ℝ))| ≤ 12 * ε := by
  have hw0 := fourCornerWeights_nonneg hu0 hu1 hv0 hv1
  have hsum := fourCornerWeights_sum u v
  have hw1 (i : Fin 4) : fourCornerWeights u v i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hw0 j) (Finset.mem_univ i)
  exact fourCornerColorSignal_error _ z1 z2 c ε hw0 hw1 hsum hz1 hz2

/-- Nonnegative indicator streams give bounded signals without requiring their exclusivity. -/
theorem fourCornerColorSignal_abs_le_two (w z1 z2 : Fin 4 → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hz1 : ∀ i, 0 ≤ z1 i) (hz2 : ∀ i, 0 ≤ z2 i) :
    |(fourCornerColorSignal w z1 z2).1| ≤ 2 ∧
    |(fourCornerColorSignal w z1 z2).2| ≤ 2 := by
  have hbound (z : Fin 4 → ℝ) (hz : ∀ i, 0 ≤ z i) :
      0 ≤ ∑ i, min (w i) (z i) ∧ (∑ i, min (w i) (z i)) ≤ 1 := by
    constructor
    · exact Finset.sum_nonneg (fun i _ => le_min (hw0 i) (hz i))
    · rw [← hsum]
      exact Finset.sum_le_sum (fun i _ => min_le_left (w i) (z i))
  have h1 := hbound z1 hz1
  have h2 := hbound z2 hz2
  simp only [fourCornerColorSignal, abs_le]
  constructor <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Computed-weight error enlarges the loose signal bound without indicator exclusivity. -/
theorem fourCornerColorSignal_abs_le_two_approx (w w' z1 z2 : Fin 4 → ℝ) (η : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hw : ∀ i, |w' i - w i| ≤ η)
    (hz1 : ∀ i, 0 ≤ z1 i) (hz2 : ∀ i, 0 ≤ z2 i) :
    |(fourCornerColorSignal w' z1 z2).1| ≤ 2 + 12 * η ∧
    |(fourCornerColorSignal w' z1 z2).2| ≤ 2 + 12 * η := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (hw 0)
  have hbound (z : Fin 4 → ℝ) (hz : ∀ i, 0 ≤ z i) :
      -4 * η ≤ ∑ i, min (w' i) (z i) ∧ (∑ i, min (w' i) (z i)) ≤ 1 + 4 * η := by
    constructor
    · calc
        -4 * η = ∑ _i : Fin 4, -η := by simp
        _ ≤ ∑ i, min (w' i) (z i) := by
          apply Finset.sum_le_sum
          intro i _
          have hi := abs_le.mp (hw i)
          exact le_min (by linarith [hw0 i, hi.1]) (by linarith [hz i])
    · calc
        _ ≤ ∑ i, (w i + η) := by
          apply Finset.sum_le_sum
          intro i _
          have hi := abs_le.mp (hw i)
          exact (min_le_left _ _).trans (by linarith [hi.2])
        _ = 1 + 4 * η := by rw [Finset.sum_add_distrib, hsum]; simp
  have h1 := hbound z1 hz1
  have h2 := hbound z2 hz2
  simp only [fourCornerColorSignal, abs_le]
  constructor <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end GameTheory.Math.Brouwer
