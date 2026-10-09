import GameTheory.Math.GridBrouwerContinuous
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.MinMax

/-! Four-corner weights for the canonical rising-diagonal grid interpolation.
The same formula applies on both triangles, their diagonal and cell edges. -/

namespace GameTheory.Math.Brouwer
open scoped BigOperators

/-- Cell weights ordered by the origin, diagonal, horizontal and vertical corners. -/
def fourCornerWeights {R : Type*} [LinearOrder R] [Zero R] [One R] [Sub R]
    (u v : R) : Fin 4 → R :=
  ![1 - max u v, min u v, max (u - v) 0, max (v - u) 0]

/-- Rational cell weights cast to the same canonical real weights. -/
theorem fourCornerWeights_rat_cast (u v : ℚ) (i : Fin 4) :
    ((fourCornerWeights u v i : ℚ) : ℝ) = fourCornerWeights (u : ℝ) (v : ℝ) i := by
  fin_cases i <;> simp [fourCornerWeights]

private theorem sub_error_le {u v u' v' E : ℝ}
    (hu : |u - u'| ≤ E) (hv : |v - v'| ≤ E) :
    |(u - v) - (u' - v')| ≤ 2 * E := by
  calc
    |(u - v) - (u' - v')| = |(u - u') - (v - v')| := by congr 1; ring
    _ ≤ |u - u'| + |v - v'| := abs_sub _ _
    _ ≤ 2 * E := by linarith

/-- Perturbing both cell coordinates by at most `E` changes each weight by at most `2 * E`.
The estimate applies to arbitrary real inputs, including points outside the cell. -/
theorem fourCornerWeights_perturbation {u v u' v' E : ℝ}
    (hu : |u - u'| ≤ E) (hv : |v - v'| ≤ E) (i : Fin 4) :
    |fourCornerWeights u v i - fourCornerWeights u' v' i| ≤ 2 * E := by
  have hE : 0 ≤ E := (abs_nonneg _).trans hu
  fin_cases i
  · change |(1 - max u v) - (1 - max u' v')| ≤ 2 * E
    have he : (1 - max u v) - (1 - max u' v') = -(max u v - max u' v') := by ring
    rw [he, abs_neg]
    exact (abs_max_sub_max_le_max u v u' v').trans ((max_le hu hv).trans (by linarith))
  · change |min u v - min u' v'| ≤ 2 * E
    exact (abs_min_sub_min_le_max u v u' v').trans ((max_le hu hv).trans (by linarith))
  · change |max (u - v) 0 - max (u' - v') 0| ≤ 2 * E
    exact (abs_max_sub_max_le_abs _ _ _).trans (sub_error_le hu hv)
  · change |max (v - u) 0 - max (v' - u') 0| ≤ 2 * E
    exact (abs_max_sub_max_le_abs _ _ _).trans (sub_error_le hv hu)

theorem fourCornerWeights_sum {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (u v : R) : ∑ i, fourCornerWeights u v i = 1 := by
  by_cases hvu : v ≤ u
  · simp [fourCornerWeights, Fin.sum_univ_succ, max_eq_left hvu, min_eq_right hvu,
      max_eq_left (sub_nonneg.mpr hvu), max_eq_right (sub_nonpos.mpr hvu)]
  · have huv := le_of_not_ge hvu
    simp [fourCornerWeights, Fin.sum_univ_succ, max_eq_right huv, min_eq_left huv,
      max_eq_right (sub_nonpos.mpr huv), max_eq_left (sub_nonneg.mpr huv)]

theorem fourCornerWeights_nonneg {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {u v : R} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (i : Fin 4) : 0 ≤ fourCornerWeights u v i := by
  fin_cases i
  · exact sub_nonneg.mpr (max_le hu1 hv1)
  · exact le_min hu0 hv0
  · exact le_max_right _ _
  · exact le_max_right _ _

theorem sum_vertexHat_fourCorners (f : ℕ → ℕ → ℝ) {n x y : ℕ}
    (hx : x < n) (hy : y < n) {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      vertexHat i j ((x : ℝ) + u, (y : ℝ) + v) * f i j) =
      ∑ a : Fin 4, fourCornerWeights u v a *
        ![f x y, f (x + 1) (y + 1), f (x + 1) y, f x (y + 1)] a := by
  by_cases hvu : v ≤ u
  · rw [sum_vertexHat_lower f hx hy hv0 hvu hu1]
    simp [fourCornerWeights, Fin.sum_univ_succ, max_eq_left hvu, min_eq_right hvu,
      max_eq_left (sub_nonneg.mpr hvu), max_eq_right (sub_nonpos.mpr hvu)]
    ring
  · have huv := le_of_not_ge hvu
    rw [sum_vertexHat_upper f hx hy hu0 huv hv1]
    simp [fourCornerWeights, Fin.sum_univ_succ, max_eq_right huv, min_eq_left huv,
      max_eq_right (sub_nonpos.mpr huv), max_eq_left (sub_nonneg.mpr huv)]
    ring


/-- The interpolated displacement is a convex combination of the four cell colors. -/
theorem globalGridMap_fourCorners (color : ℕ → ℕ → Fin 3) {n x y : ℕ}
    (hx : x < n) (hy : y < n) {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    globalGridMap color n ((x : ℝ) + u, (y : ℝ) + v) =
      ((x : ℝ) + u + ∑ a : Fin 4, fourCornerWeights u v a *
        ![((colorDisplacement (color x y)).1 : ℝ),
          ((colorDisplacement (color (x + 1) (y + 1))).1 : ℝ),
          ((colorDisplacement (color (x + 1) y)).1 : ℝ),
          ((colorDisplacement (color x (y + 1))).1 : ℝ)] a,
       (y : ℝ) + v + ∑ a : Fin 4, fourCornerWeights u v a *
        ![((colorDisplacement (color x y)).2 : ℝ),
          ((colorDisplacement (color (x + 1) (y + 1))).2 : ℝ),
          ((colorDisplacement (color (x + 1) y)).2 : ℝ),
          ((colorDisplacement (color x (y + 1))).2 : ℝ)] a) := by
  apply Prod.ext <;> dsimp only [globalGridMap] <;>
    rw [sum_vertexHat_fourCorners _ hx hy hu0 hu1 hv0 hv1]

/-- First-coordinate displacement on a cell, including its edges and diagonal. -/
theorem globalGridMap_fourCorners_fst_sub (color : ℕ → ℕ → Fin 3) {n x y : ℕ}
    (hx : x < n) (hy : y < n) {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (globalGridMap color n ((x : ℝ) + u, (y : ℝ) + v)).1 - ((x : ℝ) + u) =
      ∑ a : Fin 4, fourCornerWeights u v a *
        ![((colorDisplacement (color x y)).1 : ℝ),
          ((colorDisplacement (color (x + 1) (y + 1))).1 : ℝ),
          ((colorDisplacement (color (x + 1) y)).1 : ℝ),
          ((colorDisplacement (color x (y + 1))).1 : ℝ)] a := by
  rw [globalGridMap_fourCorners color hx hy hu0 hu1 hv0 hv1]
  exact add_sub_cancel_left _ _

/-- Second-coordinate displacement on a cell, including its edges and diagonal. -/
theorem globalGridMap_fourCorners_snd_sub (color : ℕ → ℕ → Fin 3) {n x y : ℕ}
    (hx : x < n) (hy : y < n) {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (globalGridMap color n ((x : ℝ) + u, (y : ℝ) + v)).2 - ((y : ℝ) + v) =
      ∑ a : Fin 4, fourCornerWeights u v a *
        ![((colorDisplacement (color x y)).2 : ℝ),
          ((colorDisplacement (color (x + 1) (y + 1))).2 : ℝ),
          ((colorDisplacement (color (x + 1) y)).2 : ℝ),
          ((colorDisplacement (color x (y + 1))).2 : ℝ)] a := by
  rw [globalGridMap_fourCorners color hx hy hu0 hu1 hv0 hv1]
  exact add_sub_cancel_left _ _
end GameTheory.Math.Brouwer
