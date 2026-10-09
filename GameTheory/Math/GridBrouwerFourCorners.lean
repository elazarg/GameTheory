import GameTheory.Math.GridBrouwerContinuous
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-! Four-corner weights for the canonical rising-diagonal grid interpolation.
The same formula applies on both triangles, their diagonal and cell edges. -/

namespace GameTheory.Math.Brouwer
open scoped BigOperators

/-- Cell weights ordered by the origin, diagonal, horizontal and vertical corners. -/
def fourCornerWeights (u v : ℝ) : Fin 4 → ℝ :=
  ![1 - max u v, min u v, max (u - v) 0, max (v - u) 0]

theorem fourCornerWeights_sum (u v : ℝ) : ∑ i, fourCornerWeights u v i = 1 := by
  by_cases hvu : v ≤ u
  · simp [fourCornerWeights, Fin.sum_univ_succ, max_eq_left hvu, min_eq_right hvu,
      max_eq_left (sub_nonneg.mpr hvu), max_eq_right (sub_nonpos.mpr hvu)]
  · have huv := le_of_not_ge hvu
    simp [fourCornerWeights, Fin.sum_univ_succ, max_eq_right huv, min_eq_left huv,
      max_eq_right (sub_nonpos.mpr huv), max_eq_left (sub_nonneg.mpr huv)]

theorem fourCornerWeights_nonneg {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
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
