import GameTheory.Math.GridBrouwer
import Mathlib.Tactic.Linarith

/-! Affine maps on the triangles of a colored square grid. Boundary exclusions
keep the displaced vertices in the square; convex interpolation therefore
preserves the square on every triangle. -/

namespace GameTheory.Math.Brouwer

open Sperner

/-- A rational point belongs to the closed square of side length `n`. -/
def InGridSquare (n : ℕ) (p : ℚ × ℚ) : Prop :=
  (0 ≤ p.1 ∧ p.1 ≤ n) ∧ (0 ≤ p.2 ∧ p.2 ≤ n)

/-- Displace a grid vertex by its color vector. -/
def vertexImage (color : ℕ → ℕ → Fin 3) (i j : ℕ) : ℚ × ℚ :=
  ((i : ℚ) + (colorDisplacement (color i j)).1,
    (j : ℚ) + (colorDisplacement (color i j)).2)

private theorem displacedCoordinate_bounds {n k : ℕ} {d : ℚ}
    (hk : k ≤ n) (hd : -1 ≤ d ∧ d ≤ 1)
    (hzero : k = 0 → 0 ≤ d) (hend : k = n → d ≤ 0) :
    0 ≤ (k : ℚ) + d ∧ (k : ℚ) + d ≤ n := by
  constructor
  · by_cases h : k = 0
    · simpa [h] using hzero h
    · have hk' : (1 : ℚ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      linarith [hd.1]
  · by_cases h : k = n
    · have hd' := hend h
      simp only [h]
      linarith
    · have hk' : (k : ℚ) + 1 ≤ n := by
        exact_mod_cast (show k + 1 ≤ n by omega)
      linarith [hd.2]

/-- Boundary exclusions and the unit displacement bound keep every vertex in the square. -/
theorem vertexImage_mem_square {color : ℕ → ℕ → Fin 3} {n i j : ℕ}
    (hb : GridBoundary color n) (hi : i ≤ n) (hj : j ≤ n) :
    InGridSquare n (vertexImage color i j) := by
  have hv : (-1 ≤ (colorDisplacement (color i j)).1 ∧
      (colorDisplacement (color i j)).1 ≤ 1) ∧
      (-1 ≤ (colorDisplacement (color i j)).2 ∧
      (colorDisplacement (color i j)).2 ≤ 1) := by
    generalize color i j = a
    fin_cases a <;> norm_num [colorDisplacement]
  obtain ⟨hl, hb', hr, ht⟩ := gridBoundary_inward hb
  refine ⟨displacedCoordinate_bounds hi hv.1 ?_ ?_,
    displacedCoordinate_bounds hj hv.2 ?_ ?_⟩
  · intro h
    simpa [h] using hl j hj
  · intro h
    simpa [h] using hr j hj
  · intro h
    simpa [h] using hb' i hi
  · intro h
    simpa [h] using ht i hi

/-- The point in a grid triangle with the supplied barycentric weights. -/
def trianglePoint (t : GridTriangle) (u v w : ℚ) : ℚ × ℚ :=
  (u * (corner t 0).1 + v * (corner t 1).1 + w * (corner t 2).1,
    u * (corner t 0).2 + v * (corner t 1).2 + w * (corner t 2).2)

/-- Affine interpolation of the displaced vertices of a grid triangle. -/
def triangleImage (color : ℕ → ℕ → Fin 3) (t : GridTriangle)
    (u v w : ℚ) : ℚ × ℚ :=
  (u * (vertexImage color (corner t 0).1 (corner t 0).2).1 +
      v * (vertexImage color (corner t 1).1 (corner t 1).2).1 +
      w * (vertexImage color (corner t 2).1 (corner t 2).2).1,
    u * (vertexImage color (corner t 0).1 (corner t 0).2).2 +
      v * (vertexImage color (corner t 1).1 (corner t 1).2).2 +
      w * (vertexImage color (corner t 2).1 (corner t 2).2).2)

/-- Affine interpolation is the original point plus its interpolated displacement. -/
theorem triangleImage_eq_point_add_displacement (color : ℕ → ℕ → Fin 3)
    (t : GridTriangle) (u v w : ℚ) :
    triangleImage color t u v w =
      let d := weightedDisplacement (color (corner t 0).1 (corner t 0).2)
        (color (corner t 1).1 (corner t 1).2)
        (color (corner t 2).1 (corner t 2).2) u v w
      ((trianglePoint t u v w).1 + d.1, (trianglePoint t u v w).2 + d.2) := by
  apply Prod.ext <;>
    dsimp [triangleImage, trianglePoint, vertexImage, weightedDisplacement] <;> ring

/-- Small image-minus-point residuals identify a trichromatic triangle. -/
theorem triangleImage_small_implies_trichromatic (color : ℕ → ℕ → Fin 3)
    (t : GridTriangle) (u v w : ℚ) (hs : u + v + w = 1)
    (hx : |(triangleImage color t u v w).1 - (trianglePoint t u v w).1| ≤ 1 / 6)
    (hy : |(triangleImage color t u v w).2 - (trianglePoint t u v w).2| ≤ 1 / 6) :
    Trichromatic (color (corner t 0).1 (corner t 0).2)
      (color (corner t 1).1 (corner t 1).2)
      (color (corner t 2).1 (corner t 2).2) := by
  rw [triangleImage_eq_point_add_displacement] at hx hy
  simp only [add_sub_cancel_left] at hx hy
  exact weightedDisplacement_small_implies_trichromatic _ _ _ u v w hs hx hy

/-- At the barycenter, the affine image uses the equal-weight color displacement. -/
theorem triangleImage_barycenter (color : ℕ → ℕ → Fin 3) (t : GridTriangle) :
    triangleImage color t (1 / 3) (1 / 3) (1 / 3) =
      ((trianglePoint t (1 / 3) (1 / 3) (1 / 3)).1 +
          (triangleBarycenterDisplacement color t).1,
        (trianglePoint t (1 / 3) (1 / 3) (1 / 3)).2 +
          (triangleBarycenterDisplacement color t).2) := by
  exact triangleImage_eq_point_add_displacement color t (1 / 3) (1 / 3) (1 / 3)

/-- A triangle's barycenter is fixed precisely when its vertex colors are distinct. -/
theorem triangleImage_barycenter_fixed_iff (color : ℕ → ℕ → Fin 3)
    (t : GridTriangle) :
    triangleImage color t (1 / 3) (1 / 3) (1 / 3) =
        trianglePoint t (1 / 3) (1 / 3) (1 / 3) ↔
      Trichromatic (color (corner t 0).1 (corner t 0).2)
        (color (corner t 1).1 (corner t 1).2)
        (color (corner t 2).1 (corner t 2).2) := by
  rw [triangleImage_barycenter]
  simpa only [Prod.ext_iff, add_eq_left, Prod.fst, Prod.snd] using
    triangleBarycenterDisplacement_eq_zero_iff color t

/-- Every boundary-respecting grid has a valid triangle with a fixed barycenter. -/
theorem exists_grid_fixed_barycenter {color : ℕ → ℕ → Fin 3} {n : ℕ}
    (hb : GridBoundary color n) :
    ∃ t, ValidTriangle n t ∧
      triangleImage color t (1 / 3) (1 / 3) (1 / 3) =
        trianglePoint t (1 / 3) (1 / 3) (1 / 3) := by
  obtain ⟨t, ht, hz⟩ := exists_grid_zero_displacement hb
  exact ⟨t, ht, (triangleImage_barycenter_fixed_iff color t).mpr
    ((triangleBarycenterDisplacement_eq_zero_iff color t).mp hz)⟩

private theorem convexThree_bounds {n a b c u v w : ℚ}
    (ha : 0 ≤ a ∧ a ≤ n) (hb : 0 ≤ b ∧ b ≤ n) (hc : 0 ≤ c ∧ c ≤ n)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hs : u + v + w = 1) :
    0 ≤ u * a + v * b + w * c ∧ u * a + v * b + w * c ≤ n := by
  constructor
  · exact add_nonneg (add_nonneg (mul_nonneg hu ha.1) (mul_nonneg hv hb.1))
      (mul_nonneg hw hc.1)
  · have h₁ := mul_le_mul_of_nonneg_left ha.2 hu
    have h₂ := mul_le_mul_of_nonneg_left hb.2 hv
    have h₃ := mul_le_mul_of_nonneg_left hc.2 hw
    nlinarith

private theorem corner_le {n : ℕ} {t : GridTriangle} (ht : ValidTriangle n t)
    (p : Fin 3) : (corner t p).1 ≤ n ∧ (corner t p).2 ≤ n := by
  rcases t with ⟨x, y, upper⟩
  change x < n ∧ y < n at ht
  cases upper <;> fin_cases p <;> simp [corner] <;> omega

/-- Nonnegative barycentric interpolation of a valid triangle preserves the square. -/
theorem triangleImage_mem_square {color : ℕ → ℕ → Fin 3} {n : ℕ}
    (hb : GridBoundary color n) {t : GridTriangle} (ht : ValidTriangle n t)
    {u v w : ℚ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hs : u + v + w = 1) : InGridSquare n (triangleImage color t u v w) := by
  have hcorner (p : Fin 3) := vertexImage_mem_square hb
    (corner_le ht p).1 (corner_le ht p).2
  exact ⟨convexThree_bounds (hcorner 0).1 (hcorner 1).1 (hcorner 2).1 hu hv hw hs,
    convexThree_bounds (hcorner 0).2 (hcorner 1).2 (hcorner 2).2 hu hv hw hs⟩

end GameTheory.Math.Brouwer
