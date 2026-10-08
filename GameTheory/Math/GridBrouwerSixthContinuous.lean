import GameTheory.Math.GridBrouwerContinuous
import GameTheory.Math.GridBrouwerSixthGeometry

/-! The finite sixth-grid representation evaluates the globally continuous
normalized grid map exactly. Its rational local residual test is equivalent
to the real approximate fixed-point inequality at the represented point. -/

namespace GameTheory.Math.Brouwer

open Sperner

/-- The exact local displacement at the point selected by its sixth-grid numerators. -/
def sixthDisplacement (color : ℕ → ℕ → Fin 3) (n X Y : ℕ) : ℚ × ℚ :=
  let t := sixthTriangle n X Y
  weightedDisplacement (color (corner t 0).1 (corner t 0).2)
    (color (corner t 1).1 (corner t 1).2)
    (color (corner t 2).1 (corner t 2).2)
    (sixthWeights n X Y 0) (sixthWeights n X Y 1) (sixthWeights n X Y 2)

/-- The normalized real point denoted by two sixth-grid numerators. -/
noncomputable def sixthRealPoint (n X Y : ℕ) : ℝ × ℝ :=
  ((X : ℝ) / (6 * n), (Y : ℝ) / (6 * n))

/-- Coordinatewise residual at the represented point, with precision scaled to the grid. -/
def SixthPointSmallResidual (color : ℕ → ℕ → Fin 3) (n X Y : ℕ) : Prop :=
  |(normalizedGridMap color n (sixthRealPoint n X Y)).1 -
      (sixthRealPoint n X Y).1| ≤ 1 / (6 * n) ∧
    |(normalizedGridMap color n (sixthRealPoint n X Y)).2 -
      (sixthRealPoint n X Y).2| ≤ 1 / (6 * n)

/-- Local affine evaluation agrees with the continuous global interpolation. -/
theorem globalGridMap_sixthPoint (color : ℕ → ℕ → Fin 3) {n X Y : ℕ}
    (hn : 0 < n) (hX : X ≤ 6 * n) (hY : Y ≤ 6 * n) :
    globalGridMap color n ((X : ℝ) / 6, (Y : ℝ) / 6) =
      ((X : ℝ) / 6 + ((sixthDisplacement color n X Y).1 : ℝ),
       (Y : ℝ) / 6 + ((sixthDisplacement color n X Y).2 : ℝ)) := by
  have hx := sixthCellIndex_bounds hn hX
  have hy := sixthCellIndex_bounds hn hY
  have hx' : (6 : ℝ) * sixthCellIndex n X + sixthOffset n X = X := by
    exact_mod_cast hx.2.2
  have hy' : (6 : ℝ) * sixthCellIndex n Y + sixthOffset n Y = Y := by
    exact_mod_cast hy.2.2
  have hxp : (X : ℝ) / 6 = sixthCellIndex n X + (sixthOffset n X : ℝ) / 6 := by
    linarith
  have hyp : (Y : ℝ) / 6 = sixthCellIndex n Y + (sixthOffset n Y : ℝ) / 6 := by
    linarith
  have hxa : (sixthOffset n X : ℝ) / 6 ≤ 1 := by
    have hb : (sixthOffset n X : ℝ) ≤ 6 := by exact_mod_cast hx.2.1
    linarith
  have hya : (sixthOffset n Y : ℝ) / 6 ≤ 1 := by
    have hb : (sixthOffset n Y : ℝ) ≤ 6 := by exact_mod_cast hy.2.1
    linarith
  have hx0 : (0 : ℝ) ≤ (sixthOffset n X : ℝ) / 6 := by positivity
  have hy0 : (0 : ℝ) ≤ (sixthOffset n Y : ℝ) / 6 := by positivity
  rw [hxp, hyp]
  by_cases h : sixthOffset n X < sixthOffset n Y
  · have hab : (sixthOffset n X : ℝ) / 6 ≤ (sixthOffset n Y : ℝ) / 6 := by
      have hh : (sixthOffset n X : ℝ) < sixthOffset n Y := by exact_mod_cast h
      linarith
    rw [globalGridMap_upper _ hx.1 hy.1 hx0 hab hya]
    apply Prod.ext <;>
      simp [sixthDisplacement, sixthTriangle, sixthWeights, corner, weightedDisplacement, h]
      <;> ring
  · have hba : (sixthOffset n Y : ℝ) / 6 ≤ (sixthOffset n X : ℝ) / 6 := by
      have hh : (sixthOffset n Y : ℝ) ≤ sixthOffset n X := by
        exact_mod_cast (show sixthOffset n Y ≤ sixthOffset n X by omega)
      linarith
    rw [globalGridMap_lower _ hx.1 hy.1 hy0 hba hxa]
    apply Prod.ext <;>
      simp [sixthDisplacement, sixthTriangle, sixthWeights, corner, weightedDisplacement, h]
      <;> ring

/-- Normalization divides the exact rational displacement by the square width. -/
theorem normalizedGridMap_sixthPoint (color : ℕ → ℕ → Fin 3) {n X Y : ℕ}
    (hn : 0 < n) (hX : X ≤ 6 * n) (hY : Y ≤ 6 * n) :
    normalizedGridMap color n (sixthRealPoint n X Y) =
      ((sixthRealPoint n X Y).1 + ((sixthDisplacement color n X Y).1 : ℝ) / n,
       (sixthRealPoint n X Y).2 + ((sixthDisplacement color n X Y).2 : ℝ) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hscale (Z : ℕ) : (n : ℝ) * ((Z : ℝ) / (6 * n)) = (Z : ℝ) / 6 := by
    field_simp
  dsimp only [normalizedGridMap, sixthRealPoint]
  rw [hscale X, hscale Y, globalGridMap_sixthPoint _ hn hX hY]
  apply Prod.ext <;> dsimp <;> field_simp

private theorem scaled_absolute_residual_iff (d : ℚ) {n : ℕ} (hn : 0 < n) :
    |(d : ℝ) / n| ≤ 1 / (6 * n) ↔ |d| ≤ (1 / 6 : ℚ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_div, abs_of_pos hn', ← div_div, div_le_div_iff_of_pos_right hn']
  have hcast : ((1 / 6 : ℚ) : ℝ) = 1 / 6 := by norm_num
  rw [← Rat.cast_abs, ← hcast, Rat.cast_le]

/-- The finite rational residual test is exactly the real fixed-point inequality. -/
theorem sixthPointSmallResidual_iff_local (color : ℕ → ℕ → Fin 3) {n X Y : ℕ}
    (hn : 0 < n) (hX : X ≤ 6 * n) (hY : Y ≤ 6 * n) :
    SixthPointSmallResidual color n X Y ↔
      |(sixthDisplacement color n X Y).1| ≤ (1 / 6 : ℚ) ∧
        |(sixthDisplacement color n X Y).2| ≤ (1 / 6 : ℚ) := by
  unfold SixthPointSmallResidual
  rw [normalizedGridMap_sixthPoint _ hn hX hY]
  simp only [add_sub_cancel_left]
  exact and_congr (scaled_absolute_residual_iff _ hn) (scaled_absolute_residual_iff _ hn)

/-- The finite displacement at a canonical barycenter is the canonical barycenter displacement. -/
theorem sixthDisplacement_barycenter (color : ℕ → ℕ → Fin 3) {n : ℕ}
    {t : GridTriangle} (ht : ValidTriangle n t) :
    sixthDisplacement color n (sixthBarycenterNumerators t).1
      (sixthBarycenterNumerators t).2 = triangleBarycenterDisplacement color t := by
  unfold sixthDisplacement
  rw [sixthTriangle_barycenter ht]
  simp only [sixthWeights_barycenter ht]
  rfl

/-- Bounded numerators denote a point in the normalized square. -/
theorem sixthRealPoint_mem_unitSquare {n X Y : ℕ} (hn : 0 < n)
    (hX : X ≤ 6 * n) (hY : Y ≤ 6 * n) :
    InRealGridSquare 1 (sixthRealPoint n X Y) := by
  have hn' : (0 : ℝ) < 6 * n := by positivity
  have hX' : (X : ℝ) ≤ 6 * n := by exact_mod_cast hX
  have hY' : (Y : ℝ) ≤ 6 * n := by exact_mod_cast hY
  dsimp only [InRealGridSquare, sixthRealPoint]
  rw [Nat.cast_one]
  exact ⟨⟨by positivity, (div_le_one hn').mpr hX'⟩,
    ⟨by positivity, (div_le_one hn').mpr hY'⟩⟩

/-- Trichromatic barycenters are actual fixed points of the continuous normalized map. -/
theorem normalizedGridMap_sixthBarycenter_fixed (color : ℕ → ℕ → Fin 3)
    {n : ℕ} {t : GridTriangle} (ht : ValidTriangle n t)
    (htri : Trichromatic (color (corner t 0).1 (corner t 0).2)
      (color (corner t 1).1 (corner t 1).2)
      (color (corner t 2).1 (corner t 2).2)) :
    normalizedGridMap color n
        (sixthRealPoint n (sixthBarycenterNumerators t).1 (sixthBarycenterNumerators t).2) =
      sixthRealPoint n (sixthBarycenterNumerators t).1 (sixthBarycenterNumerators t).2 := by
  have hn : 0 < n := by have hx := ht.1; omega
  have hbounds := sixthBarycenterNumerators_bounds ht
  rw [normalizedGridMap_sixthPoint _ hn hbounds.1 hbounds.2,
    sixthDisplacement_barycenter _ ht,
    (triangleBarycenterDisplacement_eq_zero_iff color t).mpr htri]
  simp

end GameTheory.Math.Brouwer
