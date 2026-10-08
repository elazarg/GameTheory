import GameTheory.Math.GridBrouwerSixthPoints

/-! The sixth-grid locator reconstructs the input point by affine weights.
Triangle barycenters have canonical integer numerators in this representation. -/

namespace GameTheory.Math.Brouwer

open Sperner

/-- Affine reconstruction from the located cell recovers the rational point. -/
theorem trianglePoint_sixthWeights {n X Y : ℕ} (hn : 0 < n)
    (hX : X ≤ 6 * n) (hY : Y ≤ 6 * n) :
    trianglePoint (sixthTriangle n X Y) (sixthWeights n X Y 0)
      (sixthWeights n X Y 1) (sixthWeights n X Y 2) =
      ((X : ℚ) / 6, (Y : ℚ) / 6) := by
  have hx := (sixthCellIndex_bounds hn hX).2.2
  have hy := (sixthCellIndex_bounds hn hY).2.2
  have hx' : (6 : ℚ) * sixthCellIndex n X + sixthOffset n X = X := by exact_mod_cast hx
  have hy' : (6 : ℚ) * sixthCellIndex n Y + sixthOffset n Y = Y := by exact_mod_cast hy
  unfold sixthWeights sixthTriangle trianglePoint corner
  by_cases h : sixthOffset n X < sixthOffset n Y <;>
    simp [h, Nat.cast_add, Nat.cast_one] <;>
    constructor <;> linarith

/-- Integer coordinate numerators of a triangle barycenter on the sixth grid. -/
def sixthBarycenterNumerators (t : GridTriangle) : ℕ × ℕ :=
  (6 * t.x + if t.upper then 2 else 4,
    6 * t.y + if t.upper then 4 else 2)

/-- Barycenter numerators remain inside the closed square. -/
theorem sixthBarycenterNumerators_bounds {n : ℕ} {t : GridTriangle}
    (ht : ValidTriangle n t) :
    (sixthBarycenterNumerators t).1 ≤ 6 * n ∧
      (sixthBarycenterNumerators t).2 ≤ 6 * n := by
  rcases t with ⟨x, y, upper⟩
  cases upper <;> simp only [sixthBarycenterNumerators, Bool.false_eq_true,
    ↓reduceIte] <;>
    simp only [ValidTriangle] at ht <;> omega

/-- A local coordinate below six belongs to its indicated cell. -/
theorem sixthCellIndex_interior {n k r : ℕ} (hk : k < n) (hr : r < 6) :
    sixthCellIndex n (6 * k + r) = k := by
  have hd : (6 * k + r) / 6 = k := by omega
  simp only [sixthCellIndex, hd]
  exact Nat.min_eq_left (by omega)

/-- The locator preserves an interior local numerator. -/
theorem sixthOffset_interior {n k r : ℕ} (hk : k < n) (hr : r < 6) :
    sixthOffset n (6 * k + r) = r := by
  rw [sixthOffset, sixthCellIndex_interior hk hr]
  omega

/-- Locating a canonical barycenter recovers its original triangle. -/
theorem sixthTriangle_barycenter {n : ℕ} {t : GridTriangle}
    (ht : ValidTriangle n t) :
    sixthTriangle n (sixthBarycenterNumerators t).1
      (sixthBarycenterNumerators t).2 = t := by
  rcases t with ⟨x, y, upper⟩
  rcases ht with ⟨hx, hy⟩
  change x < n at hx
  change y < n at hy
  cases upper with
  | false =>
    simp [sixthBarycenterNumerators, sixthTriangle,
      sixthCellIndex_interior hx (r := 4) (by decide),
      sixthCellIndex_interior hy (r := 2) (by decide),
      sixthOffset_interior hx (r := 4) (by decide),
      sixthOffset_interior hy (r := 2) (by decide)]
  | true =>
    simp [sixthBarycenterNumerators, sixthTriangle,
      sixthCellIndex_interior hx (r := 2) (by decide),
      sixthCellIndex_interior hy (r := 4) (by decide),
      sixthOffset_interior hx (r := 2) (by decide),
      sixthOffset_interior hy (r := 4) (by decide)]

/-- Canonical barycenters receive the same one-third weight at every corner. -/
theorem sixthWeights_barycenter {n : ℕ} {t : GridTriangle}
    (ht : ValidTriangle n t) (p : Fin 3) :
    sixthWeights n (sixthBarycenterNumerators t).1
      (sixthBarycenterNumerators t).2 p = 1 / 3 := by
  rcases t with ⟨x, y, upper⟩
  rcases ht with ⟨hx, hy⟩
  change x < n at hx
  change y < n at hy
  cases upper with
  | false =>
    fin_cases p <;> norm_num [sixthBarycenterNumerators, sixthWeights,
      sixthOffset_interior hx (r := 4) (by decide),
      sixthOffset_interior hy (r := 2) (by decide)]
  | true =>
    fin_cases p <;> norm_num [sixthBarycenterNumerators, sixthWeights,
      sixthOffset_interior hx (r := 2) (by decide),
      sixthOffset_interior hy (r := 4) (by decide)]

/-- The numerator representation denotes the ordinary affine barycenter. -/
theorem trianglePoint_barycenter_numerators (t : GridTriangle) :
    trianglePoint t (1 / 3) (1 / 3) (1 / 3) =
      (((sixthBarycenterNumerators t).1 : ℚ) / 6,
        ((sixthBarycenterNumerators t).2 : ℚ) / 6) := by
  rcases t with ⟨x, y, upper⟩
  cases upper <;> apply Prod.ext <;>
    simp [trianglePoint, corner, sixthBarycenterNumerators] <;> ring

end GameTheory.Math.Brouwer
