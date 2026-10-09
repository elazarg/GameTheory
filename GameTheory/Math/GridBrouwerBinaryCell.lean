import GameTheory.Math.BinaryExtraction
import GameTheory.Math.GridBrouwerContinuous
import Mathlib.Data.Rat.Cast.Order

/-! Exact binary cell extraction turns a small interpolated residual into a
trichromatic triangle, including unit-square edges and the rising diagonal. -/
namespace GameTheory.Math.Brouwer
open Sperner

/-- The dyadic cell containing a unit point, with its rising-diagonal half. -/
def binaryGridTriangle (b : ℕ) (x y : ℚ) : GridTriangle :=
  ⟨binaryPrefix b x, binaryPrefix b y,
    decide (binaryRemainder b x < binaryRemainder b y)⟩

/-- The endpoint convention always selects a genuine cell of the dyadic grid. -/
theorem binaryGridTriangle_valid (b : ℕ) (x y : ℚ) :
    ValidTriangle (2 ^ b) (binaryGridTriangle b x y) :=
  ⟨binaryPrefix_lt b x, binaryPrefix_lt b y⟩

private theorem lower_small (color : ℕ → ℕ → Fin 3) {n i j : ℕ}
    (hi : i < n) (hj : j < n) (u v : ℚ) (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u ≤ 1)
    (hx : |(globalGridMap color n ((i : ℝ) + u, (j : ℝ) + v)).1 -
      ((i : ℝ) + u)| ≤ 1 / 6)
    (hy : |(globalGridMap color n ((i : ℝ) + u, (j : ℝ) + v)).2 -
      ((j : ℝ) + v)| ≤ 1 / 6) :
    Trichromatic (color i j) (color (i + 1) j) (color (i + 1) (j + 1)) := by
  have hvr : (0 : ℝ) ≤ v := by exact_mod_cast hv
  have hvur : (v : ℝ) ≤ u := by exact_mod_cast hvu
  have hur : (u : ℝ) ≤ 1 := by exact_mod_cast hu
  rw [globalGridMap_lower color hi hj hvr hvur hur] at hx hy
  simp only [add_sub_cancel_left] at hx hy
  apply weightedDisplacement_small_implies_trichromatic _ _ _ (1 - u) (u - v) v
    (by ring)
  · unfold weightedDisplacement
    dsimp only
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hx
  · unfold weightedDisplacement
    dsimp only
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hy

private theorem upper_small (color : ℕ → ℕ → Fin 3) {n i j : ℕ}
    (hi : i < n) (hj : j < n) (u v : ℚ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1)
    (hx : |(globalGridMap color n ((i : ℝ) + u, (j : ℝ) + v)).1 -
      ((i : ℝ) + u)| ≤ 1 / 6)
    (hy : |(globalGridMap color n ((i : ℝ) + u, (j : ℝ) + v)).2 -
      ((j : ℝ) + v)| ≤ 1 / 6) :
    Trichromatic (color i j) (color (i + 1) (j + 1)) (color i (j + 1)) := by
  have hur : (0 : ℝ) ≤ u := by exact_mod_cast hu
  have huvR : (u : ℝ) ≤ v := by exact_mod_cast huv
  have hvr : (v : ℝ) ≤ 1 := by exact_mod_cast hv
  rw [globalGridMap_upper color hi hj hur huvR hvr] at hx hy
  simp only [add_sub_cancel_left] at hx hy
  apply weightedDisplacement_small_implies_trichromatic _ _ _ (1 - v) u (v - u)
    (by ring)
  · unfold weightedDisplacement
    dsimp only
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hx
  · unfold weightedDisplacement
    dsimp only
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hy

/-- Every small residual identifies the exact triangle selected by binary extraction. -/
theorem binaryGridTriangle_trichromatic (color : ℕ → ℕ → Fin 3) (b : ℕ) (x y : ℚ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hx : |(globalGridMap color (2 ^ b) ((2 ^ b : ℕ) * (x : ℝ),
      (2 ^ b : ℕ) * (y : ℝ))).1 - (2 ^ b : ℕ) * (x : ℝ)| ≤ 1 / 6)
    (hy : |(globalGridMap color (2 ^ b) ((2 ^ b : ℕ) * (x : ℝ),
      (2 ^ b : ℕ) * (y : ℝ))).2 - (2 ^ b : ℕ) * (y : ℝ)| ≤ 1 / 6) :
    let t := binaryGridTriangle b x y
    Trichromatic (color (corner t 0).1 (corner t 0).2)
      (color (corner t 1).1 (corner t 1).2) (color (corner t 2).1 (corner t 2).2) := by
  have hex : ((2 ^ b : ℕ) : ℝ) * (x : ℝ) =
      (binaryPrefix b x : ℝ) + (binaryRemainder b x : ℝ) := by
    exact_mod_cast binary_decomposition b x
  have hey : ((2 ^ b : ℕ) : ℝ) * (y : ℝ) =
      (binaryPrefix b y : ℝ) + (binaryRemainder b y : ℝ) := by
    exact_mod_cast binary_decomposition b y
  rw [hex, hey] at hx hy
  have hxb := binaryRemainder_bounds hx0 hx1 b
  have hyb := binaryRemainder_bounds hy0 hy1 b
  by_cases h : binaryRemainder b x < binaryRemainder b y
  · simpa [binaryGridTriangle, h, corner] using upper_small color
      (binaryPrefix_lt b x) (binaryPrefix_lt b y) (binaryRemainder b x)
      (binaryRemainder b y) hxb.1 h.le hyb.2 hx hy
  · simpa [binaryGridTriangle, h, corner] using lower_small color
      (binaryPrefix_lt b x) (binaryPrefix_lt b y) (binaryRemainder b x)
      (binaryRemainder b y) hyb.1 (le_of_not_gt h) hxb.2 hx hy

end GameTheory.Math.Brouwer
