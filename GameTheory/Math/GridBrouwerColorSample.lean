import GameTheory.Math.GridBrouwerColorSignal
import GameTheory.Math.BinaryExtraction

/-!
# Canonical displacement bounds for binary-selected color samples

Dyadic cell decomposition bounds displacement coordinates by one throughout the unit square,
including endpoints. Clear sample evaluations remain close to the canonical color displacement
when their extracted remainders and Boolean flags have controlled numerical error.
-/

namespace GameTheory.Math.Brouwer
open scoped BigOperators

/-- The dyadic-grid displacement of a rational unit-square point has unit coordinates. -/
theorem globalGridMap_dyadic_displacement_abs_le_one (color : ℕ → ℕ → Fin 3)
    (b : ℕ) (x y : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |(globalGridMap color (2 ^ b) ((2 ^ b : ℕ) * (x : ℝ),
      (2 ^ b : ℕ) * (y : ℝ))).1 - (2 ^ b : ℕ) * (x : ℝ)| ≤ 1 ∧
    |(globalGridMap color (2 ^ b) ((2 ^ b : ℕ) * (x : ℝ),
      (2 ^ b : ℕ) * (y : ℝ))).2 - (2 ^ b : ℕ) * (y : ℝ)| ≤ 1 := by
  have hex : ((2 ^ b : ℕ) : ℝ) * (x : ℝ) =
      (binaryPrefix b x : ℝ) + (binaryRemainder b x : ℝ) := by
    exact_mod_cast binary_decomposition b x
  have hey : ((2 ^ b : ℕ) : ℝ) * (y : ℝ) =
      (binaryPrefix b y : ℝ) + (binaryRemainder b y : ℝ) := by
    exact_mod_cast binary_decomposition b y
  have hxb := binaryRemainder_bounds hx0 hx1 b
  have hyb := binaryRemainder_bounds hy0 hy1 b
  have hu0 : (0 : ℝ) ≤ binaryRemainder b x := by exact_mod_cast hxb.1
  have hu1 : (binaryRemainder b x : ℝ) ≤ 1 := by exact_mod_cast hxb.2
  have hv0 : (0 : ℝ) ≤ binaryRemainder b y := by exact_mod_cast hyb.1
  have hv1 : (binaryRemainder b y : ℝ) ≤ 1 := by exact_mod_cast hyb.2
  rw [hex, hey]
  rw [globalGridMap_fourCorners_fst_sub color (binaryPrefix_lt b x) (binaryPrefix_lt b y)
    hu0 hu1 hv0 hv1, globalGridMap_fourCorners_snd_sub color
    (binaryPrefix_lt b x) (binaryPrefix_lt b y) hu0 hu1 hv0 hv1]
  have he := weightedColorDisplacement_abs_le_one
    (fourCornerWeights (binaryRemainder b x : ℝ) (binaryRemainder b y : ℝ))
    ![color (binaryPrefix b x) (binaryPrefix b y),
      color (binaryPrefix b x + 1) (binaryPrefix b y + 1),
      color (binaryPrefix b x + 1) (binaryPrefix b y),
      color (binaryPrefix b x) (binaryPrefix b y + 1)]
    (fourCornerWeights_nonneg hu0 hu1 hv0 hv1) (fourCornerWeights_sum _ _)
  simpa [Fin.sum_univ_succ] using he

/-- Clear extraction and correctly evaluated flags control the ideal clipped sample signal. -/
theorem clipped_color_signal_error {u v u' v' N δ : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hN : 1 ≤ N) (hδ : 0 ≤ δ)
    (hu : |u' - u| ≤ 46 * N * δ) (hv : |v' - v| ≤ 46 * N * δ)
    (colors : Fin 4 → Fin 3) (z1 z2 : Fin 4 → ℝ)
    (hz1 : ∀ i, |z1 i - (if colors i = 1 then 1 else 0)| ≤ 2 * δ)
    (hz2 : ∀ i, |z2 i - (if colors i = 2 then 1 else 0)| ≤ 2 * δ) :
    |(fourCornerColorSignal (fourCornerWeights u' v') z1 z2).1 -
      (∑ i, fourCornerWeights u v i * ((colorDisplacement (colors i)).1 : ℝ))| ≤
        2000 * N * δ ∧
    |(fourCornerColorSignal (fourCornerWeights u' v') z1 z2).2 -
      (∑ i, fourCornerWeights u v i * ((colorDisplacement (colors i)).2 : ℝ))| ≤
        2000 * N * δ := by
  have hw0 := fourCornerWeights_nonneg hu0 hu1 hv0 hv1
  have hsum := fourCornerWeights_sum u v
  have hw1 (i : Fin 4) : fourCornerWeights u v i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hw0 j) (Finset.mem_univ i)
  have hw (i : Fin 4) : |fourCornerWeights u' v' i - fourCornerWeights u v i| ≤
      92 * N * δ := by
    have h := fourCornerWeights_perturbation hu hv i
    linarith only [h]
  have he := fourCornerColorSignal_error_approx (fourCornerWeights u v)
    (fourCornerWeights u' v') z1 z2 colors (2 * δ) (92 * N * δ) hw0 hw1 hsum hw hz1 hz2
  have hδN : δ ≤ N * δ := by nlinarith only [hN, hδ]
  constructor <;> nlinarith only [he.1, he.2, hδN, hδ]

end GameTheory.Math.Brouwer
