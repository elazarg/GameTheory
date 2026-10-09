import GameTheory.Math.GridBrouwerContinuous
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Lipschitz bounds for triangular grid displacement

Each vertex hat has Lipschitz constant two. Summing hats with coefficients of absolute value
at most one bounds each displacement coordinate by twice the number of grid vertices.
These coarse bounds also control displacement evaluated at scaled coordinates, without requiring
any regularity of the vertex coloring.
-/

namespace GameTheory.Math.Brouwer
open Sperner
open scoped BigOperators

theorem lipschitzWith_vertexHat (i j : ℕ) : LipschitzWith 2 (vertexHat i j) := by
  have hx : LipschitzWith 1 (fun p : ℝ × ℝ => p.1 - (i : ℝ)) := by
    simpa using (LipschitzWith.prod_fst (α := ℝ) (β := ℝ)).sub (LipschitzWith.const (i : ℝ))
  have hy : LipschitzWith 1 (fun p : ℝ × ℝ => p.2 - (j : ℝ)) := by
    simpa using (LipschitzWith.prod_snd (α := ℝ) (β := ℝ)).sub (LipschitzWith.const (j : ℝ))
  have hax : LipschitzWith 1 (fun p : ℝ × ℝ => |p.1 - (i : ℝ)|) := by
    simpa [Function.comp_def, Real.norm_eq_abs] using (lipschitzWith_one_norm (E := ℝ)).comp hx
  have hay : LipschitzWith 1 (fun p : ℝ × ℝ => |p.2 - (j : ℝ)|) := by
    simpa [Function.comp_def, Real.norm_eq_abs] using (lipschitzWith_one_norm (E := ℝ)).comp hy
  have htwo : (1 : NNReal) + 1 = 2 := by norm_num
  have had : LipschitzWith 2
      (fun p : ℝ × ℝ => |(p.1 - (i : ℝ)) - (p.2 - (j : ℝ))|) := by
    simpa [Function.comp_def, Real.norm_eq_abs, htwo] using
      (lipschitzWith_one_norm (E := ℝ)).comp (hx.sub hy)
  have hm : LipschitzWith 2 (fun p : ℝ × ℝ =>
      max |p.1 - (i : ℝ)| (max |p.2 - (j : ℝ)| |(p.1 - (i : ℝ)) - (p.2 - (j : ℝ))|)) := by
    simpa using hax.max (hay.max had)
  unfold vertexHat
  simpa only [zero_add] using ((LipschitzWith.const (α := ℝ × ℝ) (1 : ℝ)).sub hm).const_max 0

theorem vertexHat_weighted_sum_lipschitz (s : Finset (ℕ × ℕ)) (a : ℕ → ℕ → ℝ)
    (ha : ∀ v ∈ s, |a v.1 v.2| ≤ 1) :
    LipschitzWith (2 * s.card) (fun p : ℝ × ℝ =>
      ∑ v ∈ s, vertexHat v.1 v.2 p * a v.1 v.2) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro p q
  rw [Real.dist_eq, ← Finset.sum_sub_distrib]
  calc
    |∑ v ∈ s, (vertexHat v.1 v.2 p * a v.1 v.2 - vertexHat v.1 v.2 q * a v.1 v.2)|
        ≤ ∑ v ∈ s, |vertexHat v.1 v.2 p * a v.1 v.2 - vertexHat v.1 v.2 q * a v.1 v.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ s, 2 * dist p q := by
      apply Finset.sum_le_sum
      intro v hv
      rw [← sub_mul, abs_mul]
      calc
        |vertexHat v.1 v.2 p - vertexHat v.1 v.2 q| * |a v.1 v.2|
            ≤ |vertexHat v.1 v.2 p - vertexHat v.1 v.2 q| :=
          mul_le_of_le_one_right (abs_nonneg _) (ha v hv)
        _ ≤ 2 * dist p q := by
          simpa only [Real.dist_eq, NNReal.coe_ofNat] using
            (lipschitzWith_vertexHat v.1 v.2).dist_le_mul p q
    _ = (↑(2 * (s.card : NNReal)) : ℝ) * dist p q := by simp; ring

theorem globalGridMap_fst_displacement_lipschitz (color : ℕ → ℕ → Fin 3) (n : ℕ) :
    LipschitzWith (2 * (n + 1) ^ 2) (fun p : ℝ × ℝ => (globalGridMap color n p).1 - p.1) := by
  have h := vertexHat_weighted_sum_lipschitz
    ((Finset.range (n + 1)).product (Finset.range (n + 1)))
    (fun i j => ((colorDisplacement (color i j)).1 : ℝ)) (by
      intro v _
      generalize color v.1 v.2 = c
      fin_cases c <;> norm_num [colorDisplacement])
  simpa [globalGridMap, Finset.sum_product, pow_two] using h

theorem globalGridMap_snd_displacement_lipschitz (color : ℕ → ℕ → Fin 3) (n : ℕ) :
    LipschitzWith (2 * (n + 1) ^ 2) (fun p : ℝ × ℝ => (globalGridMap color n p).2 - p.2) := by
  have h := vertexHat_weighted_sum_lipschitz
    ((Finset.range (n + 1)).product (Finset.range (n + 1)))
    (fun i j => ((colorDisplacement (color i j)).2 : ℝ)) (by
      intro v _
      generalize color v.1 v.2 = c
      fin_cases c <;> norm_num [colorDisplacement])
  simpa [globalGridMap, Finset.sum_product, pow_two] using h

theorem lipschitzWith_grid_scale (n : ℕ) :
    LipschitzWith n (fun p : ℝ × ℝ => ((n : ℝ) * p.1, (n : ℝ) * p.2)) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro p q
  simp only [Prod.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, Nat.abs_cast,
    NNReal.coe_natCast]
  rw [mul_max_of_nonneg _ _ (Nat.cast_nonneg n)]

theorem globalGridMap_scaled_fst_displacement_lipschitz
    (color : ℕ → ℕ → Fin 3) (n : ℕ) :
    LipschitzWith (2 * n * (n + 1) ^ 2) (fun p : ℝ × ℝ =>
      (globalGridMap color n ((n : ℝ) * p.1, (n : ℝ) * p.2)).1 - (n : ℝ) * p.1) := by
  have h := (globalGridMap_fst_displacement_lipschitz color n).comp (lipschitzWith_grid_scale n)
  simpa only [Function.comp_def, mul_right_comm] using h

theorem globalGridMap_scaled_snd_displacement_lipschitz
    (color : ℕ → ℕ → Fin 3) (n : ℕ) :
    LipschitzWith (2 * n * (n + 1) ^ 2) (fun p : ℝ × ℝ =>
      (globalGridMap color n ((n : ℝ) * p.1, (n : ℝ) * p.2)).2 - (n : ℝ) * p.2) := by
  have h := (globalGridMap_snd_displacement_lipschitz color n).comp (lipschitzWith_grid_scale n)
  simpa only [Function.comp_def, mul_right_comm] using h

/-- The horizontal scaled displacement has quantitative inward bounds on the unit square. -/
theorem globalGridMap_scaled_fst_displacement_inward
    {color : ℕ → ℕ → Fin 3} {n : ℕ} (hb : GridBoundary color n) (hn : 0 < n)
    {p : ℝ × ℝ} (hp : InRealGridSquare 1 p) :
    -(2 * (n : ℝ) * (n + 1) ^ 2) * p.1 ≤
      (globalGridMap color n ((n : ℝ) * p.1, (n : ℝ) * p.2)).1 - (n : ℝ) * p.1 ∧
    (globalGridMap color n ((n : ℝ) * p.1, (n : ℝ) * p.2)).1 - (n : ℝ) * p.1 ≤
      (2 * (n : ℝ) * (n + 1) ^ 2) * (1 - p.1) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hy : 0 ≤ (n : ℝ) * p.2 ∧ (n : ℝ) * p.2 ≤ n := by
    constructor
    · exact mul_nonneg hn0 hp.2.1
    · simpa using mul_le_mul_of_nonneg_left hp.2.2 hn0
  have hleft := globalGridMap_mem_square hb hn (p := (0, (n : ℝ) * p.2))
    (show InRealGridSquare n (0, (n : ℝ) * p.2) from ⟨⟨le_rfl, hn0⟩, hy⟩)
  have hright := globalGridMap_mem_square hb hn (p := (n, (n : ℝ) * p.2))
    (show InRealGridSquare n (n, (n : ℝ) * p.2) from ⟨⟨hn0, le_rfl⟩, hy⟩)
  have h0 := (globalGridMap_scaled_fst_displacement_lipschitz color n).dist_le_mul p (0, p.2)
  have h1 := (globalGridMap_scaled_fst_displacement_lipschitz color n).dist_le_mul p (1, p.2)
  simp only [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero,
    sub_zero, abs_of_nonneg hp.1.1, max_eq_left hp.1.1, mul_zero,
    NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_add, NNReal.coe_one] at h0
  simp only [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero,
    max_eq_left (abs_nonneg (p.1 - 1)),
    mul_one, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_add, NNReal.coe_one] at h1
  have hx1 : p.1 ≤ (1 : ℝ) := by simpa only [Nat.cast_one] using hp.1.2
  simp only [abs_of_nonpos (sub_nonpos.mpr hx1)] at h1
  rw [abs_le] at h0 h1
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, hleft.1.1, hright.1.2]

/-- The vertical scaled displacement has quantitative inward bounds on the unit square. -/
theorem globalGridMap_scaled_snd_displacement_inward
    {color : ℕ → ℕ → Fin 3} {n : ℕ} (hb : GridBoundary color n) (hn : 0 < n)
    {p : ℝ × ℝ} (hp : InRealGridSquare 1 p) :
    -(2 * (n : ℝ) * (n + 1) ^ 2) * p.2 ≤
      (globalGridMap color n ((n : ℝ) * p.1, (n : ℝ) * p.2)).2 - (n : ℝ) * p.2 ∧
    (globalGridMap color n ((n : ℝ) * p.1, (n : ℝ) * p.2)).2 - (n : ℝ) * p.2 ≤
      (2 * (n : ℝ) * (n + 1) ^ 2) * (1 - p.2) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hx : 0 ≤ (n : ℝ) * p.1 ∧ (n : ℝ) * p.1 ≤ n := by
    constructor
    · exact mul_nonneg hn0 hp.1.1
    · simpa using mul_le_mul_of_nonneg_left hp.1.2 hn0
  have hlower := globalGridMap_mem_square hb hn (p := ((n : ℝ) * p.1, 0))
    (show InRealGridSquare n ((n : ℝ) * p.1, 0) from ⟨hx, ⟨le_rfl, hn0⟩⟩)
  have hupper := globalGridMap_mem_square hb hn (p := ((n : ℝ) * p.1, n))
    (show InRealGridSquare n ((n : ℝ) * p.1, n) from ⟨hx, ⟨hn0, le_rfl⟩⟩)
  have h0 := (globalGridMap_scaled_snd_displacement_lipschitz color n).dist_le_mul p (p.1, 0)
  have h1 := (globalGridMap_scaled_snd_displacement_lipschitz color n).dist_le_mul p (p.1, 1)
  simp only [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero,
    sub_zero, abs_of_nonneg hp.2.1, max_eq_right hp.2.1, mul_zero,
    NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_add, NNReal.coe_one] at h0
  simp only [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero,
    max_eq_right (abs_nonneg (p.2 - 1)),
    mul_one, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_add, NNReal.coe_one] at h1
  have hy1 : p.2 ≤ (1 : ℝ) := by simpa only [Nat.cast_one] using hp.2.2
  simp only [abs_of_nonpos (sub_nonpos.mpr hy1)] at h1
  rw [abs_le] at h0 h1
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, hlower.2.1, hupper.2.2]

end GameTheory.Math.Brouwer
