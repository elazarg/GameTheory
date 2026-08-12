/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses

/-!
# The exact two-parameter cyclic Q region

For positive `a,b`, this file classifies the cyclic zero-diagonal matrix

`[[0,-a,b],[b,0,-a],[-a,b,0]]`.

It is textbook standard Q exactly when `a < b`, and its homogeneous simplex
problem is infeasible exactly when `a ≠ b`.  Thus the nonhomogeneous
standard-Q region in this family is exactly the open cone `0 < a < b`.

The Q proof is constructive.  After positive rescaling it uses the empty
support, three cyclic two-coordinate supports, and the full support.  No
matrix-classification theorem or numerical search enters the proof.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification
namespace CyclicParametricQ

open Finset Math.LinearProgramming

abbrev Player := Fin 3

/-- The ratio-normalized cyclic matrix. -/
def normalizedCyclicMatrix (t : ℝ) : Player → Player → ℝ :=
  fun who owner =>
    if who = 0 then
      if owner = 0 then 0 else if owner = 1 then -1 else t
    else if who = 1 then
      if owner = 0 then t else if owner = 1 then 0 else -1
    else
      if owner = 0 then -1 else if owner = 1 then t else 0

/-- The original two-parameter cyclic matrix. -/
def cyclicMatrix (a b : ℝ) : Player → Player → ℝ :=
  fun who owner => a * normalizedCyclicMatrix (b / a) who owner

private def emptySolution (t : ℝ) (q : Player → ℝ)
    (hq : ∀ i, 0 ≤ q i) : StandardLCPSolution (normalizedCyclicMatrix t) q where
  weight := 0
  weight_nonneg := by intro i; simp
  residual_nonneg := by intro i; simpa using hq i
  complementary := by intro i; simp

private def pairZeroOneSolution (t : ℝ) (q : Player → ℝ)
    (ht : 0 < t) (h0 : 0 ≤ q 0) (h1 : q 1 ≤ 0)
    (hout : 0 ≤ t * q 2 + q 1 + t ^ 2 * q 0) :
    StandardLCPSolution (normalizedCyclicMatrix t) q where
  weight := ![-q 1 / t, q 0, 0]
  weight_nonneg := by
    intro i
    fin_cases i
    · change 0 ≤ -q 1 / t
      exact div_nonneg (neg_nonneg.mpr h1) ht.le
    · change 0 ≤ q 0
      exact h0
    · change 0 ≤ (0 : ℝ)
      exact le_rfl
  residual_nonneg := by
    intro i
    fin_cases i <;>
      simp [normalizedCyclicMatrix, Fin.sum_univ_succ] <;>
      field_simp [ne_of_gt ht] <;>
      nlinarith [hout, sq_nonneg t]
  complementary := by
    intro i
    fin_cases i
    all_goals simp [normalizedCyclicMatrix, Fin.sum_univ_succ]
    all_goals field_simp [ne_of_gt ht]
    all_goals simp

private def pairOneTwoSolution (t : ℝ) (q : Player → ℝ)
    (ht : 0 < t) (h1 : 0 ≤ q 1) (h2 : q 2 ≤ 0)
    (hout : 0 ≤ t * q 0 + q 2 + t ^ 2 * q 1) :
    StandardLCPSolution (normalizedCyclicMatrix t) q where
  weight := ![0, -q 2 / t, q 1]
  weight_nonneg := by
    intro i
    fin_cases i
    · change 0 ≤ (0 : ℝ)
      exact le_rfl
    · change 0 ≤ -q 2 / t
      exact div_nonneg (neg_nonneg.mpr h2) ht.le
    · change 0 ≤ q 1
      exact h1
  residual_nonneg := by
    intro i
    fin_cases i <;>
      simp [normalizedCyclicMatrix, Fin.sum_univ_succ] <;>
      field_simp [ne_of_gt ht] <;>
      nlinarith [hout, sq_nonneg t]
  complementary := by
    intro i
    fin_cases i
    all_goals simp [normalizedCyclicMatrix, Fin.sum_univ_succ]
    all_goals field_simp [ne_of_gt ht]
    all_goals simp

private def pairTwoZeroSolution (t : ℝ) (q : Player → ℝ)
    (ht : 0 < t) (h2 : 0 ≤ q 2) (h0 : q 0 ≤ 0)
    (hout : 0 ≤ t * q 1 + q 0 + t ^ 2 * q 2) :
    StandardLCPSolution (normalizedCyclicMatrix t) q where
  weight := ![q 2, 0, -q 0 / t]
  weight_nonneg := by
    intro i
    fin_cases i
    · change 0 ≤ q 2
      exact h2
    · change 0 ≤ (0 : ℝ)
      exact le_rfl
    · change 0 ≤ -q 0 / t
      exact div_nonneg (neg_nonneg.mpr h0) ht.le
  residual_nonneg := by
    intro i
    fin_cases i <;>
      simp [normalizedCyclicMatrix, Fin.sum_univ_succ] <;>
      field_simp [ne_of_gt ht] <;>
      nlinarith [hout, sq_nonneg t]
  complementary := by
    intro i
    fin_cases i
    all_goals simp [normalizedCyclicMatrix, Fin.sum_univ_succ]
    all_goals field_simp [ne_of_gt ht]
    all_goals simp

private def fullSolution (t : ℝ) (q : Player → ℝ)
    (hden : 0 < t ^ 3 - 1)
    (h0 : t * q 0 + t ^ 2 * q 1 + q 2 ≤ 0)
    (h1 : q 0 + t * q 1 + t ^ 2 * q 2 ≤ 0)
    (h2 : t ^ 2 * q 0 + q 1 + t * q 2 ≤ 0) :
    StandardLCPSolution (normalizedCyclicMatrix t) q where
  weight := fun i =>
    if i = 0 then -(t * q 0 + t ^ 2 * q 1 + q 2) / (t ^ 3 - 1)
    else if i = 1 then -(q 0 + t * q 1 + t ^ 2 * q 2) / (t ^ 3 - 1)
    else -(t ^ 2 * q 0 + q 1 + t * q 2) / (t ^ 3 - 1)
  weight_nonneg := by
    intro i
    fin_cases i
    · change 0 ≤ -(t * q 0 + t ^ 2 * q 1 + q 2) / (t ^ 3 - 1)
      apply div_nonneg
      · nlinarith [h0]
      · exact hden.le
    · change 0 ≤ -(q 0 + t * q 1 + t ^ 2 * q 2) / (t ^ 3 - 1)
      apply div_nonneg
      · nlinarith [h1]
      · exact hden.le
    · change 0 ≤ -(t ^ 2 * q 0 + q 1 + t * q 2) / (t ^ 3 - 1)
      apply div_nonneg
      · nlinarith [h2]
      · exact hden.le
  residual_nonneg := by
    intro i
    fin_cases i <;>
      simp [normalizedCyclicMatrix, Fin.sum_univ_succ,
        show (2 : Player) ≠ 0 by decide, show (2 : Player) ≠ 1 by decide] <;>
      field_simp [ne_of_gt hden] <;> ring_nf <;> norm_num
  complementary := by
    intro i
    fin_cases i <;>
      apply mul_eq_zero_of_right <;>
      simp [normalizedCyclicMatrix, Fin.sum_univ_succ,
        show (2 : Player) ≠ 0 by decide, show (2 : Player) ≠ 1 by decide] <;>
      field_simp [ne_of_gt hden] <;> ring

private theorem cube_sub_one_pos {t : ℝ} (ht : 1 < t) :
    0 < t ^ 3 - 1 := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hquad : 0 < t ^ 2 + t + 1 := by nlinarith [sq_nonneg t]
  have hprod := mul_pos (sub_pos.mpr ht) hquad
  nlinarith [show (t - 1) * (t ^ 2 + t + 1) = t ^ 3 - 1 by ring]

private theorem fullBounds_two_nonnegative
    {t x y z : ℝ} (ht : 1 < t)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z ≤ 0)
    (hfail : t * x + z + t ^ 2 * y < 0) :
    t * x + t ^ 2 * y + z ≤ 0 ∧
      x + t * y + t ^ 2 * z ≤ 0 ∧
      t ^ 2 * x + y + t * z ≤ 0 := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have ht2 : 1 < t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
  have ht3 : 1 < t ^ 3 := by
    have := mul_lt_mul_of_pos_left ht2 ht0
    nlinarith [show t * t ^ 2 = t ^ 3 by ring]
  constructor
  · linarith
  constructor <;> nlinarith [mul_nonneg hx (sub_nonneg.mpr ht.le),
    mul_nonneg hy (sub_nonneg.mpr ht.le)]

private theorem fullBounds_one_nonnegative
    {t x y z : ℝ} (ht : 1 < t)
    (hx : 0 ≤ x) (hy : y ≤ 0) (hz : z ≤ 0)
    (hfail : t ^ 2 * x + y + t * z < 0) :
    t * x + t ^ 2 * y + z ≤ 0 ∧
      x + t * y + t ^ 2 * z ≤ 0 ∧
      t ^ 2 * x + y + t * z ≤ 0 := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have ht2 : 1 < t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
  have ht3 : 1 < t ^ 3 := by
    have := mul_lt_mul_of_pos_left ht2 ht0
    nlinarith [show t * t ^ 2 = t ^ 3 by ring]
  constructor
  · have hscaled := mul_lt_mul_of_pos_left hfail ht0
    nlinarith [mul_nonneg (neg_nonneg.mpr hy) (sub_nonneg.mpr ht.le)]
  constructor
  · have hscaled := mul_lt_mul_of_pos_left hfail ht0
    nlinarith [mul_nonneg (neg_nonneg.mpr hy) (sub_nonneg.mpr ht.le),
      mul_nonneg (neg_nonneg.mpr hz) (sub_nonneg.mpr ht.le)]
  · exact hfail.le

/-- For `1 < t`, the ratio-normalized cyclic matrix is textbook standard Q. -/
theorem normalizedCyclicMatrix_standardQ {t : ℝ} (ht : 1 < t) :
    IsStandardQMatrix (normalizedCyclicMatrix t) := by
  intro q
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hden := cube_sub_one_pos ht
  by_cases hq0 : 0 ≤ q 0
  · by_cases hq1 : 0 ≤ q 1
    · by_cases hq2 : 0 ≤ q 2
      · exact ⟨emptySolution t q (by intro i; fin_cases i <;> assumption)⟩
      · have hq2' : q 2 ≤ 0 := le_of_lt (lt_of_not_ge hq2)
        by_cases hp : 0 ≤ t * q 0 + q 2 + t ^ 2 * q 1
        · exact ⟨pairOneTwoSolution t q ht0 hq1 hq2' hp⟩
        · obtain ⟨h0, h1, h2⟩ := fullBounds_two_nonnegative
            ht hq0 hq1 hq2' (lt_of_not_ge hp)
          exact ⟨fullSolution t q hden (by nlinarith [h0])
            (by nlinarith [h1]) (by nlinarith [h2])⟩
    · have hq1' : q 1 ≤ 0 := le_of_lt (lt_of_not_ge hq1)
      by_cases hq2 : 0 ≤ q 2
      · by_cases hp : 0 ≤ t * q 2 + q 1 + t ^ 2 * q 0
        · exact ⟨pairZeroOneSolution t q ht0 hq0 hq1' hp⟩
        · obtain ⟨h2, h0, h1⟩ := fullBounds_two_nonnegative
            ht hq2 hq0 hq1' (by nlinarith [lt_of_not_ge hp])
          exact ⟨fullSolution t q hden (by nlinarith [h0])
            (by nlinarith [h1]) (by nlinarith [h2])⟩
      · have hq2' : q 2 ≤ 0 := le_of_lt (lt_of_not_ge hq2)
        by_cases hp : 0 ≤ t * q 2 + q 1 + t ^ 2 * q 0
        · exact ⟨pairZeroOneSolution t q ht0 hq0 hq1' hp⟩
        · obtain ⟨h0, h1, h2⟩ := fullBounds_one_nonnegative
            ht hq0 hq1' hq2' (by nlinarith [lt_of_not_ge hp])
          exact ⟨fullSolution t q hden (by nlinarith [h0])
            (by nlinarith [h1]) (by nlinarith [h2])⟩
  · have hq0' : q 0 ≤ 0 := le_of_lt (lt_of_not_ge hq0)
    by_cases hq1 : 0 ≤ q 1
    · by_cases hq2 : 0 ≤ q 2
      · by_cases hp : 0 ≤ t * q 1 + q 0 + t ^ 2 * q 2
        · exact ⟨pairTwoZeroSolution t q ht0 hq2 hq0' hp⟩
        · obtain ⟨h1, h2, h0⟩ := fullBounds_two_nonnegative
            ht hq1 hq2 hq0' (by nlinarith [lt_of_not_ge hp])
          exact ⟨fullSolution t q hden (by nlinarith [h0])
            (by nlinarith [h1]) (by nlinarith [h2])⟩
      · have hq2' : q 2 ≤ 0 := le_of_lt (lt_of_not_ge hq2)
        by_cases hp : 0 ≤ t * q 0 + q 2 + t ^ 2 * q 1
        · exact ⟨pairOneTwoSolution t q ht0 hq1 hq2' hp⟩
        · obtain ⟨h1, h2, h0⟩ := fullBounds_one_nonnegative
            ht hq1 hq2' hq0' (by nlinarith [lt_of_not_ge hp])
          exact ⟨fullSolution t q hden (by nlinarith [h0])
            (by nlinarith [h1]) (by nlinarith [h2])⟩
    · have hq1' : q 1 ≤ 0 := le_of_lt (lt_of_not_ge hq1)
      by_cases hq2 : 0 ≤ q 2
      · by_cases hp : 0 ≤ t * q 1 + q 0 + t ^ 2 * q 2
        · exact ⟨pairTwoZeroSolution t q ht0 hq2 hq0' hp⟩
        · obtain ⟨h2, h0, h1⟩ := fullBounds_one_nonnegative
            ht hq2 hq0' hq1' (by nlinarith [lt_of_not_ge hp])
          exact ⟨fullSolution t q hden (by nlinarith [h0])
            (by nlinarith [h1]) (by nlinarith [h2])⟩
      · have hq2' : q 2 ≤ 0 := le_of_lt (lt_of_not_ge hq2)
        exact ⟨fullSolution t q hden (by nlinarith) (by nlinarith) (by nlinarith)⟩

private theorem not_standardQ_of_ratio_le_one {t : ℝ} (_ht0 : 0 < t)
    (ht : t ≤ 1) : ¬IsStandardQMatrix (normalizedCyclicMatrix t) := by
  intro hQ
  obtain ⟨solution⟩ := hQ (fun _ => -1)
  have h0 := solution.residual_nonneg 0
  have h1 := solution.residual_nonneg 1
  have h2 := solution.residual_nonneg 2
  have hz0 := solution.weight_nonneg 0
  have hz1 := solution.weight_nonneg 1
  have hz2 := solution.weight_nonneg 2
  simp [normalizedCyclicMatrix, Fin.sum_univ_succ] at h0 h1 h2
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hz0 (sub_nonpos.mpr ht),
    mul_nonpos_of_nonneg_of_nonpos hz1 (sub_nonpos.mpr ht),
    mul_nonpos_of_nonneg_of_nonpos hz2 (sub_nonpos.mpr ht)]

theorem normalizedCyclicMatrix_standardQ_iff {t : ℝ} (ht0 : 0 < t) :
    IsStandardQMatrix (normalizedCyclicMatrix t) ↔ 1 < t := by
  constructor
  · intro hQ
    exact lt_of_not_ge fun ht => not_standardQ_of_ratio_le_one ht0 ht hQ
  · exact normalizedCyclicMatrix_standardQ

private def uniformSimplex : stdSimplex ℝ Player :=
  ⟨fun _ => 1 / 3, by
    constructor
    · intro i; norm_num
    · norm_num [Fin.sum_univ_succ]⟩

@[simp] private theorem uniformSimplex_apply (i : Player) :
    uniformSimplex i = 1 / 3 := rfl

theorem normalizedCyclicMatrix_hasHomogeneous_iff {t : ℝ} (ht0 : 0 < t) :
    HasHomogeneousSimplexSolution (normalizedCyclicMatrix t) ↔ t = 1 := by
  constructor
  · rintro ⟨weight, hresidual, hcomplementary⟩
    let x : ℝ := weight.val 0
    let y : ℝ := weight.val 1
    let z : ℝ := weight.val 2
    have hx : 0 ≤ x := weight.property.1 0
    have hy : 0 ≤ y := weight.property.1 1
    have hz : 0 ≤ z := weight.property.1 2
    have htotal : x + (y + z) = 1 := by
      simpa [x, y, z, Fin.sum_univ_succ] using weight.property.2
    have hr0 : singletonLCPResidual (normalizedCyclicMatrix t) weight 0 =
        -y + t * z := by
      calc
        singletonLCPResidual (normalizedCyclicMatrix t) weight 0 =
            -weight 1 + t * weight 2 := by
          simp [singletonLCPResidual, wsum, dotProduct,
            normalizedCyclicMatrix, Fin.sum_univ_succ, mul_comm]
        _ = -y + t * z := rfl
    have hr1 : singletonLCPResidual (normalizedCyclicMatrix t) weight 1 =
        t * x - z := by
      calc
        singletonLCPResidual (normalizedCyclicMatrix t) weight 1 =
            t * weight 0 + -weight 2 := by
          simp [singletonLCPResidual, wsum, dotProduct,
            normalizedCyclicMatrix, Fin.sum_univ_succ, mul_comm]
        _ = t * x + -z := rfl
        _ = t * x - z := (sub_eq_add_neg _ _).symm
    have hr2 : singletonLCPResidual (normalizedCyclicMatrix t) weight 2 =
        -x + t * y := by
      calc
        singletonLCPResidual (normalizedCyclicMatrix t) weight 2 =
            -weight 0 + t * weight 1 := by
          simp [singletonLCPResidual, wsum, dotProduct,
            normalizedCyclicMatrix, Fin.sum_univ_succ, mul_comm,
            show (2 : Player) ≠ 0 by decide,
            show (2 : Player) ≠ 1 by decide]
        _ = -x + t * y := rfl
    have h0 := hcomplementary 0
    have h1 := hcomplementary 1
    have h2 := hcomplementary 2
    rw [hr0] at h0
    rw [hr1] at h1
    rw [hr2] at h2
    change x * (-y + t * z) = 0 at h0
    change y * (t * x - z) = 0 at h1
    change z * (-x + t * y) = 0 at h2
    by_contra hne
    have hpair : x * y + x * z + y * z = 0 := by
      have htne : t - 1 ≠ 0 := sub_ne_zero.mpr hne
      have : (t - 1) * (x * y + x * z + y * z) = 0 := by
        nlinarith [h0, h1, h2]
      exact (mul_eq_zero.mp this).resolve_left htne
    have hxy : x * y = 0 := by
      nlinarith [mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]
    have hxz : x * z = 0 := by
      nlinarith [mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]
    have hyz : y * z = 0 := by
      nlinarith [mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]
    by_cases hx0 : x = 0
    · by_cases hy0 : y = 0
      · have hz1 : z = 1 := by linarith
        have h := hresidual 1
        rw [hr1, hx0, hz1] at h
        norm_num at h
      · have hz0 : z = 0 := (mul_eq_zero.mp hyz).resolve_left hy0
        have hy1 : y = 1 := by linarith
        have h := hresidual 0
        rw [hr0, hy1, hz0] at h
        norm_num at h
    · have hy0 : y = 0 := (mul_eq_zero.mp hxy).resolve_left hx0
      have hz0 : z = 0 := (mul_eq_zero.mp hxz).resolve_left hx0
      have hx1 : x = 1 := by linarith
      have h := hresidual 2
      rw [hr2, hx1, hy0] at h
      norm_num at h
  · rintro rfl
    refine ⟨uniformSimplex, ?_, ?_⟩
    · intro i
      fin_cases i <;>
        norm_num [singletonLCPResidual, wsum, dotProduct,
          normalizedCyclicMatrix, Fin.sum_univ_succ,
          show (2 : Player) ≠ 1 by decide]
    · intro i
      fin_cases i <;>
        norm_num [singletonLCPResidual, wsum, dotProduct,
          normalizedCyclicMatrix, Fin.sum_univ_succ,
          show (2 : Player) ≠ 1 by decide]

theorem normalizedCyclicMatrix_noHomogeneous_iff {t : ℝ} (ht0 : 0 < t) :
    ¬HasHomogeneousSimplexSolution (normalizedCyclicMatrix t) ↔ t ≠ 1 := by
  rw [not_congr (normalizedCyclicMatrix_hasHomogeneous_iff ht0)]

section Scaling

variable {α : Type} [Fintype α]

private def scaleStandardLCPSolution (c : ℝ) {M : α → α → ℝ}
    {q : α → ℝ} (hc : 0 < c)
    (solution : StandardLCPSolution M (fun i => q i / c)) :
    StandardLCPSolution (fun i j => c * M i j) q where
  weight := solution.weight
  weight_nonneg := solution.weight_nonneg
  residual_nonneg := by
    intro i
    have h := solution.residual_nonneg i
    have hsum : (∑ j, solution.weight j * (c * M i j)) =
        c * ∑ j, solution.weight j * M i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hfactor : q i + ∑ j, solution.weight j * (c * M i j) =
        c * (q i / c + ∑ j, solution.weight j * M i j) := by
      rw [hsum, mul_add]
      field_simp [ne_of_gt hc]
    rw [hfactor]
    exact mul_nonneg hc.le h
  complementary := by
    intro i
    have h := solution.complementary i
    have hcne := ne_of_gt hc
    change solution.weight i *
      (q i + ∑ j, solution.weight j * (c * M i j)) = 0
    have hsum : (∑ j, solution.weight j * (c * M i j)) =
        c * ∑ j, solution.weight j * M i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hfactor : q i + ∑ j, solution.weight j * (c * M i j) =
        c * (q i / c + ∑ j, solution.weight j * M i j) := by
      rw [hsum, mul_add]
      field_simp [hcne]
    rw [hfactor]
    calc
      solution.weight i *
          (c * (q i / c + ∑ j, solution.weight j * M i j)) =
          c * (solution.weight i *
            (q i / c + ∑ j, solution.weight j * M i j)) := by ring
      _ = 0 := by rw [h]; ring

private theorem isStandardQMatrix_posScale (c : ℝ) (hc : 0 < c)
    (M : α → α → ℝ) (hQ : IsStandardQMatrix M) :
    IsStandardQMatrix (fun i j => c * M i j) := by
  intro q
  obtain ⟨solution⟩ := hQ (fun i => q i / c)
  exact ⟨scaleStandardLCPSolution c hc solution⟩

private theorem isStandardQMatrix_posScale_iff (c : ℝ) (hc : 0 < c)
    (M : α → α → ℝ) :
    IsStandardQMatrix (fun i j => c * M i j) ↔ IsStandardQMatrix M := by
  constructor
  · intro hscaled
    have hrecip : 0 < 1 / c := one_div_pos.mpr hc
    have hQ := isStandardQMatrix_posScale (1 / c) hrecip
      (fun i j => c * M i j) hscaled
    have heq : (fun i j => (1 / c) * (c * M i j)) = M := by
      funext i j
      field_simp [ne_of_gt hc]
    rwa [heq] at hQ
  · exact isStandardQMatrix_posScale c hc M

end Scaling

/-- Exact standard-Q region of the positive two-parameter family. -/
theorem cyclicMatrix_standardQ_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsStandardQMatrix (cyclicMatrix a b) ↔ a < b := by
  change IsStandardQMatrix
      (fun i j => a * normalizedCyclicMatrix (b / a) i j) ↔ a < b
  rw [isStandardQMatrix_posScale_iff a ha,
    normalizedCyclicMatrix_standardQ_iff (div_pos hb ha)]
  exact one_lt_div ha

/-- Exact homogeneous obstruction in the positive two-parameter family. -/
theorem cyclicMatrix_noHomogeneous_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ¬HasHomogeneousSimplexSolution (cyclicMatrix a b) ↔ a ≠ b := by
  change ¬HasHomogeneousSimplexSolution
      (fun i j => a * normalizedCyclicMatrix (b / a) i j) ↔ a ≠ b
  rw [not_congr (singletonLCPFeasible_smul_iff ha
      (normalizedCyclicMatrix (b / a))),
    normalizedCyclicMatrix_noHomogeneous_iff (div_pos hb ha)]
  constructor
  · intro hratio hab
    subst b
    exact hratio (div_self ha.ne')
  · intro hab hratio
    apply hab
    have := (div_eq_one_iff_eq ha.ne').mp hratio
    exact this.symm

/-- The nonhomogeneous standard-Q region is exactly the open cone
`0 < a < b`. -/
theorem cyclicMatrix_standardQ_and_noHomogeneous_iff
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsStandardQMatrix (cyclicMatrix a b) ∧
        ¬HasHomogeneousSimplexSolution (cyclicMatrix a b) ↔
      a < b := by
  rw [cyclicMatrix_standardQ_iff ha hb,
    cyclicMatrix_noHomogeneous_iff ha hb]
  exact and_iff_left_of_imp ne_of_lt

end CyclicParametricQ
end QuittingLCPClassification
end GameTheory

namespace GameTheory.QuittingLCPClassification.CyclicParametricQ

#print axioms cyclicMatrix_standardQ_iff
#print axioms cyclicMatrix_noHomogeneous_iff
#print axioms cyclicMatrix_standardQ_and_noHomogeneous_iff

end GameTheory.QuittingLCPClassification.CyclicParametricQ
