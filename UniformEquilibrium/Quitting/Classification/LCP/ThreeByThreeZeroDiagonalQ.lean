/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.CyclicParametricQ

/-!
# Exact three-dimensional zero-diagonal Q classification

For a real `3 × 3` matrix with zero diagonal, this file classifies exactly
the intersection of textbook standard Q with the absence of a homogeneous
simplex solution.

There are only two possible strict sign orientations (the two directed
three-cycles).  In either orientation, standard Q is equivalent to positivity
of the cyclic determinant: the product of the three positive off-diagonal
entries strictly exceeds the absolute product of the three negative entries.

The proof first classifies the six-parameter directed-cycle family.  Positive
row and column scalings reduce it to a one-parameter canonical matrix.  Its Q
property is proved constructively using the empty support, the three
two-coordinate supports, and the full support.  Necessity uses an explicit
strictly positive left multiplier for `q = -1`.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification
namespace ThreeByThreeZeroDiagonalQ

open Finset Math.LinearProgramming

abbrev Player := Fin 3

/-- The two strict directed-cycle orientations. -/
def ForwardOrientation (M : Player → Player → ℝ) : Prop :=
  M 0 1 < 0 ∧ 0 < M 0 2 ∧
  0 < M 1 0 ∧ M 1 2 < 0 ∧
  M 2 0 < 0 ∧ 0 < M 2 1

def ReverseOrientation (M : Player → Player → ℝ) : Prop :=
  0 < M 0 1 ∧ M 0 2 < 0 ∧
  M 1 0 < 0 ∧ 0 < M 1 2 ∧
  0 < M 2 0 ∧ M 2 1 < 0

/-- A zero-diagonal standard-Q matrix outside the homogeneous branch has no
other sign chamber: its six off-diagonal entries form one of the two strict
directed cycles. -/
theorem forward_or_reverse_orientation
    (M : Player → Player → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsStandardQMatrix M)
    (hhom : ¬HasHomogeneousSimplexSolution M) :
    ForwardOrientation M ∨ ReverseOrientation M := by
  obtain ⟨i0, hi0⟩ := exists_negative_entry_in_column_of_noHomogeneous
    M hdiag hhom 0
  obtain ⟨i1, hi1⟩ := exists_negative_entry_in_column_of_noHomogeneous
    M hdiag hhom 1
  obtain ⟨i2, hi2⟩ := exists_negative_entry_in_column_of_noHomogeneous
    M hdiag hhom 2
  obtain ⟨j0, hj0⟩ := exists_positive_entry_in_row_of_standardQ M hQ 0
  obtain ⟨j1, hj1⟩ := exists_positive_entry_in_row_of_standardQ M hQ 1
  obtain ⟨j2, hj2⟩ := exists_positive_entry_in_row_of_standardQ M hQ 2
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;>
    fin_cases j0 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [hdiag] at hi0 hi1 hi2 hj0 hj1 hj2 ⊢ <;>
    first | exact Or.inl ⟨hi1, hj0, hj1, hi2, hi0, hj2⟩ |
      exact Or.inr ⟨hj0, hi2, hi0, hj1, hj2, hi1⟩ |
      linarith

/-- The one-parameter diagonal-scaling normal form. -/
def canonicalMatrix (t : ℝ) : Player → Player → ℝ := fun who owner =>
  if who = 0 then
    if owner = 0 then 0 else if owner = 1 then -1 else t
  else if who = 1 then
    if owner = 0 then 1 else if owner = 1 then 0 else -1
  else
    if owner = 0 then -1 else if owner = 1 then 1 else 0

private def emptySolution (t : ℝ) (q : Player → ℝ)
    (hq : ∀ i, 0 ≤ q i) : StandardLCPSolution (canonicalMatrix t) q where
  weight := 0
  weight_nonneg := by intro i; simp
  residual_nonneg := by intro i; simpa using hq i
  complementary := by intro i; simp

private def pairZeroOneSolution (t : ℝ) (q : Player → ℝ)
    (h0 : 0 ≤ q 0) (h1 : q 1 ≤ 0)
    (hout : 0 ≤ q 0 + q 1 + q 2) :
    StandardLCPSolution (canonicalMatrix t) q where
  weight := ![-q 1, q 0, 0]
  weight_nonneg := by
    intro i
    fin_cases i <;> simp <;> linarith
  residual_nonneg := by
    intro i
    fin_cases i <;> simp [canonicalMatrix, Fin.sum_univ_succ]
    linarith
  complementary := by
    intro i
    fin_cases i <;> simp [canonicalMatrix, Fin.sum_univ_succ]

private def pairOneTwoSolution (t : ℝ) (q : Player → ℝ)
    (h1 : 0 ≤ q 1) (h2 : q 2 ≤ 0)
    (hout : 0 ≤ q 0 + q 2 + t * q 1) :
    StandardLCPSolution (canonicalMatrix t) q where
  weight := ![0, -q 2, q 1]
  weight_nonneg := by
    intro i
    fin_cases i <;> simp <;> linarith
  residual_nonneg := by
    intro i
    fin_cases i <;> simp [canonicalMatrix, Fin.sum_univ_succ]
    nlinarith [hout]
  complementary := by
    intro i
    fin_cases i <;> simp [canonicalMatrix, Fin.sum_univ_succ]

private def pairTwoZeroSolution (t : ℝ) (q : Player → ℝ)
    (ht : 0 < t) (h2 : 0 ≤ q 2) (h0 : q 0 ≤ 0)
    (hout : 0 ≤ q 1 + q 2 + q 0 / t) :
    StandardLCPSolution (canonicalMatrix t) q where
  weight := ![q 2, 0, -q 0 / t]
  weight_nonneg := by
    intro i
    fin_cases i
    · simpa using h2
    · simp
    · simp
      exact div_nonneg (neg_nonneg.mpr h0) ht.le
  residual_nonneg := by
    intro i
    fin_cases i
    · simp [canonicalMatrix, Fin.sum_univ_succ]
      have hzero : q 0 + (-q 0 / t) * t = 0 := by
        field_simp [ne_of_gt ht]
        ring
      rw [hzero]
    · simp [canonicalMatrix, Fin.sum_univ_succ]
      convert hout using 1
      ring
    · simp [canonicalMatrix, Fin.sum_univ_succ]
  complementary := by
    intro i
    fin_cases i
    · simp [canonicalMatrix, Fin.sum_univ_succ]
      right
      field_simp [ne_of_gt ht]
      ring
    · simp [canonicalMatrix, Fin.sum_univ_succ]
    · simp [canonicalMatrix, Fin.sum_univ_succ]

private def fullSolution (t : ℝ) (q : Player → ℝ)
    (hden : 0 < t - 1)
    (h0 : q 0 + t * q 1 + q 2 ≤ 0)
    (h1 : q 0 + t * q 1 + t * q 2 ≤ 0)
    (h2 : q 0 + q 1 + q 2 ≤ 0) :
    StandardLCPSolution (canonicalMatrix t) q where
  weight := fun i =>
    if i = 0 then -(q 0 + t * q 1 + q 2) / (t - 1)
    else if i = 1 then -(q 0 + t * q 1 + t * q 2) / (t - 1)
    else -(q 0 + q 1 + q 2) / (t - 1)
  weight_nonneg := by
    intro i
    fin_cases i
    · simp
      exact div_nonneg (by nlinarith [h0]) hden.le
    · simp
      exact div_nonneg (by nlinarith [h1]) hden.le
    · simp [show (2 : Player) ≠ 0 by decide,
        show (2 : Player) ≠ 1 by decide]
      exact div_nonneg (by nlinarith [h2]) hden.le
  residual_nonneg := by
    intro i
    fin_cases i <;> simp [canonicalMatrix, Fin.sum_univ_succ,
      show (2 : Player) ≠ 0 by decide,
      show (2 : Player) ≠ 1 by decide] <;>
      field_simp [ne_of_gt hden] <;> ring_nf <;> norm_num
  complementary := by
    intro i
    fin_cases i <;> simp [canonicalMatrix, Fin.sum_univ_succ,
      show (2 : Player) ≠ 0 by decide,
      show (2 : Player) ≠ 1 by decide] <;>
      right <;> field_simp [ne_of_gt hden] <;> ring

/-- The canonical matrix is standard Q whenever its cyclic product ratio is
strictly larger than one. -/
theorem canonicalMatrix_standardQ {t : ℝ} (ht : 1 < t) :
    IsStandardQMatrix (canonicalMatrix t) := by
  intro q
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hden : 0 < t - 1 := sub_pos.mpr ht
  by_cases hq0 : 0 ≤ q 0
  · by_cases hq1 : 0 ≤ q 1
    · by_cases hq2 : 0 ≤ q 2
      · exact ⟨emptySolution t q (by intro i; fin_cases i <;> assumption)⟩
      · have hq2' : q 2 ≤ 0 := le_of_lt (lt_of_not_ge hq2)
        by_cases hp : 0 ≤ q 0 + q 2 + t * q 1
        · exact ⟨pairOneTwoSolution t q hq1 hq2' hp⟩
        · exact ⟨fullSolution t q hden (by nlinarith)
            (by nlinarith) (by nlinarith)⟩
    · have hq1' : q 1 ≤ 0 := le_of_lt (lt_of_not_ge hq1)
      by_cases hq2 : 0 ≤ q 2
      · by_cases hp : 0 ≤ q 0 + q 1 + q 2
        · exact ⟨pairZeroOneSolution t q hq0 hq1' hp⟩
        · exact ⟨fullSolution t q hden (by nlinarith)
            (by nlinarith) (by nlinarith)⟩
      · have hq2' : q 2 ≤ 0 := le_of_lt (lt_of_not_ge hq2)
        by_cases hp : 0 ≤ q 0 + q 1 + q 2
        · exact ⟨pairZeroOneSolution t q hq0 hq1' hp⟩
        · exact ⟨fullSolution t q hden (by nlinarith)
            (by nlinarith) (by nlinarith)⟩
  · have hq0' : q 0 ≤ 0 := le_of_lt (lt_of_not_ge hq0)
    by_cases hq1 : 0 ≤ q 1
    · by_cases hq2 : 0 ≤ q 2
      · by_cases hp : 0 ≤ q 1 + q 2 + q 0 / t
        · exact ⟨pairTwoZeroSolution t q ht0 hq2 hq0' hp⟩
        · have hscaled : q 0 + t * q 1 + t * q 2 < 0 := by
            have := lt_of_not_ge hp
            have := mul_lt_mul_of_pos_left this ht0
            field_simp [ne_of_gt ht0] at this
            nlinarith
          exact ⟨fullSolution t q hden (by nlinarith)
            hscaled.le (by nlinarith)⟩
      · have hq2' : q 2 ≤ 0 := le_of_lt (lt_of_not_ge hq2)
        by_cases hp : 0 ≤ q 0 + q 2 + t * q 1
        · exact ⟨pairOneTwoSolution t q hq1 hq2' hp⟩
        · exact ⟨fullSolution t q hden (by nlinarith)
            (by nlinarith) (by nlinarith)⟩
    · have hq1' : q 1 ≤ 0 := le_of_lt (lt_of_not_ge hq1)
      by_cases hq2 : 0 ≤ q 2
      · by_cases hp : 0 ≤ q 1 + q 2 + q 0 / t
        · exact ⟨pairTwoZeroSolution t q ht0 hq2 hq0' hp⟩
        · have hscaled : q 0 + t * q 1 + t * q 2 < 0 := by
            have hfail := lt_of_not_ge hp
            have hmul := mul_lt_mul_of_pos_left hfail ht0
            field_simp [ne_of_gt ht0] at hmul
            nlinarith
          exact ⟨fullSolution t q hden (by nlinarith)
            hscaled.le (by nlinarith)⟩
      · have hq2' : q 2 ≤ 0 := le_of_lt (lt_of_not_ge hq2)
        exact ⟨fullSolution t q hden (by nlinarith)
          (by nlinarith) (by nlinarith)⟩

/-- Positive row and column scaling preserves textbook standard Q. -/
theorem isStandardQMatrix_posDiagonalScale
    {M : Player → Player → ℝ} (row col : Player → ℝ)
    (hrow : ∀ i, 0 < row i) (hcol : ∀ i, 0 < col i)
    (hQ : IsStandardQMatrix M) :
    IsStandardQMatrix (fun i j => row i * M i j * col j) := by
  intro q
  obtain ⟨solution⟩ := hQ (fun i => q i / row i)
  refine ⟨
    { weight := fun i => solution.weight i / col i
      weight_nonneg := fun i => div_nonneg (solution.weight_nonneg i) (hcol i).le
      residual_nonneg := ?_
      complementary := ?_ }⟩
  · intro i
    have h := solution.residual_nonneg i
    have heq : q i + ∑ j, (solution.weight j / col j) *
          (row i * M i j * col j) =
        row i * (q i / row i + ∑ j, solution.weight j * M i j) := by
      rw [mul_add, Finset.mul_sum]
      field_simp [ne_of_gt (hrow i)]
      apply congrArg (fun x => q i + x)
      apply Finset.sum_congr rfl
      intro j _
      field_simp [ne_of_gt (hcol j)]
    rw [heq]
    exact mul_nonneg (hrow i).le h
  · intro i
    have h := solution.complementary i
    have heq : q i + ∑ j, (solution.weight j / col j) *
          (row i * M i j * col j) =
        row i * (q i / row i + ∑ j, solution.weight j * M i j) := by
      rw [mul_add, Finset.mul_sum]
      field_simp [ne_of_gt (hrow i)]
      apply congrArg (fun x => q i + x)
      apply Finset.sum_congr rfl
      intro j _
      field_simp [ne_of_gt (hcol j)]
    rw [heq]
    calc
      (solution.weight i / col i) *
          (row i * (q i / row i + ∑ j, solution.weight j * M i j)) =
          (row i / col i) * (solution.weight i *
            (q i / row i + ∑ j, solution.weight j * M i j)) := by ring
      _ = 0 := by rw [h, mul_zero]

/-- Positive diagonal row/column scaling is an equivalence on standard-Q
matrices. -/
theorem isStandardQMatrix_posDiagonalScale_iff
    {M : Player → Player → ℝ} (row col : Player → ℝ)
    (hrow : ∀ i, 0 < row i) (hcol : ∀ i, 0 < col i) :
    IsStandardQMatrix (fun i j => row i * M i j * col j) ↔
      IsStandardQMatrix M := by
  constructor
  · intro hscaled
    have hinvRow : ∀ i, 0 < (row i)⁻¹ := fun i => inv_pos.mpr (hrow i)
    have hinvCol : ∀ i, 0 < (col i)⁻¹ := fun i => inv_pos.mpr (hcol i)
    have hback := isStandardQMatrix_posDiagonalScale
      (fun i => (row i)⁻¹) (fun i => (col i)⁻¹)
      hinvRow hinvCol hscaled
    have heq :
        (fun i j => (row i)⁻¹ * (row i * M i j * col j) * (col j)⁻¹) = M := by
      funext i j
      field_simp [ne_of_gt (hrow i), ne_of_gt (hcol j)]
    rwa [heq] at hback
  · exact isStandardQMatrix_posDiagonalScale row col hrow hcol

/-- Six positive magnitudes in one directed-cycle orientation. -/
def directedCycleMatrix (a b c d e f : ℝ) : Player → Player → ℝ :=
  fun who owner =>
    if who = 0 then
      if owner = 0 then 0 else if owner = 1 then -a else b
    else if who = 1 then
      if owner = 0 then c else if owner = 1 then 0 else -d
    else
      if owner = 0 then -e else if owner = 1 then f else 0

/-- The oriented cyclic determinant. -/
def cycleGap (a b c d e f : ℝ) : ℝ := b * c * f - a * d * e

private theorem directedCycleMatrix_standardQ_of_gap_pos
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f) :
    IsStandardQMatrix (directedCycleMatrix a b c d e f) := by
  let t := b * c * f / (a * d * e)
  have hden : 0 < a * d * e := mul_pos (mul_pos ha hd) he
  have ht : 1 < t := by
    dsimp [t, cycleGap] at *
    exact (one_lt_div hden).2 (by nlinarith)
  let row : Player → ℝ := ![f / (a * e), 1 / c, 1 / e]
  let col : Player → ℝ := ![1, e / f, c / d]
  have hrow : ∀ i, 0 < row i := by
    intro i
    fin_cases i <;> simp [row] <;> positivity
  have hcol : ∀ i, 0 < col i := by
    intro i
    fin_cases i <;> simp [col] <;> positivity
  have heq :
      (fun i j => row i * directedCycleMatrix a b c d e f i j * col j) =
        canonicalMatrix t := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [row, col, directedCycleMatrix, canonicalMatrix, t] <;>
      field_simp [ne_of_gt ha, ne_of_gt hc, ne_of_gt hd,
        ne_of_gt he, ne_of_gt hf]
  apply (isStandardQMatrix_posDiagonalScale_iff row col hrow hcol).mp
  rw [heq]
  exact canonicalMatrix_standardQ ht

/-- Exact standard-Q region of the positive six-parameter directed-cycle
family. -/
theorem directedCycleMatrix_standardQ_iff
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    IsStandardQMatrix (directedCycleMatrix a b c d e f) ↔
      0 < cycleGap a b c d e f := by
  constructor
  · intro hQ
    by_contra hnot
    have hgap : cycleGap a b c d e f ≤ 0 := le_of_not_gt hnot
    obtain ⟨solution⟩ := hQ (fun _ => -1)
    let x := solution.weight 0
    let y := solution.weight 1
    let z := solution.weight 2
    have hx : 0 ≤ x := solution.weight_nonneg 0
    have hy : 0 ≤ y := solution.weight_nonneg 1
    have hz : 0 ≤ z := solution.weight_nonneg 2
    have h0 := solution.residual_nonneg 0
    have h1 := solution.residual_nonneg 1
    have h2 := solution.residual_nonneg 2
    simp [directedCycleMatrix, Fin.sum_univ_succ] at h0 h1 h2
    have h0' : 0 ≤ -1 - a * y + b * z := by
      dsimp [y, z]
      nlinarith [h0]
    have h1' : 0 ≤ -1 + c * x - d * z := by
      dsimp [x, z]
      nlinarith [h1]
    have h2' : 0 ≤ -1 - e * x + f * y := by
      dsimp [x, y]
      nlinarith [h2]
    have hweighted : 0 ≤
        (c * f) * (-1 - a * y + b * z) +
        (a * e) * (-1 + c * x - d * z) +
        (a * c) * (-1 - e * x + f * y) :=
      add_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg hc.le hf.le) h0')
        (mul_nonneg (mul_nonneg ha.le he.le) h1'))
        (mul_nonneg (mul_nonneg ha.le hc.le) h2')
    have hsumPos : 0 < c * f + a * e + a * c := by positivity
    have hgapz : cycleGap a b c d e f * z ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hgap hz
    have hid :
        (c * f) * (-1 - a * y + b * z) +
          (a * e) * (-1 + c * x - d * z) +
          (a * c) * (-1 - e * x + f * y) =
        -(c * f + a * e + a * c) + cycleGap a b c d e f * z := by
      simp [cycleGap]
      ring
    rw [hid] at hweighted
    linarith
  · exact directedCycleMatrix_standardQ_of_gap_pos ha hb hc hd he hf

private def directedKernelSimplex
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) : stdSimplex ℝ Player := by
  let total := a * d + b * c + a * c
  have htotal : 0 < total := by dsimp [total]; positivity
  refine ⟨![a * d / total, b * c / total, a * c / total], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp <;> positivity
  · simp [Fin.sum_univ_succ, total]
    field_simp [ne_of_gt htotal]
    ring

@[simp] private theorem directedKernelSimplex_zero
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    directedKernelSimplex a b c d ha hb hc hd 0 =
      a * d / (a * d + b * c + a * c) := rfl

@[simp] private theorem directedKernelSimplex_one
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    directedKernelSimplex a b c d ha hb hc hd 1 =
      b * c / (a * d + b * c + a * c) := rfl

@[simp] private theorem directedKernelSimplex_two
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    directedKernelSimplex a b c d ha hb hc hd 2 =
      a * c / (a * d + b * c + a * c) := rfl

/-- In the strict directed-cycle sign chamber, the homogeneous simplex LCP
is feasible exactly on the determinant-zero hypersurface. -/
theorem directedCycleMatrix_hasHomogeneous_iff
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (_hf : 0 < f) :
    HasHomogeneousSimplexSolution (directedCycleMatrix a b c d e f) ↔
      cycleGap a b c d e f = 0 := by
  constructor
  · rintro ⟨weight, hresidual, hcomplementary⟩
    let x : ℝ := weight.val 0
    let y : ℝ := weight.val 1
    let z : ℝ := weight.val 2
    have hx : 0 ≤ x := weight.property.1 0
    have hy : 0 ≤ y := weight.property.1 1
    have hz : 0 ≤ z := weight.property.1 2
    have htotal : x + (y + z) = 1 := by
      change weight.val 0 + (weight.val 1 + weight.val 2) = 1
      simpa [Fin.sum_univ_succ] using weight.property.2
    have hr0 : singletonLCPResidual (directedCycleMatrix a b c d e f)
        weight 0 = -a * y + b * z := by
      dsimp only [x, y, z]
      simp [singletonLCPResidual, wsum, dotProduct, directedCycleMatrix,
        Fin.sum_univ_succ]
      rw [show weight 1 = weight.val 1 by rfl,
        show weight 2 = weight.val 2 by rfl]
      ring
    have hr1 : singletonLCPResidual (directedCycleMatrix a b c d e f)
        weight 1 = c * x - d * z := by
      dsimp only [x, y, z]
      simp [singletonLCPResidual, wsum, dotProduct, directedCycleMatrix,
        Fin.sum_univ_succ]
      rw [show weight 0 = weight.val 0 by rfl,
        show weight 2 = weight.val 2 by rfl]
      ring
    have hr2 : singletonLCPResidual (directedCycleMatrix a b c d e f)
        weight 2 = -e * x + f * y := by
      dsimp only [x, y, z]
      simp [singletonLCPResidual, wsum, dotProduct, directedCycleMatrix,
        Fin.sum_univ_succ,
        show (2 : Player) ≠ 0 by decide, show (2 : Player) ≠ 1 by decide]
      rw [show weight 0 = weight.val 0 by rfl,
        show weight 1 = weight.val 1 by rfl]
      ring
    have hxpos : 0 < x := by
      by_contra hxnot
      have hxzero : x = 0 := le_antisymm (le_of_not_gt hxnot) hx
      have hc1 := hcomplementary 1
      have hc2 := hcomplementary 2
      rw [hr1] at hc1
      rw [hr2] at hc2
      change y * (c * x - d * z) = 0 at hc1
      change z * (-e * x + f * y) = 0 at hc2
      rw [hxzero] at hc1 hc2 htotal
      by_cases hy0 : y = 0
      · have hz1 : z = 1 := by linarith
        have h := hresidual 1
        rw [hr1, hxzero, hz1] at h
        nlinarith
      · have hz0 : z = 0 := by
          rcases mul_eq_zero.mp hc1 with hyzero | hdz
          · exact absurd hyzero hy0
          · nlinarith
        have hy1 : y = 1 := by linarith
        have h := hresidual 0
        rw [hr0, hy1, hz0] at h
        nlinarith
    have hr0zero : -a * y + b * z = 0 := by
      have h := hcomplementary 0
      rw [hr0] at h
      change x * (-a * y + b * z) = 0 at h
      exact (mul_eq_zero.mp h).resolve_left hxpos.ne'
    have hzpos : 0 < z := by
      by_contra hznot
      have hzzero : z = 0 := le_antisymm (le_of_not_gt hznot) hz
      rw [hzzero] at hr0zero
      have hyzero : y = 0 := by nlinarith
      rw [hyzero, hzzero] at htotal
      have hx1 : x = 1 := by linarith
      have h := hresidual 2
      rw [hr2, hx1, hyzero] at h
      nlinarith
    have hypos : 0 < y := by
      by_contra hynot
      have hyzero : y = 0 := le_antisymm (le_of_not_gt hynot) hy
      rw [hyzero] at hr0zero
      nlinarith
    have hr1zero : c * x - d * z = 0 := by
      have h := hcomplementary 1
      rw [hr1] at h
      change y * (c * x - d * z) = 0 at h
      exact (mul_eq_zero.mp h).resolve_left hypos.ne'
    have hr2zero : -e * x + f * y = 0 := by
      have h := hcomplementary 2
      rw [hr2] at h
      change z * (-e * x + f * y) = 0 at h
      exact (mul_eq_zero.mp h).resolve_left hzpos.ne'
    have hdetx : cycleGap a b c d e f * x = 0 := by
      calc
        cycleGap a b c d e f * x =
            b * f * (c * x - d * z) +
              a * d * (-e * x + f * y) +
              d * f * (b * z - a * y) := by
                simp [cycleGap]
                ring
        _ = 0 := by
          have hlast : b * z - a * y = 0 := by linarith [hr0zero]
          rw [hr1zero, hr2zero, hlast]
          ring
    exact (mul_eq_zero.mp hdetx).resolve_right hxpos.ne'
  · intro hgap
    let weight := directedKernelSimplex a b c d ha hb hc hd
    have htotal : 0 < a * d + b * c + a * c := by positivity
    have hr0 : singletonLCPResidual (directedCycleMatrix a b c d e f)
        weight 0 = 0 := by
      simp [weight, wsum, dotProduct, directedCycleMatrix,
        Fin.sum_univ_succ]
      field_simp [ne_of_gt htotal]
      ring
    have hr1 : singletonLCPResidual (directedCycleMatrix a b c d e f)
        weight 1 = 0 := by
      simp [weight, wsum, dotProduct, directedCycleMatrix,
        Fin.sum_univ_succ]
      field_simp [ne_of_gt htotal]
      ring
    have hr2 : singletonLCPResidual (directedCycleMatrix a b c d e f)
        weight 2 = 0 := by
      simp [weight, wsum, dotProduct, directedCycleMatrix,
        Fin.sum_univ_succ, show (2 : Player) ≠ 0 by decide,
        show (2 : Player) ≠ 1 by decide]
      field_simp [ne_of_gt htotal]
      dsimp [cycleGap] at hgap
      nlinarith
    refine ⟨weight, ?_, ?_⟩
    · intro i
      fin_cases i
      · change 0 ≤ singletonLCPResidual
          (directedCycleMatrix a b c d e f) weight 0
        rw [hr0]
      · change 0 ≤ singletonLCPResidual
          (directedCycleMatrix a b c d e f) weight 1
        rw [hr1]
      · change 0 ≤ singletonLCPResidual
          (directedCycleMatrix a b c d e f) weight 2
        rw [hr2]
    · intro i
      fin_cases i
      · change weight 0 * singletonLCPResidual
          (directedCycleMatrix a b c d e f) weight 0 = 0
        rw [hr0, mul_zero]
      · change weight 1 * singletonLCPResidual
          (directedCycleMatrix a b c d e f) weight 1 = 0
        rw [hr1, mul_zero]
      · change weight 2 * singletonLCPResidual
          (directedCycleMatrix a b c d e f) weight 2 = 0
        rw [hr2, mul_zero]

theorem directedCycleMatrix_noHomogeneous_iff
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    ¬HasHomogeneousSimplexSolution (directedCycleMatrix a b c d e f) ↔
      cycleGap a b c d e f ≠ 0 := by
  rw [not_congr (directedCycleMatrix_hasHomogeneous_iff ha hb hc hd he hf)]

/-- Within either strict directed-cycle chamber, standard Q already excludes
the homogeneous hypersurface. -/
theorem directedCycleMatrix_standardQ_and_noHomogeneous_iff
    {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    IsStandardQMatrix (directedCycleMatrix a b c d e f) ∧
        ¬HasHomogeneousSimplexSolution (directedCycleMatrix a b c d e f) ↔
      0 < cycleGap a b c d e f := by
  rw [directedCycleMatrix_standardQ_iff ha hb hc hd he hf,
    directedCycleMatrix_noHomogeneous_iff ha hb hc hd he hf]
  exact and_iff_left_of_imp ne_of_gt

/-- For a zero-diagonal matrix this is its determinant, written without
introducing matrix coordinates. -/
def cycleDeterminant (M : Player → Player → ℝ) : ℝ :=
  M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1

/-- On a zero-diagonal `3 × 3` matrix, the cyclic expression is the ordinary
matrix determinant. -/
theorem cycleDeterminant_eq_det (M : Matrix Player Player ℝ)
    (hdiag : ∀ i, M i i = 0) :
    cycleDeterminant M = Matrix.det M := by
  rw [Matrix.det_fin_three]
  simp [cycleDeterminant, hdiag]

private theorem eq_directedCycleMatrix_of_forward
    (M : Player → Player → ℝ) (hdiag : ∀ i, M i i = 0) :
    M = directedCycleMatrix (-M 0 1) (M 0 2) (M 1 0)
      (-M 1 2) (-M 2 0) (M 2 1) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [directedCycleMatrix, hdiag]

/-- Complete semialgebraic test inside the forward strict sign chamber. -/
theorem standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_forward
    (M : Player → Player → ℝ) (hdiag : ∀ i, M i i = 0)
    (horient : ForwardOrientation M) :
    IsStandardQMatrix M ∧ ¬HasHomogeneousSimplexSolution M ↔
      0 < cycleDeterminant M := by
  rcases horient with ⟨h01, h02, h10, h12, h20, h21⟩
  have ha : 0 < -M 0 1 := neg_pos.mpr h01
  have hb : 0 < M 0 2 := h02
  have hc : 0 < M 1 0 := h10
  have hd : 0 < -M 1 2 := neg_pos.mpr h12
  have he : 0 < -M 2 0 := neg_pos.mpr h20
  have hf : 0 < M 2 1 := h21
  rw [eq_directedCycleMatrix_of_forward M hdiag]
  rw [directedCycleMatrix_standardQ_and_noHomogeneous_iff
    ha hb hc hd he hf]
  simp [cycleGap, cycleDeterminant, directedCycleMatrix]
  ring_nf

private def swapOneTwoFun (i : Player) : Player :=
  if i = 0 then 0 else if i = 1 then 2 else 1

private def swapOneTwo : Player ≃ Player where
  toFun := swapOneTwoFun
  invFun := swapOneTwoFun
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

@[simp] private theorem swapOneTwo_zero : swapOneTwo 0 = 0 := rfl
@[simp] private theorem swapOneTwo_one : swapOneTwo 1 = 2 := rfl
@[simp] private theorem swapOneTwo_two : swapOneTwo 2 = 1 := rfl
@[simp] private theorem swapOneTwo_symm_zero : swapOneTwo.symm 0 = 0 := rfl
@[simp] private theorem swapOneTwo_symm_one : swapOneTwo.symm 1 = 2 := rfl
@[simp] private theorem swapOneTwo_symm_two : swapOneTwo.symm 2 = 1 := rfl

private theorem standardQ_reindex_iff (M : Player → Player → ℝ) :
    IsStandardQMatrix (reindexMatrix swapOneTwo M) ↔
      IsStandardQMatrix M := by
  constructor
  · intro h
    have hback := isStandardQMatrix_reindexMatrix
      swapOneTwo.symm (reindexMatrix swapOneTwo M) h
    have heq : reindexMatrix swapOneTwo.symm
        (reindexMatrix swapOneTwo M) = M := by
      funext i j
      simp [reindexMatrix]
    rwa [heq] at hback
  · exact isStandardQMatrix_reindexMatrix swapOneTwo M

private theorem noHomogeneous_reindex_iff (M : Player → Player → ℝ) :
    ¬HasHomogeneousSimplexSolution (reindexMatrix swapOneTwo M) ↔
      ¬HasHomogeneousSimplexSolution M := by
  exact not_congr (singletonLCPFeasible_reindexMatrix_iff swapOneTwo M)

private theorem forward_reindex_of_reverse
    (M : Player → Player → ℝ) (h : ReverseOrientation M) :
    ForwardOrientation (reindexMatrix swapOneTwo M) := by
  rcases h with ⟨h01, h02, h10, h12, h20, h21⟩
  exact ⟨by simpa [reindexMatrix] using h02,
    by simpa [reindexMatrix] using h01,
    by simpa [reindexMatrix] using h20,
    by simpa [reindexMatrix] using h21,
    by simpa [reindexMatrix] using h10,
    by simpa [reindexMatrix] using h12⟩

private theorem cycleDeterminant_reindex_swap
    (M : Player → Player → ℝ) :
    cycleDeterminant (reindexMatrix swapOneTwo M) = cycleDeterminant M := by
  simp [cycleDeterminant, reindexMatrix]
  ring

/-- Complete semialgebraic test inside the reverse strict sign chamber. -/
theorem standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_reverse
    (M : Player → Player → ℝ) (hdiag : ∀ i, M i i = 0)
    (horient : ReverseOrientation M) :
    IsStandardQMatrix M ∧ ¬HasHomogeneousSimplexSolution M ↔
      0 < cycleDeterminant M := by
  let N := reindexMatrix swapOneTwo M
  have hdiagN : ∀ i, N i i = 0 := by
    intro i
    simp [N, reindexMatrix, hdiag]
  have horientN : ForwardOrientation N :=
    forward_reindex_of_reverse M horient
  have hclass := standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_forward
    N hdiagN horientN
  rw [standardQ_reindex_iff M, noHomogeneous_reindex_iff M,
    cycleDeterminant_reindex_swap M] at hclass
  exact hclass

/-- **Complete `3 × 3` classification.**  A real zero-diagonal matrix is
textbook standard Q and outside the homogeneous simplex branch exactly when
its off-diagonal signs form one of the two strict directed cycles and its
determinant is positive. -/
theorem standardQ_and_noHomogeneous_iff_orientation_and_determinant
    (M : Player → Player → ℝ) (hdiag : ∀ i, M i i = 0) :
    IsStandardQMatrix M ∧ ¬HasHomogeneousSimplexSolution M ↔
      (ForwardOrientation M ∨ ReverseOrientation M) ∧
        0 < cycleDeterminant M := by
  constructor
  · rintro ⟨hQ, hhom⟩
    have horient := forward_or_reverse_orientation M hdiag hQ hhom
    refine ⟨horient, ?_⟩
    rcases horient with hforward | hreverse
    · exact (standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_forward
        M hdiag hforward).mp ⟨hQ, hhom⟩
    · exact (standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_reverse
        M hdiag hreverse).mp ⟨hQ, hhom⟩
  · rintro ⟨hforward | hreverse, hdet⟩
    · exact (standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_forward
        M hdiag hforward).mpr hdet
    · exact (standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_reverse
        M hdiag hreverse).mpr hdet

/-- The complete classification stated with the ordinary matrix
determinant. -/
theorem standardQ_and_noHomogeneous_iff_orientation_and_det_pos
    (M : Matrix Player Player ℝ) (hdiag : ∀ i, M i i = 0) :
    IsStandardQMatrix M ∧ ¬HasHomogeneousSimplexSolution M ↔
      (ForwardOrientation M ∨ ReverseOrientation M) ∧
        0 < Matrix.det M := by
  rw [← cycleDeterminant_eq_det M hdiag]
  exact standardQ_and_noHomogeneous_iff_orientation_and_determinant M hdiag

section ArbitraryThreeElementType

variable {alpha : Type} [Fintype alpha]

/-- Coordinate-free form of the complete classification: on any
three-element type, the condition is equivalent to the existence of a
labeling in which one of the two directed-cycle sign patterns holds and the
cyclic determinant is positive. -/
theorem standardQ_and_noHomogeneous_iff_exists_cyclic_labeling
    (M : alpha → alpha → ℝ) (hcard : Fintype.card alpha = 3)
    (hdiag : ∀ i, M i i = 0) :
    IsStandardQMatrix M ∧ ¬HasHomogeneousSimplexSolution M ↔
      ∃ e : alpha ≃ Player,
        (ForwardOrientation (reindexMatrix e M) ∨
          ReverseOrientation (reindexMatrix e M)) ∧
        0 < cycleDeterminant (reindexMatrix e M) := by
  constructor
  · rintro ⟨hQ, hhom⟩
    let e : alpha ≃ Player := Fintype.equivFinOfCardEq hcard
    have hQe : IsStandardQMatrix (reindexMatrix e M) :=
      isStandardQMatrix_reindexMatrix e M hQ
    have hhome : ¬HasHomogeneousSimplexSolution (reindexMatrix e M) :=
      (not_congr (singletonLCPFeasible_reindexMatrix_iff e M)).mpr hhom
    have hdiage : ∀ i, reindexMatrix e M i i = 0 := by
      intro i
      simp [reindexMatrix, hdiag]
    exact ⟨e,
      (standardQ_and_noHomogeneous_iff_orientation_and_determinant
        (reindexMatrix e M) hdiage).mp ⟨hQe, hhome⟩⟩
  · rintro ⟨e, hclass⟩
    have hdiage : ∀ i, reindexMatrix e M i i = 0 := by
      intro i
      simp [reindexMatrix, hdiag]
    obtain ⟨hQe, hhome⟩ :=
      (standardQ_and_noHomogeneous_iff_orientation_and_determinant
        (reindexMatrix e M) hdiage).mpr hclass
    have hQback := isStandardQMatrix_reindexMatrix e.symm
      (reindexMatrix e M) hQe
    have heq : reindexMatrix e.symm (reindexMatrix e M) = M := by
      funext i j
      simp [reindexMatrix]
    have hQ : IsStandardQMatrix M := by rwa [heq] at hQback
    have hhom : ¬HasHomogeneousSimplexSolution M :=
      (not_congr (singletonLCPFeasible_reindexMatrix_iff e M)).mp hhome
    exact ⟨hQ, hhom⟩

end ArbitraryThreeElementType

end ThreeByThreeZeroDiagonalQ
end QuittingLCPClassification
end GameTheory

namespace GameTheory.QuittingLCPClassification.ThreeByThreeZeroDiagonalQ

#print axioms forward_or_reverse_orientation
#print axioms directedCycleMatrix_standardQ_iff
#print axioms directedCycleMatrix_hasHomogeneous_iff
#print axioms standardQ_and_noHomogeneous_iff_orientation_and_determinant
#print axioms standardQ_and_noHomogeneous_iff_orientation_and_det_pos
#print axioms standardQ_and_noHomogeneous_iff_exists_cyclic_labeling

end GameTheory.QuittingLCPClassification.ThreeByThreeZeroDiagonalQ
