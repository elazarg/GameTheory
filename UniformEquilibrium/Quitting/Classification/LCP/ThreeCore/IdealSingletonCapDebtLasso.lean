/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeByThreeZeroDiagonalQ

/-!
# Ideal singleton-block cap and debt dynamics

This file isolates the finite-dimensional algebra behind three-core
elimination. An ideal singleton block is the zero-mesh limit of a finite block
in which only one player may quit. Carrier realization is supplied separately.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Ideal action of an owner singleton block on the vector of cap clearances
above own-singleton rewards. -/
def idealSingletonClearance
    (M : ι → ι → ℝ) (owner : ι) (α : ℝ) (t : ι → ℝ) : ι → ℝ :=
  fun who =>
    if who = owner then t who
    else max 0 (α * t who + (1 - α) * M who owner)

/-- Ideal action of the same block on total semantic debt. -/
def idealSingletonDebt
    (M : ι → ι → ℝ) (owner : ι) (α : ℝ)
    (t : ι → ℝ) (D : ℝ) : ℝ :=
  α * D + (1 - α) * t owner +
    ∑ who ∈ Finset.univ.erase owner,
      max 0 (-(α * t who + (1 - α) * M who owner))

/-- If the owner clearance vanishes and every opponent update stays
nonnegative, the block has no additive debt charge. -/
theorem idealSingletonDebt_eq_mul_of_zeroCost
    (M : ι → ι → ℝ) (owner : ι) (α : ℝ)
    (t : ι → ℝ) (D : ℝ)
    (howner : t owner = 0)
    (hnonneg : ∀ who, who ≠ owner →
      0 ≤ α * t who + (1 - α) * M who owner) :
    idealSingletonDebt M owner α t D = α * D := by
  unfold idealSingletonDebt
  rw [howner, mul_zero, add_zero]
  have hsum :
      (∑ who ∈ Finset.univ.erase owner,
        max 0 (-(α * t who + (1 - α) * M who owner))) = 0 := by
    apply Finset.sum_eq_zero
    intro who hwho
    have hne : who ≠ owner := by simpa using hwho
    rw [max_eq_left]
    linarith [hnonneg who hne]
  rw [hsum, add_zero]

namespace Question193ThreeCore

open QuittingLCPClassification.ThreeByThreeZeroDiagonalQ

abbrev Player := Fin 3

/-- Axis state with only coordinate two nonzero. -/
def axisTwo (H : ℝ) : Player → ℝ := ![0, 0, H]

/-- Axis state with only coordinate one nonzero. -/
def axisOne (H : ℝ) : Player → ℝ := ![0, H, 0]

/-- Axis state with only coordinate zero nonzero. -/
def axisZero (H : ℝ) : Player → ℝ := ![H, 0, 0]

/-- First zero-cost cyclic ratio. -/
def firstRatio (e H : ℝ) : ℝ := e / (H + e)

/-- Height after the first cyclic block. -/
def secondHeight (c e H : ℝ) : ℝ := c * H / (H + e)

/-- Second zero-cost cyclic ratio. -/
def secondRatio (d H₂ : ℝ) : ℝ := d / (H₂ + d)

/-- Height after the second cyclic block. -/
def firstHeight (b d H₂ : ℝ) : ℝ := b * H₂ / (H₂ + d)

/-- Third zero-cost cyclic ratio. -/
def thirdRatio (a H₁ : ℝ) : ℝ := a / (H₁ + a)

/-- Height-return map of the three-block ideal cycle. -/
def heightReturn (a b c d e f H : ℝ) : ℝ :=
  b * c * f * H / ((b * c + a * (c + d)) * H + a * d * e)

/-- Positive fixed height of the directed three-cycle when its determinant
is positive. -/
def fixedHeight (a b c d e f : ℝ) : ℝ :=
  (b * c * f - a * d * e) / (b * c + a * (c + d))

private theorem ratio_balance {H x : ℝ} (hH : 0 < H) (hx : 0 < x) :
    x / (H + x) * H = (1 - x / (H + x)) * x := by
  field_simp [ne_of_gt (add_pos hH hx)]
  ring

private theorem one_sub_ratio_pos {H x : ℝ} (hH : 0 < H) (hx : 0 < x) :
    0 < 1 - x / (H + x) := by
  have hden : 0 < H + x := add_pos hH hx
  have hlt : x / (H + x) < 1 := (div_lt_one hden).2 (by linarith)
  linarith

private theorem one_sub_ratio_mul {H x y : ℝ} (hH : 0 < H) (hx : 0 < x) :
    (1 - x / (H + x)) * y = H * y / (H + x) := by
  field_simp [ne_of_gt (add_pos hH hx)]
  ring

private theorem ratio_nonneg {H x : ℝ} (hH : 0 < H) (hx : 0 < x) :
    0 ≤ x / (H + x) := (div_pos hx (add_pos hH hx)).le

private theorem ratio_lt_one {H x : ℝ} (hH : 0 < H) (hx : 0 < x) :
    x / (H + x) < 1 := (div_lt_one (add_pos hH hx)).2 (by linarith)

theorem first_block
    {a b c d e f H : ℝ}
    (hH : 0 < H) (he : 0 < e) (hc : 0 < c) :
    idealSingletonClearance (directedCycleMatrix a b c d e f) 0
        (firstRatio e H) (axisTwo H) =
      axisOne (secondHeight c e H) := by
  funext who
  fin_cases who
  · simp [idealSingletonClearance, axisTwo, axisOne]
  · simp [idealSingletonClearance, directedCycleMatrix, firstRatio,
      axisTwo, axisOne, secondHeight]
    rw [max_eq_right]
    · simpa [mul_comm] using one_sub_ratio_mul (y := c) hH he
    · exact mul_nonneg (one_sub_ratio_pos hH he).le hc.le
  · simp [idealSingletonClearance, directedCycleMatrix, firstRatio,
      axisTwo, axisOne]
    exact (ratio_balance hH he).le

theorem first_block_zeroCost
    {a b c d e f H D : ℝ}
    (hH : 0 < H) (he : 0 < e) (hc : 0 < c) :
    idealSingletonDebt (directedCycleMatrix a b c d e f) 0
        (firstRatio e H) (axisTwo H) D = firstRatio e H * D := by
  apply idealSingletonDebt_eq_mul_of_zeroCost
  · simp [axisTwo]
  · intro who hwho
    fin_cases who
    · exact (hwho rfl).elim
    · simp [directedCycleMatrix, firstRatio, axisTwo]
      exact mul_nonneg (one_sub_ratio_pos hH he).le hc.le
    · simp [directedCycleMatrix, firstRatio, axisTwo]
      rw [← ratio_balance hH he]

theorem second_block
    {a b c d e f H₂ : ℝ}
    (hH₂ : 0 < H₂) (hd : 0 < d) (hb : 0 < b) :
    idealSingletonClearance (directedCycleMatrix a b c d e f) 2
        (secondRatio d H₂) (axisOne H₂) =
      axisZero (firstHeight b d H₂) := by
  funext who
  fin_cases who
  · simp [idealSingletonClearance, directedCycleMatrix, secondRatio,
      axisOne, axisZero, firstHeight]
    rw [max_eq_right]
    · simpa [mul_comm] using one_sub_ratio_mul (y := b) hH₂ hd
    · exact mul_nonneg (one_sub_ratio_pos hH₂ hd).le hb.le
  · simp [idealSingletonClearance, directedCycleMatrix, secondRatio,
      axisOne, axisZero]
    exact (ratio_balance hH₂ hd).le
  · simp [idealSingletonClearance, axisOne, axisZero]

theorem second_block_zeroCost
    {a b c d e f H₂ D : ℝ}
    (hH₂ : 0 < H₂) (hd : 0 < d) (hb : 0 < b) :
    idealSingletonDebt (directedCycleMatrix a b c d e f) 2
        (secondRatio d H₂) (axisOne H₂) D = secondRatio d H₂ * D := by
  apply idealSingletonDebt_eq_mul_of_zeroCost
  · simp [axisOne]
  · intro who hwho
    fin_cases who
    · simp [directedCycleMatrix, secondRatio, axisOne]
      exact mul_nonneg (one_sub_ratio_pos hH₂ hd).le hb.le
    · simp [directedCycleMatrix, secondRatio, axisOne]
      rw [← ratio_balance hH₂ hd]
    · exact (hwho rfl).elim

theorem third_block
    {a b c d e f H₁ : ℝ}
    (hH₁ : 0 < H₁) (ha : 0 < a) (hf : 0 < f) :
    idealSingletonClearance (directedCycleMatrix a b c d e f) 1
        (thirdRatio a H₁) (axisZero H₁) =
      axisTwo (f * H₁ / (H₁ + a)) := by
  funext who
  fin_cases who
  · simp [idealSingletonClearance, directedCycleMatrix, thirdRatio,
      axisZero, axisTwo]
    exact (ratio_balance hH₁ ha).le
  · simp [idealSingletonClearance, axisZero, axisTwo]
  · simp [idealSingletonClearance, directedCycleMatrix, thirdRatio,
      axisZero, axisTwo]
    rw [max_eq_right]
    · simpa [mul_comm] using one_sub_ratio_mul (y := f) hH₁ ha
    · exact mul_nonneg (one_sub_ratio_pos hH₁ ha).le hf.le

theorem third_block_zeroCost
    {a b c d e f H₁ D : ℝ}
    (hH₁ : 0 < H₁) (ha : 0 < a) (hf : 0 < f) :
    idealSingletonDebt (directedCycleMatrix a b c d e f) 1
        (thirdRatio a H₁) (axisZero H₁) D = thirdRatio a H₁ * D := by
  apply idealSingletonDebt_eq_mul_of_zeroCost
  · simp [axisZero]
  · intro who hwho
    fin_cases who
    · simp [directedCycleMatrix, thirdRatio, axisZero]
      rw [← ratio_balance hH₁ ha]
    · exact (hwho rfl).elim
    · simp [directedCycleMatrix, thirdRatio, axisZero]
      exact mul_nonneg (one_sub_ratio_pos hH₁ ha).le hf.le

/-- The three successive axis heights have the displayed rational return map. -/
theorem three_block_height_eq_return
    {a b c d e f H : ℝ}
    (hH : 0 < H) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) :
    f * firstHeight b d (secondHeight c e H) /
        (firstHeight b d (secondHeight c e H) + a) =
      heightReturn a b c d e f H := by
  unfold firstHeight secondHeight heightReturn
  field_simp [ne_of_gt (add_pos hH he)]
  ring

theorem fixedHeight_pos
    {a b c d e f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hdet : a * d * e < b * c * f) :
    0 < fixedHeight a b c d e f := by
  unfold fixedHeight
  exact div_pos (sub_pos.mpr hdet)
    (add_pos (mul_pos hb hc) (mul_pos ha (add_pos hc hd)))

theorem heightReturn_fixed
    {a b c d e f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hdet : a * d * e < b * c * f) :
    heightReturn a b c d e f (fixedHeight a b c d e f) =
      fixedHeight a b c d e f := by
  have hA : 0 < b * c + a * (c + d) :=
    add_pos (mul_pos hb hc) (mul_pos ha (add_pos hc hd))
  have hH := fixedHeight_pos ha hb hc hd hdet
  have hB : 0 < b * c * f := lt_trans (mul_pos (mul_pos ha hd) he) hdet
  unfold heightReturn fixedHeight
  field_simp [ne_of_gt hA, ne_of_gt hB]
  ring

theorem heightReturn_pos
    {a b c d e f H : ℝ}
    (hH : 0 < H) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    0 < heightReturn a b c d e f H := by
  unfold heightReturn
  exact div_pos (mul_pos (mul_pos (mul_pos hb hc) hf) hH)
    (add_pos
      (mul_pos (add_pos (mul_pos hb hc) (mul_pos ha (add_pos hc hd))) hH)
      (mul_pos (mul_pos ha hd) he))

/-- Above the fixed height, the return map stays above it. -/
theorem fixedHeight_le_heightReturn_of_le
    {a b c d e f H : ℝ}
    (hH : fixedHeight a b c d e f ≤ H)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e)
    (hdet : a * d * e < b * c * f) :
    fixedHeight a b c d e f ≤ heightReturn a b c d e f H := by
  have hA : 0 < b * c + a * (c + d) :=
    add_pos (mul_pos hb hc) (mul_pos ha (add_pos hc hd))
  have hstar := fixedHeight_pos ha hb hc hd hdet
  have hHpos : 0 < H := lt_of_lt_of_le hstar hH
  have hden : 0 < (b * c + a * (c + d)) * H + a * d * e :=
    add_pos (mul_pos hA hHpos) (mul_pos (mul_pos ha hd) he)
  unfold fixedHeight heightReturn at *
  apply (div_le_div_iff₀ hA hden).2
  have hAH : b * c * f - a * d * e ≤
      (b * c + a * (c + d)) * H := by
    simpa [mul_comm] using (div_le_iff₀ hA).1 hH
  rw [← sub_nonneg]
  rw [show
    b * c * f * H * (b * c + a * (c + d)) -
        (b * c * f - a * d * e) *
          ((b * c + a * (c + d)) * H + a * d * e) =
      a * d * e *
        ((b * c + a * (c + d)) * H - (b * c * f - a * d * e)) by ring]
  exact mul_nonneg (mul_nonneg (mul_pos ha hd).le he.le)
    (sub_nonneg.mpr hAH)

/-- Below the fixed height, one return does not decrease the height. -/
theorem le_heightReturn_of_le_fixedHeight
    {a b c d e f H : ℝ}
    (hH : 0 < H) (hle : H ≤ fixedHeight a b c d e f)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) :
    H ≤ heightReturn a b c d e f H := by
  have hA : 0 < b * c + a * (c + d) :=
    add_pos (mul_pos hb hc) (mul_pos ha (add_pos hc hd))
  have hden : 0 < (b * c + a * (c + d)) * H + a * d * e :=
    add_pos (mul_pos hA hH) (mul_pos (mul_pos ha hd) he)
  unfold fixedHeight at hle
  have hscaled := (le_div_iff₀ hA).1 hle
  have hdenLe : (b * c + a * (c + d)) * H + a * d * e ≤
      b * c * f := by linarith
  unfold heightReturn
  apply (le_div_iff₀ hden).2
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hdenLe hH.le

/-- The smaller of the initial and fixed heights is invariant under the
height return map. -/
theorem min_height_fixed_le_heightReturn
    {a b c d e f H₀ H : ℝ}
    (hH₀ : 0 < H₀) (hH : min H₀ (fixedHeight a b c d e f) ≤ H)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e)
    (hdet : a * d * e < b * c * f) :
    min H₀ (fixedHeight a b c d e f) ≤
      heightReturn a b c d e f H := by
  have hstar := fixedHeight_pos ha hb hc hd hdet
  have hminPos : 0 < min H₀ (fixedHeight a b c d e f) :=
    lt_min hH₀ hstar
  have hHpos : 0 < H := lt_of_lt_of_le hminPos hH
  rcases le_total H (fixedHeight a b c d e f) with hle | hge
  · exact hH.trans (le_heightReturn_of_le_fixedHeight hHpos hle
      ha hb hc hd he)
  · exact (min_le_right _ _).trans
      (fixedHeight_le_heightReturn_of_le hge ha hb hc hd he hdet)

/-- A positive lower bound on height gives a uniform strict upper bound on
the first contraction factor. -/
theorem firstRatio_le_of_height_lower
    {e lower H : ℝ} (he : 0 < e) (hlower : 0 < lower)
    (hH : lower ≤ H) :
    firstRatio e H ≤ e / (lower + e) := by
  unfold firstRatio
  exact div_le_div_of_nonneg_left he.le (add_pos hlower he)
    (by simpa [add_comm] using add_le_add_right hH e)

theorem fixed_height_contraction_nonneg_lt_one
    {e lower : ℝ} (he : 0 < e) (hlower : 0 < lower) :
    0 ≤ e / (lower + e) ∧ e / (lower + e) < 1 := by
  exact ⟨(div_pos he (add_pos hlower he)).le,
    (div_lt_one (add_pos hlower he)).2 (by linarith)⟩

/-- The product of the three zero-cost ratios is controlled by its first
factor, hence by any uniform positive lower bound on the axis height. -/
theorem three_ratio_product_le_fixed_contraction
    {a b c d e H : ℝ}
    (hH : 0 < H) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e)
    {lower : ℝ} (hlower : 0 < lower) (hlowerH : lower ≤ H) :
    firstRatio e H * secondRatio d (secondHeight c e H) *
        thirdRatio a (firstHeight b d (secondHeight c e H)) ≤
      e / (lower + e) := by
  have hH₂ : 0 < secondHeight c e H := by
    unfold secondHeight
    exact div_pos (mul_pos hc hH) (add_pos hH he)
  have hH₁ : 0 < firstHeight b d (secondHeight c e H) := by
    unfold firstHeight
    exact div_pos (mul_pos hb hH₂) (add_pos hH₂ hd)
  have hfirst0 : 0 ≤ firstRatio e H := ratio_nonneg hH he
  have hsecond0 : 0 ≤ secondRatio d (secondHeight c e H) :=
    ratio_nonneg hH₂ hd
  have hthird0 : 0 ≤ thirdRatio a
      (firstHeight b d (secondHeight c e H)) := ratio_nonneg hH₁ ha
  have hsecond1 : secondRatio d (secondHeight c e H) ≤ 1 :=
    (ratio_lt_one hH₂ hd).le
  have hthird1 : thirdRatio a
      (firstHeight b d (secondHeight c e H)) ≤ 1 :=
    (ratio_lt_one hH₁ ha).le
  have hproductFirst :
      firstRatio e H * secondRatio d (secondHeight c e H) *
          thirdRatio a (firstHeight b d (secondHeight c e H)) ≤
        firstRatio e H := by
    have hmul : secondRatio d (secondHeight c e H) *
        thirdRatio a (firstHeight b d (secondHeight c e H)) ≤ 1 := by
      simpa using mul_le_mul hsecond1 hthird1 hthird0
        (by norm_num : 0 ≤ (1 : ℝ))
    calc
      firstRatio e H * secondRatio d (secondHeight c e H) *
          thirdRatio a (firstHeight b d (secondHeight c e H)) =
          firstRatio e H *
            (secondRatio d (secondHeight c e H) *
              thirdRatio a (firstHeight b d (secondHeight c e H))) := by ring
      _ ≤ firstRatio e H * 1 := mul_le_mul_of_nonneg_left hmul hfirst0
      _ = firstRatio e H := mul_one _
  exact hproductFirst.trans (firstRatio_le_of_height_lower he hlower hlowerH)

end Question193ThreeCore

end GameTheory
