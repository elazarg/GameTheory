/-
# Finite simplex approximation

Generic denominator-clearing lemmas for finite probability vectors.
-/

import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open scoped BigOperators

namespace GameTheory.Math.SimplexApproximation

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Floor every coordinate except `base`, then place the residual mass there. -/
def residualFloorCounts (base : κ) (weight : κ → ℝ) (denominator : ℕ) :
    κ → ℕ :=
  fun k =>
    if k = base then
      denominator -
        ∑ j ∈ Finset.univ.erase base, ⌊(denominator : ℝ) * weight j⌋₊
    else
      ⌊(denominator : ℝ) * weight k⌋₊

@[simp]
theorem residualFloorCounts_self (base : κ) (weight : κ → ℝ)
    (denominator : ℕ) :
    residualFloorCounts base weight denominator base =
      denominator -
        ∑ k ∈ Finset.univ.erase base, ⌊(denominator : ℝ) * weight k⌋₊ := by
  simp [residualFloorCounts]

theorem residualFloorCounts_ne {base k : κ} (hk : k ≠ base)
    (weight : κ → ℝ) (denominator : ℕ) :
    residualFloorCounts base weight denominator k =
      ⌊(denominator : ℝ) * weight k⌋₊ := by
  rw [residualFloorCounts, if_neg hk]

theorem sum_floor_erase_le_denominator (base : κ) {weight : κ → ℝ}
    (hweight : ∀ k, 0 ≤ weight k) (hsum : ∑ k, weight k = 1)
    (denominator : ℕ) :
    ∑ k ∈ Finset.univ.erase base,
        ⌊(denominator : ℝ) * weight k⌋₊ ≤ denominator := by
  have hfloor :
      (∑ k ∈ Finset.univ.erase base,
          (⌊(denominator : ℝ) * weight k⌋₊ : ℝ)) ≤
        ∑ k ∈ Finset.univ.erase base, (denominator : ℝ) * weight k := by
    exact Finset.sum_le_sum fun k _ =>
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg denominator) (hweight k))
  have herase : ∑ k ∈ Finset.univ.erase base, weight k ≤ 1 := by
    have hsplit :
        weight base + ∑ k ∈ Finset.univ.erase base, weight k = 1 := by
      rw [Finset.add_sum_erase (Finset.univ : Finset κ) weight (by simp),
        hsum]
    linarith [hweight base]
  have hmul :
      ∑ k ∈ Finset.univ.erase base, (denominator : ℝ) * weight k ≤
        (denominator : ℝ) := by
    rw [← Finset.mul_sum]
    calc
      (denominator : ℝ) * ∑ k ∈ Finset.univ.erase base, weight k ≤
          (denominator : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left herase (Nat.cast_nonneg denominator)
      _ = (denominator : ℝ) := by ring
  exact_mod_cast hfloor.trans hmul

/-- The residual-floor counts have exactly the requested total mass. -/
theorem sum_residualFloorCounts (base : κ) {weight : κ → ℝ}
    (hweight : ∀ k, 0 ≤ weight k) (hsum : ∑ k, weight k = 1)
    (denominator : ℕ) :
    ∑ k, residualFloorCounts base weight denominator k = denominator := by
  let total : ℕ :=
    ∑ k ∈ Finset.univ.erase base, ⌊(denominator : ℝ) * weight k⌋₊
  have htotal : total ≤ denominator :=
    sum_floor_erase_le_denominator base hweight hsum denominator
  have hsplit :
      ∑ k, residualFloorCounts base weight denominator k =
        residualFloorCounts base weight denominator base +
          ∑ k ∈ Finset.univ.erase base,
            residualFloorCounts base weight denominator k := by
    rw [← Finset.add_sum_erase (Finset.univ : Finset κ)
      (residualFloorCounts base weight denominator) (by simp)]
  have herase :
      ∑ k ∈ Finset.univ.erase base,
          residualFloorCounts base weight denominator k = total := by
    dsimp [total]
    apply Finset.sum_congr rfl
    intro k hk
    exact residualFloorCounts_ne (Finset.ne_of_mem_erase hk) weight denominator
  calc
    ∑ k, residualFloorCounts base weight denominator k =
        (denominator - total) + total := by
      rw [hsplit, residualFloorCounts_self, herase]
    _ = denominator := Nat.sub_add_cancel htotal

theorem abs_floor_sub_le_one {value : ℝ} (hvalue : 0 ≤ value) :
    |(⌊value⌋₊ : ℝ) - value| ≤ 1 := by
  have hle : (⌊value⌋₊ : ℝ) ≤ value := Nat.floor_le hvalue
  have hlt : value < (⌊value⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one value
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

theorem residualFloorCounts_self_abs_error_le_card
    (base : κ) {weight : κ → ℝ}
    (hweight : ∀ k, 0 ≤ weight k) (hsum : ∑ k, weight k = 1)
    (denominator : ℕ) :
    |(residualFloorCounts base weight denominator base : ℝ) -
        (denominator : ℝ) * weight base| ≤ (Fintype.card κ : ℝ) := by
  let total : ℕ :=
    ∑ k ∈ Finset.univ.erase base, ⌊(denominator : ℝ) * weight k⌋₊
  have htotal : total ≤ denominator :=
    sum_floor_erase_le_denominator base hweight hsum denominator
  have hcount :
      (residualFloorCounts base weight denominator base : ℝ) =
        (denominator : ℝ) -
          ∑ k ∈ Finset.univ.erase base,
            (⌊(denominator : ℝ) * weight k⌋₊ : ℝ) := by
    simp [residualFloorCounts, total, Nat.cast_sub htotal]
  have hmass :
      (denominator : ℝ) * weight base =
        (denominator : ℝ) -
          ∑ k ∈ Finset.univ.erase base,
            (denominator : ℝ) * weight k := by
    have hsplit :
        weight base + ∑ k ∈ Finset.univ.erase base, weight k = 1 := by
      rw [Finset.add_sum_erase (Finset.univ : Finset κ) weight (by simp),
        hsum]
    rw [← Finset.mul_sum]
    nlinarith
  have hdiff :
      (residualFloorCounts base weight denominator base : ℝ) -
          (denominator : ℝ) * weight base =
        ∑ k ∈ Finset.univ.erase base,
          ((denominator : ℝ) * weight k -
            (⌊(denominator : ℝ) * weight k⌋₊ : ℝ)) := by
    rw [hcount, hmass, Finset.sum_sub_distrib]
    ring
  have hnonneg :
      0 ≤ ∑ k ∈ Finset.univ.erase base,
        ((denominator : ℝ) * weight k -
          (⌊(denominator : ℝ) * weight k⌋₊ : ℝ)) := by
    exact Finset.sum_nonneg fun k _ =>
      sub_nonneg.mpr
        (Nat.floor_le
          (mul_nonneg (Nat.cast_nonneg denominator) (hweight k)))
  rw [hdiff, abs_of_nonneg hnonneg]
  calc
    ∑ k ∈ Finset.univ.erase base,
        ((denominator : ℝ) * weight k -
          (⌊(denominator : ℝ) * weight k⌋₊ : ℝ)) ≤
        ∑ _k ∈ Finset.univ.erase base, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      have hlt :
          (denominator : ℝ) * weight k <
            (⌊(denominator : ℝ) * weight k⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one ((denominator : ℝ) * weight k)
      linarith
    _ = ((Finset.univ.erase base).card : ℝ) := by simp
    _ ≤ (Fintype.card κ : ℝ) := by
      exact_mod_cast Finset.card_le_univ (Finset.univ.erase base)

/-- Every coordinate count differs from its ideal mass by at most the carrier
cardinality. -/
theorem residualFloorCounts_abs_error_le_card
    (base : κ) {weight : κ → ℝ}
    (hweight : ∀ k, 0 ≤ weight k) (hsum : ∑ k, weight k = 1)
    (denominator : ℕ) (k : κ) :
    |(residualFloorCounts base weight denominator k : ℝ) -
        (denominator : ℝ) * weight k| ≤ (Fintype.card κ : ℝ) := by
  by_cases hk : k = base
  · subst hk
    exact residualFloorCounts_self_abs_error_le_card
      k hweight hsum denominator
  · rw [residualFloorCounts_ne hk]
    have hone :
        |(⌊(denominator : ℝ) * weight k⌋₊ : ℝ) -
            (denominator : ℝ) * weight k| ≤ 1 :=
      abs_floor_sub_le_one
        (mul_nonneg (Nat.cast_nonneg denominator) (hweight k))
    have hcard : (1 : ℝ) ≤ (Fintype.card κ : ℝ) := by
      exact_mod_cast
        (Fintype.card_pos_iff.mpr ⟨base⟩ : 0 < Fintype.card κ)
    exact hone.trans hcard

end GameTheory.Math.SimplexApproximation
