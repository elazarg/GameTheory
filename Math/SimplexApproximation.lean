import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite Simplex Approximation

Generic denominator-clearing lemmas for finite probability vectors.
-/

noncomputable section

open scoped BigOperators

namespace Math

namespace SimplexApproximation

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- Integer counts obtained by flooring all coordinates except `k₀` and putting
the residual mass on `k₀`. This is the denominator-clearing device for turning
a finite convex combination into a finite cycle. -/
def residualFloorCounts (k₀ : κ) (w : κ → ℝ) (N : ℕ) : κ → ℕ :=
  fun k =>
    if k = k₀ then
      N - ∑ k ∈ (Finset.univ.erase k₀), ⌊(N : ℝ) * w k⌋₊
    else
      ⌊(N : ℝ) * w k⌋₊

@[simp] theorem residualFloorCounts_self (k₀ : κ) (w : κ → ℝ) (N : ℕ) :
    residualFloorCounts k₀ w N k₀ =
      N - ∑ k ∈ (Finset.univ.erase k₀), ⌊(N : ℝ) * w k⌋₊ := by
  simp [residualFloorCounts]

theorem residualFloorCounts_ne {k₀ k : κ} (hk : k ≠ k₀) (w : κ → ℝ) (N : ℕ) :
    residualFloorCounts k₀ w N k = ⌊(N : ℝ) * w k⌋₊ := by
  rw [residualFloorCounts, if_neg hk]

/-- The non-residual floored mass is at most the denominator. -/
theorem sum_floor_erase_le_denominator (k₀ : κ) {w : κ → ℝ}
    (hw_nonneg : ∀ k, 0 ≤ w k) (hw_sum : ∑ k, w k = 1) (N : ℕ) :
    ∑ k ∈ (Finset.univ.erase k₀), ⌊(N : ℝ) * w k⌋₊ ≤ N := by
  have hfloor :
      (∑ k ∈ (Finset.univ.erase k₀), (⌊(N : ℝ) * w k⌋₊ : ℝ)) ≤
        ∑ k ∈ (Finset.univ.erase k₀), (N : ℝ) * w k := by
    exact Finset.sum_le_sum fun k _ =>
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (hw_nonneg k))
  have hsum_erase_le :
      ∑ k ∈ (Finset.univ.erase k₀), w k ≤ 1 := by
    have hsplit :
        w k₀ + ∑ k ∈ (Finset.univ.erase k₀), w k = 1 := by
      rw [Finset.add_sum_erase (Finset.univ : Finset κ) w (by simp), hw_sum]
    nlinarith [hw_nonneg k₀]
  have hmul :
      ∑ k ∈ (Finset.univ.erase k₀), (N : ℝ) * w k ≤ (N : ℝ) := by
    rw [← Finset.mul_sum]
    calc
      (N : ℝ) * ∑ k ∈ Finset.univ.erase k₀, w k ≤ (N : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hsum_erase_le (Nat.cast_nonneg N)
      _ = (N : ℝ) := by ring
  exact_mod_cast hfloor.trans hmul

/-- The residual-floor counts have total mass exactly `N`. -/
theorem sum_residualFloorCounts (k₀ : κ) {w : κ → ℝ}
    (hw_nonneg : ∀ k, 0 ≤ w k) (hw_sum : ∑ k, w k = 1) (N : ℕ) :
    ∑ k, residualFloorCounts k₀ w N k = N := by
  let S : ℕ := ∑ k ∈ (Finset.univ.erase k₀), ⌊(N : ℝ) * w k⌋₊
  have hS : S ≤ N := sum_floor_erase_le_denominator k₀ hw_nonneg hw_sum N
  have hsplit :
      ∑ k, residualFloorCounts k₀ w N k =
        residualFloorCounts k₀ w N k₀ +
          ∑ k ∈ (Finset.univ.erase k₀), residualFloorCounts k₀ w N k := by
    rw [← Finset.add_sum_erase (Finset.univ : Finset κ)
      (residualFloorCounts k₀ w N) (by simp)]
  have hsum_erase :
      ∑ k ∈ (Finset.univ.erase k₀), residualFloorCounts k₀ w N k = S := by
    dsimp [S]
    apply Finset.sum_congr rfl
    intro k hk
    exact residualFloorCounts_ne (Finset.ne_of_mem_erase hk) w N
  calc
    ∑ k, residualFloorCounts k₀ w N k
        = (N - S) + S := by
          rw [hsplit, residualFloorCounts_self, hsum_erase]
    _ = N := Nat.sub_add_cancel hS

theorem abs_floor_sub_le_one {a : ℝ} (ha : 0 ≤ a) :
    |(⌊a⌋₊ : ℝ) - a| ≤ 1 := by
  have hle : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
  have hlt : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

theorem residualFloorCounts_self_abs_error_le_card [Nonempty κ] (k₀ : κ) {w : κ → ℝ}
    (hw_nonneg : ∀ k, 0 ≤ w k) (hw_sum : ∑ k, w k = 1) (N : ℕ) :
    |(residualFloorCounts k₀ w N k₀ : ℝ) - (N : ℝ) * w k₀| ≤
      (Fintype.card κ : ℝ) := by
  let S : ℕ := ∑ k ∈ (Finset.univ.erase k₀), ⌊(N : ℝ) * w k⌋₊
  have hS : S ≤ N := sum_floor_erase_le_denominator k₀ hw_nonneg hw_sum N
  have hc0 : (residualFloorCounts k₀ w N k₀ : ℝ) =
      (N : ℝ) - ∑ k ∈ (Finset.univ.erase k₀), (⌊(N : ℝ) * w k⌋₊ : ℝ) := by
    simp [residualFloorCounts, S, Nat.cast_sub hS]
  have hNw0 : (N : ℝ) * w k₀ =
      (N : ℝ) - ∑ k ∈ (Finset.univ.erase k₀), (N : ℝ) * w k := by
    have hsplit : w k₀ + ∑ k ∈ (Finset.univ.erase k₀), w k = 1 := by
      rw [Finset.add_sum_erase (Finset.univ : Finset κ) w (by simp), hw_sum]
    rw [← Finset.mul_sum]
    nlinarith
  have hdiff : (residualFloorCounts k₀ w N k₀ : ℝ) - (N : ℝ) * w k₀ =
      ∑ k ∈ (Finset.univ.erase k₀), ((N : ℝ) * w k - (⌊(N : ℝ) * w k⌋₊ : ℝ)) := by
    rw [hc0, hNw0]
    rw [Finset.sum_sub_distrib]
    ring
  have hnonneg : 0 ≤ ∑ k ∈ (Finset.univ.erase k₀),
      ((N : ℝ) * w k - (⌊(N : ℝ) * w k⌋₊ : ℝ)) := by
    exact Finset.sum_nonneg fun k _ =>
      sub_nonneg.mpr (Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (hw_nonneg k)))
  rw [hdiff, abs_of_nonneg hnonneg]
  calc
    ∑ k ∈ (Finset.univ.erase k₀), ((N : ℝ) * w k - (⌊(N : ℝ) * w k⌋₊ : ℝ))
        ≤ ∑ k ∈ (Finset.univ.erase k₀), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _hk
          have hlt : (N : ℝ) * w k < (⌊(N : ℝ) * w k⌋₊ : ℝ) + 1 :=
            Nat.lt_floor_add_one ((N : ℝ) * w k)
          linarith
    _ = ((Finset.univ.erase k₀).card : ℝ) := by simp
    _ ≤ (Fintype.card κ : ℝ) := by
      exact_mod_cast Finset.card_le_univ (Finset.univ.erase k₀)

theorem residualFloorCounts_abs_error_le_card [Nonempty κ] (k₀ : κ) {w : κ → ℝ}
    (hw_nonneg : ∀ k, 0 ≤ w k) (hw_sum : ∑ k, w k = 1) (N : ℕ) (k : κ) :
    |(residualFloorCounts k₀ w N k : ℝ) - (N : ℝ) * w k| ≤
      (Fintype.card κ : ℝ) := by
  by_cases hk : k = k₀
  · subst hk
    exact residualFloorCounts_self_abs_error_le_card k hw_nonneg hw_sum N
  · rw [residualFloorCounts_ne hk]
    have hle1 : |(⌊(N : ℝ) * w k⌋₊ : ℝ) - (N : ℝ) * w k| ≤ 1 :=
      abs_floor_sub_le_one (mul_nonneg (Nat.cast_nonneg N) (hw_nonneg k))
    have hcard : (1 : ℝ) ≤ (Fintype.card κ : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card κ)
    exact hle1.trans hcard

end SimplexApproximation

end Math
