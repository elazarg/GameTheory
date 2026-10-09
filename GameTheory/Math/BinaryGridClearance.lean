import GameTheory.Math.BinaryExtraction
import Mathlib.Tactic.FieldSimp

/-! Clearance from interior dyadic grid lines bounds every binary threshold margin.
The exact threshold-grid identity transfers geometric extraction error bounds to stable digits,
including the closed unit interval endpoints. -/

namespace GameTheory.Math

/-- Every extracted threshold corresponds to an interior grid point at finer depth. -/
theorem binaryThreshold_grid_witness (b j : ℕ) (q : ℚ) (hj : j < b) :
    ∃ l : ℕ, 0 < l ∧ l < 2 ^ b ∧
      binaryRemainder j q - 1 / 2 = (2 : ℚ) ^ j * (q - (l : ℚ) / (2 : ℚ) ^ b) := by
  let p := binaryPrefix j q
  let l := (2 * p + 1) * 2 ^ (b - (j + 1))
  have hp : 2 * p + 1 < 2 ^ (j + 1) := by
    have hh := binaryPrefix_lt j q
    dsimp [p]
    rw [pow_succ]
    omega
  have hpow : 2 ^ b = 2 ^ (j + 1) * 2 ^ (b - (j + 1)) := by
    rw [← pow_add]
    congr 1
    omega
  refine ⟨l, Nat.mul_pos (by omega) (pow_pos (by decide) _), ?_, ?_⟩
  · rw [hpow]
    exact Nat.mul_lt_mul_of_pos_right hp (pow_pos (by decide) _)
  · have hpowq : (2 : ℚ) ^ b = (2 : ℚ) ^ (j + 1) * (2 : ℚ) ^ (b - (j + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    have hl : (l : ℚ) = (2 * (p : ℚ) + 1) * (2 : ℚ) ^ (b - (j + 1)) := by
      simp [l]
    have hfrac : (2 : ℚ) ^ j * ((l : ℚ) / (2 : ℚ) ^ b) = (p : ℚ) + 1 / 2 := by
      rw [hpowq, hl, pow_succ]
      field_simp

    have hd := binary_decomposition j q
    change (2 : ℚ) ^ j * q = (p : ℚ) + binaryRemainder j q at hd
    rw [mul_sub, hfrac]
    linarith

/-- Interior-grid clearance amplifies to a threshold margin at every extraction step. -/
theorem binaryRemainder_grid_clearance (b : ℕ) (q β : ℚ)
    (hgrid : ∀ l : ℕ, 0 < l → l < 2 ^ b → β < |q - (l : ℚ) / (2 : ℚ) ^ b|) :
    ∀ j < b, (2 : ℚ) ^ j * β < |binaryRemainder j q - 1 / 2| := by
  intro j hj
  obtain ⟨l, hl0, hlb, he⟩ := binaryThreshold_grid_witness b j q hj
  rw [he, abs_mul, abs_of_pos (pow_pos (by norm_num) j)]
  exact mul_lt_mul_of_pos_left (hgrid l hl0 hlb) (pow_pos (by norm_num) j)

/-- A common clearance budget preserves all extracted digits along a clipped trajectory. -/
theorem binaryThreshold_clipped_trajectory_stable_of_grid_clearance
    (q : ℚ) (y : ℕ → ℚ) (ε η β : ℚ) (b : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hbudget : ε + η ≤ β) (hinit : |y 0 - q| ≤ ε)
    (hstep : ∀ j < b, |y (j + 1) -
      max 0 (min 1 (2 * y j - if binaryThreshold (y j) then 1 else 0))| ≤ η)
    (hgrid : ∀ l : ℕ, 0 < l → l < 2 ^ b → β < |q - (l : ℚ) / (2 : ℚ) ^ b|) :
    ∀ j < b, binaryThreshold (y j) = binaryThreshold (binaryRemainder j q) := by
  apply binaryThreshold_clipped_trajectory_stable q y ε η b hq hq1 hε hη hinit hstep
  intro j hj
  have hm := mul_le_mul_of_nonneg_left hbudget (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) j)
  have he : (2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * η ≤ (2 : ℚ) ^ j * β := by
    nlinarith
  exact he.trans_lt (binaryRemainder_grid_clearance b q β hgrid j hj)

end GameTheory.Math
