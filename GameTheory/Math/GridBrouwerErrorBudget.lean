import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Dyadic error budgets for grid computations

Exponential precision with a linear exponent dominates grid scaling, binary extraction and
feedback amplification. The reward schedule is integer-valued; its normalized error obeys the
same dyadic bound used by the numerical correctness estimates.
-/

namespace GameTheory.Math

private theorem dyadic_scaled_error {δ : ℚ} {Q a : ℕ}
    (hδ : δ ≤ 1 / (2 : ℚ) ^ Q) (ha : a + 30 ≤ Q) :
    δ * (2 : ℚ) ^ a ≤ 1 / (2 : ℚ) ^ 30 := by
  have hp : (2 : ℚ) ^ (a + 30) ≤ 2 ^ Q := pow_le_pow_right₀ (by norm_num) ha
  have hd := hδ.trans (one_div_le_one_div_of_le (by positivity) hp)
  have hm := mul_le_mul_of_nonneg_right hd (by positivity : 0 ≤ (2 : ℚ) ^ a)
  rw [pow_add] at hm
  have he : (1 / ((2 : ℚ) ^ a * 2 ^ 30)) * 2 ^ a = 1 / (2 : ℚ) ^ 30 := by
    field_simp
  exact hm.trans_eq he

/-- A dyadic precision budget controls extraction, color evaluation and projected feedback. -/
theorem gridBrouwer_dyadic_error_budget (b k : ℕ) (hk : 1 ≤ k) (δ : ℚ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (2 : ℚ) ^ (100 * (b + k + 10))) :
    let T := 5 * (b + 10)
    let α : ℚ := 1 / 2 ^ T
    let β := α / 4
    let N : ℚ := 2 ^ b
    let L := 2 * N * (N + 1) ^ 2
    let ρ := 100 * δ
    let θ := α / 3
    50 * δ ≤ β ∧ 2000 * N * δ ≤ 1 / 1024 ∧ ρ / θ + L * ρ ≤ 1 / 512 := by
  dsimp only
  let T := 5 * (b + 10)
  let N : ℚ := 2 ^ b
  have hT := dyadic_scaled_error hδ (show T + 30 ≤ 100 * (b + k + 10) by
    dsimp [T]; omega)
  have hb := dyadic_scaled_error hδ (show b + 30 ≤ 100 * (b + k + 10) by omega)
  have h3b := dyadic_scaled_error hδ (show 3 * b + 30 ≤ 100 * (b + k + 10) by omega)
  have hN : 1 ≤ N := one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hpT : 0 < (2 : ℚ) ^ T := by positivity
  have hsq : (N + 1) ^ 2 ≤ 4 * N ^ 2 := by nlinarith only [hN]
  have hL : 2 * N * (N + 1) ^ 2 * (100 * δ) ≤ 800 * N ^ 3 * δ := by
    have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * N * (100 * δ))
    nlinarith only [hh]
  have h3pow : (2 : ℚ) ^ (3 * b) = N ^ 3 := by
    dsimp [N]; rw [Nat.mul_comm 3 b, pow_mul]
  rw [h3pow] at h3b
  have hρ : 100 * δ / (1 / (2 : ℚ) ^ T / 3) = 300 * δ * 2 ^ T := by
    field_simp
    ring
  constructor
  · apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 4)).mpr
    apply (le_div_iff₀ hpT).mpr
    norm_num at hT
    nlinarith only [hT]
  constructor
  · change 2000 * N * δ ≤ _
    change δ * N ≤ _ at hb
    norm_num at hb
    nlinarith only [hb]
  · change 100 * δ / (1 / (2 : ℚ) ^ T / 3) +
      2 * N * (N + 1) ^ 2 * (100 * δ) ≤ _
    rw [hρ]
    norm_num at hT h3b
    nlinarith only [hT, h3b, hL]

private theorem bimatrix_large_reward_error_bound (k Q : ℕ) (hk : 1 ≤ k) :
    let H : ℚ := ((k : ℚ) * (100 * k + 2 * k) + 1) * 2 ^ Q
    0 ≤ (k : ℚ) * (102 * k) / H ∧
      (k : ℚ) * (102 * k) / H ≤ 1 / 2 ^ Q := by
  dsimp only
  have hkpos : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp : 0 < (2 : ℚ) ^ Q := by positivity
  have hH : 0 < ((k : ℚ) * (100 * k + 2 * k) + 1) * 2 ^ Q := by positivity
  constructor
  · positivity
  · apply (div_le_div_iff₀ hH hp).mpr
    nlinarith only [hp]

/-- The integer reward schedule bounds the actual normalized error by its dyadic budget. -/
theorem bimatrix_integer_reward_error_bound (k Q : ℕ) (hk : 1 ≤ k) :
    let H : ℤ := ((k : ℤ) * (100 * k + 2 * k) + 1) * 2 ^ Q
    0 ≤ (k : ℚ) * (102 * k) / (H : ℚ) ∧
      (k : ℚ) * (102 * k) / (H : ℚ) ≤ 1 / 2 ^ Q := by
  simpa only [Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_natCast,
    Int.cast_ofNat, Int.cast_one] using bimatrix_large_reward_error_bound k Q hk

end GameTheory.Math
