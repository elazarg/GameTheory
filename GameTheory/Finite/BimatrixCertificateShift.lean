import GameTheory.Finite.BimatrixCertificate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Adding constants to either player's payoff table preserves exact Nash
certificates. Positive payoff tables have positive certified utilities, including
when best responses are tied or the certificate has zero probability entries. -/

namespace GameTheory.Finite

open scoped BigOperators

namespace BimatrixCertificate

/-- Adjust utility numerators when constants are added to the two payoff tables. -/
def shiftPayoffs {m n : ℕ} (c : BimatrixCertificate m n) (a b : ℤ) :
    BimatrixCertificate m n :=
  { c with
    rowUtilityNumerator := c.rowUtilityNumerator + a * c.colDenominator
    colUtilityNumerator := c.colUtilityNumerator + b * c.rowDenominator }

@[simp] theorem shiftPayoffs_neg_cancel {m n : ℕ} (c : BimatrixCertificate m n)
    (a b : ℤ) : (c.shiftPayoffs a b).shiftPayoffs (-a) (-b) = c := by
  cases c
  simp [shiftPayoffs, neg_mul]

theorem rowScore_shiftPayoffs {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (c : BimatrixCertificate m n) (a b : ℤ)
    (hc : (∑ j, c.colWeights j) = c.colDenominator) (i : Fin m) :
    rowScore (fun i j => A i j + a) (c.shiftPayoffs a b) i =
      rowScore A c i + a * c.colDenominator := by
  simp only [rowScore, shiftPayoffs, add_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [← Nat.cast_sum, hc]

theorem colScore_shiftPayoffs {m n : ℕ} (B : Fin m → Fin n → ℤ)
    (c : BimatrixCertificate m n) (a b : ℤ)
    (hc : (∑ i, c.rowWeights i) = c.rowDenominator) (j : Fin n) :
    colScore (fun i j => B i j + b) (c.shiftPayoffs a b) j =
      colScore B c j + b * c.rowDenominator := by
  simp only [colScore, shiftPayoffs, add_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [← Nat.cast_sum, hc]

/-- Additive shifts preserve normalization and every supported best response. -/
theorem valid_shiftPayoffs_iff {m n : ℕ} (A B : Fin m → Fin n → ℤ)
    (c : BimatrixCertificate m n) (a b : ℤ) :
    (c.shiftPayoffs a b).Valid (fun i j => A i j + a) (fun i j => B i j + b) ↔
      c.Valid A B := by
  constructor
  · rintro ⟨hr, hc, hs, ht, hA, hB⟩
    refine ⟨hr, hc, hs, ht, ?_, ?_⟩
    · intro i
      have hi := hA i
      rw [rowScore_shiftPayoffs A c a b ht i] at hi
      simpa only [shiftPayoffs, add_le_add_iff_right, add_left_inj] using hi
    · intro j
      have hj := hB j
      rw [colScore_shiftPayoffs B c a b hs j] at hj
      simpa only [shiftPayoffs, add_le_add_iff_right, add_left_inj] using hj
  · rintro ⟨hr, hc, hs, ht, hA, hB⟩
    refine ⟨hr, hc, hs, ht, ?_, ?_⟩
    · intro i
      rw [rowScore_shiftPayoffs A c a b ht i]
      simpa only [shiftPayoffs, add_le_add_iff_right, add_left_inj] using hA i
    · intro j
      rw [colScore_shiftPayoffs B c a b hs j]
      simpa only [shiftPayoffs, add_le_add_iff_right, add_left_inj] using hB j

theorem valid_unshiftPayoffs_iff {m n : ℕ} (A B : Fin m → Fin n → ℤ)
    (c : BimatrixCertificate m n) (a b : ℤ) :
    (c.shiftPayoffs (-a) (-b)).Valid A B ↔
      c.Valid (fun i j => A i j + a) (fun i j => B i j + b) := by
  simpa only [add_neg_cancel_right] using
    (valid_shiftPayoffs_iff (fun i j => A i j + a) (fun i j => B i j + b)
      c (-a) (-b))

theorem positive_rowUtilityNumerator {m n : ℕ} (A B : Fin m → Fin n → ℤ)
    (c : BimatrixCertificate m n) (hc : c.Valid A B) (hA : ∀ i j, 0 < A i j) :
    0 < c.rowUtilityNumerator := by
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show (∑ i, c.rowWeights i) ≠ 0 by rw [hc.2.2.1]; exact Nat.ne_of_gt hc.1)
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show (∑ j, c.colWeights j) ≠ 0 by rw [hc.2.2.2.1]; exact Nat.ne_of_gt hc.2.1)
  have hs : 0 < rowScore A c i := by
    apply Finset.sum_pos' (fun k _ => mul_nonneg (le_of_lt (hA i k)) (by positivity))
    exact ⟨j, Finset.mem_univ j, mul_pos (hA i j) (by exact_mod_cast Nat.pos_of_ne_zero hj)⟩
  exact hs.trans_le (hc.2.2.2.2.1 i).1

theorem positive_colUtilityNumerator {m n : ℕ} (A B : Fin m → Fin n → ℤ)
    (c : BimatrixCertificate m n) (hc : c.Valid A B) (hB : ∀ i j, 0 < B i j) :
    0 < c.colUtilityNumerator := by
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show (∑ i, c.rowWeights i) ≠ 0 by rw [hc.2.2.1]; exact Nat.ne_of_gt hc.1)
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show (∑ j, c.colWeights j) ≠ 0 by rw [hc.2.2.2.1]; exact Nat.ne_of_gt hc.2.1)
  have hs : 0 < colScore B c j := by
    apply Finset.sum_pos' (fun k _ => mul_nonneg (le_of_lt (hB k j)) (by positivity))
    exact ⟨i, Finset.mem_univ i, mul_pos (hB i j) (by exact_mod_cast Nat.pos_of_ne_zero hi)⟩
  exact hs.trans_le (hc.2.2.2.2.2 j).1

end BimatrixCertificate

/-- A binary magnitude bound supplies a strictly positive integer payoff shift. -/
theorem payoff_add_pow_positive (z : ℤ) (h : ℕ) (hz : z.natAbs ≤ 2 ^ h) :
    0 < z + ((2 : ℤ) ^ h + 1) := by
  have ha : |z| ≤ (2 : ℤ) ^ h := by
    simpa only [Int.natCast_natAbs, Nat.cast_pow, Nat.cast_ofNat] using
      (show (z.natAbs : ℤ) ≤ ((2 ^ h : ℕ) : ℤ) by exact_mod_cast hz)
  have := neg_abs_le z
  omega

/-- The same positive shift costs at most two extra bits of payoff magnitude. -/
theorem payoff_add_pow_bound (z : ℤ) (h : ℕ) (hz : z.natAbs ≤ 2 ^ h) :
    (z + ((2 : ℤ) ^ h + 1)).natAbs < 2 ^ (h + 2) := by
  have ha : |z| ≤ (2 : ℤ) ^ h := by
    simpa only [Int.natCast_natAbs, Nat.cast_pow, Nat.cast_ofNat] using
      (show (z.natAbs : ℤ) ≤ ((2 ^ h : ℕ) : ℤ) by exact_mod_cast hz)
  have hp := payoff_add_pow_positive z h hz
  have hpow : (1 : ℤ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
  have hle := le_abs_self z
  have : z + ((2 : ℤ) ^ h + 1) < (2 : ℤ) ^ (h + 2) := by
    rw [pow_add]
    norm_num
    omega
  have hab : |z + ((2 : ℤ) ^ h + 1)| < (2 : ℤ) ^ (h + 2) := by
    rwa [abs_of_pos hp]
  have hab' : ((z + ((2 : ℤ) ^ h + 1)).natAbs : ℤ) < ((2 ^ (h + 2) : ℕ) : ℤ) := by
    simpa only [Int.natCast_natAbs, Nat.cast_pow, Nat.cast_ofNat] using hab
  exact_mod_cast hab'

end GameTheory.Finite
