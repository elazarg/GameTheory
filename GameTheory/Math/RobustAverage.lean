import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Finite averages remain close to a common signal when only a bounded number of samples
are exceptional. The weighted estimate counts good and exceptional samples separately. -/

namespace GameTheory.Math
open scoped BigOperators
variable {ι F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Good samples contribute their stated error; exceptional samples contribute at most two. -/
theorem robustAverage_weighted (s bad : Finset ι) (hs : 0 < s.card)
    (hbad : bad ⊆ s) (f : ι → F) (d ε : F)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hd : |d| ≤ 1)
    (hgood : ∀ i ∈ s, i ∉ bad → |f i - d| ≤ ε) :
    |(∑ i ∈ s, f i) / (s.card : F) - d| ≤
      (((s.card - bad.card : ℕ) : F) * ε + 2 * (bad.card : F)) / (s.card : F) := by
  classical
  have hcard : (0 : F) < s.card := Nat.cast_pos.mpr hs
  have hsum : ∑ i ∈ s, |f i - d| ≤
      ((s.card - bad.card : ℕ) : F) * ε + 2 * (bad.card : F) := by
    rw [← Finset.sum_sdiff hbad (f := fun i => |f i - d|)]
    have hg : ∑ i ∈ s \ bad, |f i - d| ≤ ((s \ bad).card : F) * ε := by
      calc
        _ ≤ ∑ _i ∈ s \ bad, ε := Finset.sum_le_sum fun i hi =>
          hgood i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2
        _ = _ := by simp
    have hb : ∑ i ∈ bad, |f i - d| ≤ 2 * (bad.card : F) := by
      calc
        _ ≤ ∑ _i ∈ bad, (2 : F) := Finset.sum_le_sum fun i hi =>
          by
          have hab := abs_sub_le (f i) 0 d
          simp only [sub_zero, zero_sub, abs_neg] at hab
          linarith [hf i (hbad hi)]
        _ = _ := by simp [mul_comm]
    rw [Finset.card_sdiff_of_subset hbad] at hg
    exact add_le_add hg hb
  have hid : (∑ i ∈ s, f i) / (s.card : F) - d =
      (∑ i ∈ s, (f i - d)) / (s.card : F) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [hid, abs_div, abs_of_pos hcard]
  exact div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans hsum) hcard.le

/-- An exceptional-count bound gives a robust estimate independent of the exact count. -/
theorem robustAverage_bound (s bad : Finset ι) (hs : 0 < s.card)
    (hbad : bad ⊆ s) (b : ℕ) (hb : bad.card ≤ b) (f : ι → F) (d ε : F)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hd : |d| ≤ 1) (hε : 0 ≤ ε)
    (hgood : ∀ i ∈ s, i ∉ bad → |f i - d| ≤ ε) :
    |(∑ i ∈ s, f i) / (s.card : F) - d| ≤ ε + 2 * (b : F) / (s.card : F) := by
  have hcard : (0 : F) < s.card := Nat.cast_pos.mpr hs
  have hcount : ((s.card - bad.card : ℕ) : F) ≤ (s.card : F) :=
    Nat.cast_le.mpr (Nat.sub_le _ _)
  have hbadcount : (bad.card : F) ≤ (b : F) := Nat.cast_le.mpr hb
  calc
    _ ≤ (((s.card - bad.card : ℕ) : F) * ε + 2 * (bad.card : F)) /
        (s.card : F) := robustAverage_weighted s bad hs hbad f d ε hf hd hgood
    _ ≤ ((s.card : F) * ε + 2 * (b : F)) / (s.card : F) :=
      div_le_div_of_nonneg_right
        (add_le_add (mul_le_mul_of_nonneg_right hcount hε)
          (mul_le_mul_of_nonneg_left hbadcount (by positivity))) hcard.le
    _ = _ := by field_simp

end GameTheory.Math
