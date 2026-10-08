import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.NatAbs

/-! Reducing an integer quotient cannot increase its numerator or denominator.

The denominator must be nonzero: the normalized denominator of zero is one,
whereas the absolute value of a zero input denominator is zero.
-/

namespace GameTheory.Math.RationalQuotientBounds

private theorem factor_abs_pos (a b : ℤ) (hb : b ≠ 0) :
    ∃ c : ℤ, 1 ≤ c.natAbs ∧ a = c * ((a : ℚ) / b).num ∧
      b = c * ((a : ℚ) / b).den := by
  obtain ⟨c, ha, hd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a hb
  have hc : c ≠ 0 := by
    intro h
    rw [h, zero_mul] at hd
    exact hb hd
  refine ⟨c, ?_, ha, hd⟩
  exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hc)

theorem num_natAbs_le (a b : ℤ) (hb : b ≠ 0) :
    (((a : ℚ) / b).num).natAbs ≤ a.natAbs := by
  obtain ⟨c, hc, ha, _⟩ := factor_abs_pos a b hb
  conv_rhs => rw [ha, Int.natAbs_mul]
  simpa only [one_mul] using Nat.mul_le_mul_right (((a : ℚ) / b).num.natAbs) hc

theorem den_le (a b : ℤ) (hb : b ≠ 0) :
    ((a : ℚ) / b).den ≤ b.natAbs := by
  obtain ⟨c, hc, _, hd⟩ := factor_abs_pos a b hb
  conv_rhs => rw [hd, Int.natAbs_mul, Int.natAbs_natCast]
  simpa only [one_mul] using Nat.mul_le_mul_right (((a : ℚ) / b).den) hc

end GameTheory.Math.RationalQuotientBounds
