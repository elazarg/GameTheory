import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FieldSimp

/-! Natural common-denominator encodings of finite nonnegative rational vectors.

The product of reduced denominators gives a computable encoding without choosing
an ordering of the coordinates. Uniform bounds on the reduced fractions yield
explicit bounds on both parts of the encoding.
-/

namespace GameTheory.Math.FiniteRationalEncoding

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- A positive common denominator, also for an empty vector. -/
def denominator (z : ι → ℚ) : ℕ := ∏ i, (z i).den

/-- Natural numerators for nonnegative coordinates in the common denominator. -/
def numerator (z : ι → ℚ) (i : ι) : ℕ :=
  (z i).num.toNat * (denominator z / (z i).den)

theorem denominator_pos (z : ι → ℚ) : 0 < denominator z := by
  exact CanonicallyOrderedAdd.prod_pos.mpr fun i _ => (z i).den_pos

theorem coordinate_den_dvd (z : ι → ℚ) (i : ι) : (z i).den ∣ denominator z :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- Decoding is exact when the vector has nonnegative coordinates. -/
theorem decode (z : ι → ℚ) (hz : ∀ i, 0 ≤ z i) (i : ι) :
    (numerator z i : ℚ) / (denominator z : ℚ) = z i := by
  have hnum : 0 ≤ (z i).num := Rat.num_nonneg.mpr (hz i)
  have hn : ((z i).num.toNat : ℚ) = ((z i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  have hd : (denominator z : ℚ) ≠ 0 := by
    exact_mod_cast (denominator_pos z).ne'
  rw [numerator, Nat.cast_mul, Nat.cast_div_charZero (coordinate_den_dvd z i), hn]
  calc
    ((z i).num : ℚ) * ((denominator z : ℚ) / ((z i).den : ℚ)) /
        (denominator z : ℚ) = ((z i).num : ℚ) / ((z i).den : ℚ) := by
      field_simp
    _ = z i := Rat.num_div_den (z i)

theorem denominator_le (z : ι → ℚ) (D : ℕ) (hD : ∀ i, (z i).den ≤ D) :
    denominator z ≤ D ^ Fintype.card ι := by
  exact Finset.prod_le_pow_card _ _ _ fun i _ => hD i

theorem numerator_le (z : ι → ℚ) (N D : ℕ)
    (hN : ∀ i, (z i).num.natAbs ≤ N) (hD : ∀ i, (z i).den ≤ D) (i : ι) :
    numerator z i ≤ N * D ^ Fintype.card ι := by
  have hn : (z i).num.toNat ≤ N := by
    have h : (z i).num.toNat ≤ (z i).num.natAbs := by
      cases (z i).num <;> simp
    exact h.trans (hN i)
  exact Nat.mul_le_mul hn ((Nat.div_le_self _ _).trans (denominator_le z D hD))

theorem denominator_le_two_pow (z : ι → ℚ) (h : ℕ)
    (hD : ∀ i, (z i).den ≤ 2 ^ h) :
    denominator z ≤ 2 ^ (h * Fintype.card ι) := by
  simpa only [pow_mul] using denominator_le z (2 ^ h) hD

theorem numerator_le_two_pow (z : ι → ℚ) (h : ℕ)
    (hN : ∀ i, (z i).num.natAbs ≤ 2 ^ h) (hD : ∀ i, (z i).den ≤ 2 ^ h) (i : ι) :
    numerator z i ≤ 2 ^ (h * (Fintype.card ι + 1)) := by
  simpa only [Nat.mul_add, Nat.mul_one, pow_add, pow_mul, Nat.mul_comm] using
    numerator_le z (2 ^ h) (2 ^ h) hN hD i

end GameTheory.Math.FiniteRationalEncoding
