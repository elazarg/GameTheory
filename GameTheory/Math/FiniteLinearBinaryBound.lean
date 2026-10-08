import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-! Polynomial binary widths for bounded integer linear certificates.

The width depends on the bit bound of the coefficients, rather than on their
magnitude, so coefficients encoded in binary still give polynomial witnesses.
-/

namespace GameTheory.Math

/-- A common binary width for a denominator and all numerators of a finite
nonnegative linear certificate. -/
def linearCertificateWidth (variableCount constraintCount coefficientBits : ℕ) : ℕ :=
  variableCount * (variableCount + constraintCount + 2 * coefficientBits + 3) + 1

/-- The factorial determinant bound has polynomial binary width when the
coefficient bound has at most the advertised number of bits. -/
theorem factorial_mul_pow_lt_two_pow_of_le_two_pow (n r H h : ℕ)
    (hH : H ≤ 2 ^ h) :
    n.factorial * ((r + 1) * (H + 1) ^ 2) ^ n <
      2 ^ linearCertificateWidth n r h := by
  have hn : n.factorial ≤ (2 ^ n) ^ n :=
    n.factorial_le_pow.trans (Nat.pow_le_pow_left n.lt_two_pow_self.le n)
  have hr : r + 1 ≤ 2 ^ (r + 1) := (r + 1).lt_two_pow_self.le
  have hH' : H + 1 ≤ 2 ^ (h + 1) := by
    have hp : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by decide)
    rw [pow_succ]
    omega
  have hbase := Nat.mul_le_mul hr (Nat.pow_le_pow_left hH' 2)
  have hbound := Nat.mul_le_mul hn (Nat.pow_le_pow_left hbase n)
  have heq : (2 ^ n) ^ n * (2 ^ (r + 1) * (2 ^ (h + 1)) ^ 2) ^ n =
      2 ^ (n * (n + r + 2 * h + 3)) := by
    rw [← mul_pow, ← pow_mul, ← pow_add, ← pow_add, ← pow_mul]
    congr 1
    ring
  rw [heq] at hbound
  exact hbound.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

end GameTheory.Math
