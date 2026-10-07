import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-! Polynomial binary widths for factorial coefficient bounds arising from
finite integer linear systems. -/

namespace GameTheory.Math

/-- A factorial coefficient bound fits below an exponential whose exponent is
polynomial in the number of variables, constraints, and coefficient bound. -/
theorem factorial_mul_pow_lt_two_pow (n r H : ℕ) :
    n.factorial * ((r + 1) * (H + 1) ^ 2) ^ n <
      2 ^ (n * (n + r + 2 * H + 3) + 1) := by
  have hn : n.factorial ≤ (2 ^ n) ^ n :=
    n.factorial_le_pow.trans (Nat.pow_le_pow_left n.lt_two_pow_self.le n)
  have hr : r + 1 ≤ 2 ^ (r + 1) := (r + 1).lt_two_pow_self.le
  have hH : (H + 1) ^ 2 ≤ (2 ^ (H + 1)) ^ 2 :=
    Nat.pow_le_pow_left (H + 1).lt_two_pow_self.le 2
  have hbase := Nat.mul_le_mul hr hH
  have hbound := Nat.mul_le_mul hn (Nat.pow_le_pow_left hbase n)
  have heq : (2 ^ n) ^ n * (2 ^ (r + 1) * (2 ^ (H + 1)) ^ 2) ^ n =
      2 ^ (n * (n + r + 2 * H + 3)) := by
    rw [← mul_pow, ← pow_mul, ← pow_add, ← pow_add, ← pow_mul]
    congr 1
    ring
  rw [heq] at hbound
  exact hbound.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

/-- The symmetric bimatrix feasibility dimensions give a quadratic bit width. -/
theorem bimatrix_factorial_bound_lt_two_pow (q : ℕ) :
    (2 * q + 2).factorial *
        (((3 * q + 2) + 1) * ((q + 2) + 1) ^ 2) ^ (2 * q + 2) <
      2 ^ (14 * q ^ 2 + 36 * q + 23) := by
  have h := factorial_mul_pow_lt_two_pow (2 * q + 2) (3 * q + 2) (q + 2)
  convert h using 1
  ring

/-- Replacing the table dimension by an input-length upper bound preserves the
quadratic certificate field width. -/
theorem bimatrix_width_mono {q L : ℕ} (h : q ≤ L) :
    14 * q ^ 2 + 36 * q + 23 ≤ 14 * L ^ 2 + 36 * L + 23 := by
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left 14 (Nat.pow_le_pow_left h 2))
      (Nat.mul_le_mul_left 36 h)) 23

end GameTheory.Math
