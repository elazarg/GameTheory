import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Fin.Basic

/-! Finite coefficient vectors with Mathlib's lexicographic order.

Positive scalar multiplication and division preserve the first differing
coefficient. These facts support symbolic perturbations without introducing
an ordered field of infinitesimals.
-/

namespace GameTheory.Math.FiniteLexicographic

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : ℕ} {x y : Fin n → K} {a : K}

/-- Positive coefficientwise multiplication preserves strict lexicographic order. -/
theorem mul_lt_mul_iff (ha : 0 < a) :
    toLex (fun i => a * x i) < toLex (fun i => a * y i) ↔ toLex x < toLex y := by
  constructor
  · rintro ⟨i, hi, hlt⟩
    exact ⟨i, fun j hj => mul_left_cancel₀ (ne_of_gt ha) (hi j hj),
      (mul_lt_mul_iff_right₀ ha).mp hlt⟩
  · rintro ⟨i, hi, hlt⟩
    exact ⟨i, fun j hj => congrArg (a * ·) (hi j hj),
      (mul_lt_mul_iff_right₀ ha).mpr hlt⟩

/-- Positive coefficientwise multiplication preserves lexicographic order. -/
theorem mul_le_mul_iff (ha : 0 < a) :
    toLex (fun i => a * x i) ≤ toLex (fun i => a * y i) ↔ toLex x ≤ toLex y := by
  constructor
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact ((mul_lt_mul_iff ha).mp h).le
    · have heq : x = y := funext fun i =>
        mul_left_cancel₀ (ne_of_gt ha)
          (congrArg (fun z : Lex (Fin n → K) => ofLex z i) h)
      exact congrArg toLex heq |>.le
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact ((mul_lt_mul_iff ha).mpr h).le
    · exact congrArg (fun z => toLex (fun i => a * z i)) (toLex_inj.mp h) |>.le

/-- Positive coefficientwise division preserves strict lexicographic order. -/
theorem div_lt_div_iff (ha : 0 < a) :
    toLex (fun i => x i / a) < toLex (fun i => y i / a) ↔ toLex x < toLex y := by
  simpa only [div_eq_mul_inv, mul_comm] using
    (mul_lt_mul_iff (x := x) (y := y) (inv_pos.mpr ha))

/-- Positive coefficientwise division preserves lexicographic order. -/
theorem div_le_div_iff (ha : 0 < a) :
    toLex (fun i => x i / a) ≤ toLex (fun i => y i / a) ↔ toLex x ≤ toLex y := by
  simpa only [div_eq_mul_inv, mul_comm] using
    (mul_le_mul_iff (x := x) (y := y) (inv_pos.mpr ha))

/-- Nonnegative scaling preserves lexicographic nonnegativity. -/
theorem mul_nonneg (ha : 0 ≤ a) (hx : 0 ≤ toLex x) :
    0 ≤ toLex (fun i => a * x i) := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · change toLex (fun _ : Fin n => (0 : K)) ≤ toLex (fun i => 0 * x i)
    simp only [zero_mul]
    exact le_rfl
  · have h := (mul_le_mul_iff (x := fun _ => 0) (y := x) ha).mpr hx
    simp only [mul_zero] at h
    exact h

/-- Positive scaling preserves lexicographic positivity. -/
theorem mul_pos (ha : 0 < a) (hx : 0 < toLex x) :
    0 < toLex (fun i => a * x i) := by
  have h := (mul_lt_mul_iff (x := fun _ => 0) (y := x) ha).mpr hx
  simp only [mul_zero] at h
  exact h

omit [IsStrictOrderedRing K] in
/-- A nonnegative lexicographic coefficient vector has nonnegative constant term. -/
theorem constant_nonneg {x : Fin (n + 1) → K} (hx : 0 ≤ toLex x) : 0 ≤ x 0 := by
  exact Pi.apply_le_of_toLex hx (fun j hj => (Fin.not_lt_zero j hj).elim)

end GameTheory.Math.FiniteLexicographic
