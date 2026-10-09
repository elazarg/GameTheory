import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-! Strict Boolean threshold signals tolerate small scalar representation errors.
Clamping a Boolean scalar to a nonnegative weight preserves its error bound. -/

namespace GameTheory.Math
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The AND threshold has the strict sign of the conjunction. -/
theorem booleanThreshold_and (a b : Bool) (x y ε : F)
    (hx : |x - (if a then 1 else 0)| ≤ ε)
    (hy : |y - (if b then 1 else 0)| ≤ ε) (hε : ε < 1 / 4) :
    (0 < x + y - 3 / 2 ↔ (a && b) = true) ∧
      (x + y - 3 / 2 < 0 ↔ (a && b) = false) := by
  rw [abs_le] at hx hy
  cases a <;> cases b <;> simp_all only [
    Bool.and_false, Bool.and_true, Bool.false_eq_true, Bool.true_eq_false,
    ite_true, ite_false, sub_zero, iff_false, iff_true, not_lt] <;>
    constructor <;> linarith

/-- The OR threshold has the strict sign of the disjunction. -/
theorem booleanThreshold_or (a b : Bool) (x y ε : F)
    (hx : |x - (if a then 1 else 0)| ≤ ε)
    (hy : |y - (if b then 1 else 0)| ≤ ε) (hε : ε < 1 / 4) :
    (0 < x + y - 1 / 2 ↔ (a || b) = true) ∧
      (x + y - 1 / 2 < 0 ↔ (a || b) = false) := by
  rw [abs_le] at hx hy
  cases a <;> cases b <;> simp_all only [
    Bool.or_false, Bool.or_true, Bool.false_eq_true, Bool.true_eq_false,
    ite_true, ite_false, sub_zero, iff_false, iff_true, not_lt] <;>
    constructor <;> linarith

/-- The NOT threshold has the strict sign of the negated input. -/
theorem booleanThreshold_not (a : Bool) (x ε : F)
    (hx : |x - (if a then 1 else 0)| ≤ ε) (hε : ε < 1 / 4) :
    (0 < 1 / 2 - x ↔ (!a) = true) ∧ (1 / 2 - x < 0 ↔ (!a) = false) := by
  rw [abs_le] at hx
  cases a <;> simp_all only [Bool.not_false, Bool.not_true,
    Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, sub_zero,
    iff_false, iff_true, not_lt] <;> constructor <;> linarith

/-- Taking a minimum multiplies a Boolean indicator by its weight without amplifying error. -/
theorem booleanThreshold_min_weight (bit : Bool) (w z ε : F)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hz : |z - (if bit then 1 else 0)| ≤ ε) :
    |min w z - (if bit then w else 0)| ≤ ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hz
  rw [abs_le] at hz ⊢
  cases bit
  · simp only [Bool.false_eq_true, ite_false, sub_zero] at hz ⊢
    exact ⟨le_min (by linarith) hz.1, (min_le_right _ _).trans hz.2⟩
  · simp only [ite_true] at hz ⊢
    constructor
    · have hm : w - ε ≤ min w z := le_min (by linarith) (by linarith)
      linarith
    · have hm := min_le_left w z
      linarith

end GameTheory.Math
