import Mathlib.Order.PiLex
import Mathlib.Order.Fin.Basic

/-! # Executable finite lexicographic comparison

Scan coordinates in order, stopping at the first strict comparison or recursing
past equal coordinates. Only the supplied scalar order is used by the executable
comparison; correctness connects it to Mathlib's lexicographic order.
-/

namespace GameTheory.Math.FiniteLexicographicCompare

variable {K : Type*} [LinearOrder K] {k : ℕ}

/-- Finite lexicographic comparison, scanning the head before the tail. -/
def lexLT : {k : ℕ} → (Fin k → K) → (Fin k → K) → Bool
  | 0, _, _ => false
  | k + 1, x, y => if x 0 < y 0 then true else
      if x 0 = y 0 then lexLT (fun i : Fin k => x i.succ) (fun i => y i.succ) else false

@[simp] theorem lexLT_empty (x y : Fin 0 → K) : lexLT x y = false := rfl

theorem lexLT_succ (x y : Fin (k + 1) → K) : lexLT x y =
    if x 0 < y 0 then true else if x 0 = y 0 then
      lexLT (fun i : Fin k => x i.succ) (fun i => y i.succ) else false := rfl

private theorem lex_lt_head_tail (x y : Fin (k + 1) → K) :
    toLex x < toLex y ↔ x 0 < y 0 ∨
      x 0 = y 0 ∧ toLex (fun i : Fin k => x i.succ) < toLex (fun i => y i.succ) := by
  constructor
  · rintro ⟨i, hpre, hlt⟩
    cases i using Fin.cases with
    | zero => exact Or.inl hlt
    | succ i =>
      refine Or.inr ⟨hpre 0 (by exact Nat.zero_lt_succ i.val), i, ?_, hlt⟩
      intro j hj
      exact hpre j.succ (Fin.succ_lt_succ_iff.mpr hj)
  · rintro (hlt | ⟨he, i, hpre, hlt⟩)
    · exact ⟨0, fun j hj => (Fin.not_lt_zero j hj).elim, hlt⟩
    · refine ⟨i.succ, ?_, hlt⟩
      intro j hj
      cases j using Fin.cases with
      | zero => exact he
      | succ j => exact hpre j (Fin.succ_lt_succ_iff.mp hj)

/-- The finite scan decides strict lexicographic comparison. -/
theorem lexLT_eq_true (x y : Fin k → K) : lexLT x y = true ↔ toLex x < toLex y := by
  induction k with
  | zero =>
    constructor
    · intro h
      cases h
    · rintro ⟨i, _⟩
      exact Fin.elim0 i
  | succ k ih =>
    rw [lexLT_succ, lex_lt_head_tail]
    by_cases hlt : x 0 < y 0
    · simp only [hlt, ↓reduceIte, true_or]
    · by_cases he : x 0 = y 0
      · simp only [he, lt_self_iff_false, ↓reduceIte, false_or, true_and]
        exact ih _ _
      · simp only [hlt, he, ↓reduceIte, Bool.false_eq_true, false_and, or_self]

/-- A false comparison means the opposite weak lexicographic inequality. -/
theorem lexLT_eq_false (x y : Fin k → K) : lexLT x y = false ↔ toLex y ≤ toLex x := by
  rw [← Bool.not_eq_true, lexLT_eq_true]
  exact not_lt

end GameTheory.Math.FiniteLexicographicCompare
