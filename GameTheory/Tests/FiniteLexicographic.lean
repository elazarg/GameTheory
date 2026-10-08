import GameTheory.Math.FiniteLexicographic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! Controls for lexicographic perturbation coefficients. -/

namespace GameTheory.Tests.FiniteLexicographic

open GameTheory.Math.FiniteLexicographic

private theorem tieBreak :
    toLex (![1, 0, 1] : Fin 3 → ℚ) < toLex ![1, 1, 0] := by
  refine ⟨1, ?_, ?_⟩
  · intro j hj
    fin_cases j <;> first | rfl | simp_all
  · change (0 : ℚ) < 1
    norm_num

-- A later coefficient resolves equality of the constant terms.
example : toLex (![1, 0, 1] : Fin 3 → ℚ) < toLex ![1, 1, 0] := tieBreak

-- Strict lexicographic positivity does not imply a positive constant term.
example : 0 < toLex (![0, 1] : Fin 2 → ℚ) := by
  refine ⟨1, ?_, ?_⟩
  · intro j hj
    fin_cases j <;> first | rfl | simp_all
  · change (0 : ℚ) < 1
    norm_num

example : (![0, 1] : Fin 2 → ℚ) 0 = 0 := rfl

example : toLex (fun i => (3 : ℚ) * (![1, 0, 1] : Fin 3 → ℚ) i) <
    toLex (fun i => (3 : ℚ) * (![1, 1, 0] : Fin 3 → ℚ) i) :=
  (mul_lt_mul_iff (by norm_num : (0 : ℚ) < 3)).mpr tieBreak

example : toLex (fun i => (![1, 0, 1] : Fin 3 → ℚ) i / 3) <
    toLex (fun i => (![1, 1, 0] : Fin 3 → ℚ) i / 3) :=
  (div_lt_div_iff (by norm_num : (0 : ℚ) < 3)).mpr tieBreak

-- A negative earliest coefficient cannot be repaired by later positive ones.
example : ¬ 0 ≤ toLex (![-1, 100] : Fin 2 → ℚ) := by
  intro h
  have := constant_nonneg h
  norm_num at this

-- Nonnegative scaling includes the zero scalar.
example : 0 ≤ toLex (fun i => (0 : ℚ) * (![0, 1] : Fin 2 → ℚ) i) := by
  have h : 0 < toLex (![0, 1] : Fin 2 → ℚ) := by
    refine ⟨1, ?_, ?_⟩
    · intro j hj
      fin_cases j <;> first | rfl | simp_all
    · change (0 : ℚ) < 1
      norm_num
  exact mul_nonneg le_rfl h.le

end GameTheory.Tests.FiniteLexicographic
