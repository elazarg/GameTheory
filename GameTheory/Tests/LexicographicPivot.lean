import GameTheory.Math.LexicographicPivot
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Controls for tied symbolic ratios and competing reverse pivots. -/
namespace GameTheory.Tests.LexicographicPivot
open GameTheory.Math

private def C : Fin 2 → Fin 3 → ℚ := ![![1, 1, 0], ![1, 0, 1]]

private theorem positive : ∀ i, 0 < toLex (C i) := by
  intro i
  refine ⟨0, ?_, ?_⟩
  · intro j hj
    exact False.elim (not_lt_of_ge (Fin.zero_le j) hj)
  · fin_cases i <;> change (0 : ℚ) < 1 <;> norm_num

private theorem reverseControl : IsLeavingRow C (![1, -1] : Fin 2 → ℚ) 0 := by
  constructor
  · norm_num
  · intro i hi
    fin_cases i
    · exact le_rfl
    · norm_num at hi

-- A negative forward direction becomes a second eligible reverse row.
example : IsLeavingRow (pivotCoefficients C ![1, -1] 0)
    (pivotVector (![1, -1] : Fin 2 → ℚ) 0 (Pi.single 0 1)) 0 :=
  reverse_isLeavingRow _ _ _ positive reverseControl

example : ∀ i, 0 < pivotVector (![1, -1] : Fin 2 → ℚ) 0 (Pi.single 0 1) i := by
  intro i
  fin_cases i <;> norm_num [pivotVector, Pi.single_apply]

-- No positive direction means that the minimum-ratio rule has no leaving row.
example : ¬ ∃ l, IsLeavingRow C (![0, -1] : Fin 2 → ℚ) l := by
  rintro ⟨l, hl⟩
  have h := hl.1
  fin_cases l <;> norm_num at h

end GameTheory.Tests.LexicographicPivot
