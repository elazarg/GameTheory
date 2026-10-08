import GameTheory.Math.NonnegativeDictionary
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exit existence needs a positive coordinate, not a nonnegative entering vector. -/

namespace GameTheory.Tests.NonnegativeDictionary

open GameTheory.Math

private def triangular : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]

example : ∃ i, 0 < triangular⁻¹.mulVec ![-1, 3] i := by
  apply exists_positive_inverse_mulVec triangular ![-1, 3]
  · norm_num [triangular, Matrix.det_fin_two]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [triangular]
  · exact ⟨1, by norm_num⟩

example : ∀ i, triangular.mulVec ![-2, -3] i ≤ 0 := by
  apply mulVec_nonpos_of_nonneg
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [triangular]
  · intro i
    fin_cases i <;> norm_num

-- Without a positive entering coordinate there need not be an eligible exit.
example : ¬ ∃ i, 0 < (1 : Matrix (Fin 2) (Fin 2) ℚ)⁻¹.mulVec ![0, -1] i := by
  rintro ⟨i, hi⟩
  fin_cases i <;> norm_num at hi

-- A negative basis entry can represent a positive vector by negative coordinates.
example : (!![-1] : Matrix (Fin 1) (Fin 1) ℚ).mulVec ![-1] = ![1] := by
  funext i
  fin_cases i
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_one]

end GameTheory.Tests.NonnegativeDictionary
