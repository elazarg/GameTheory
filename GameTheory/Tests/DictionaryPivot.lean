import GameTheory.Math.DictionaryPivot
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Column replacement controls include a negative pivot and its reverse. -/

namespace GameTheory.Tests.DictionaryPivot

open GameTheory.Math

private def triangular : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]
private def entering : Fin 2 → ℚ := ![2, 3]
private def direction : Fin 2 → ℚ := ![-1, 3]

example : (triangular.updateCol 0 entering).mulVec
    (pivotVector direction 0 ![3, 2]) = ![5, 2] := by
  have hc : triangular.mulVec direction = entering := by
    funext i
    fin_cases i <;> norm_num [triangular, direction, entering, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
  rw [updated_mulVec_pivotVector triangular entering direction ![3, 2] 0 hc
    (by norm_num [direction])]
  funext i
  fin_cases i <;> norm_num [triangular, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

example : pivotVector direction 0 ![3, 2] = ![-3, 11] := by
  funext i
  fin_cases i <;> norm_num [pivotVector, direction]

example : pivotVector (pivotVector direction 0 (Pi.single 0 1)) 0
    ![-3, 11] = ![3, 2] := by
  have hf : pivotVector direction 0 ![3, 2] = ![-3, 11] := by
    funext i
    fin_cases i <;> norm_num [pivotVector, direction]
  rw [← hf]
  exact pivotVector_reverse direction 0 ![3, 2] (by norm_num [direction])

-- The inverse-coordinate theorem covers the actual updated matrix.
example : ((1 : Matrix (Fin 2) (Fin 2) ℚ).updateCol 0 ![-2, 3])⁻¹.mulVec ![3, 2] =
    pivotVector ![-2, 3] 0 ![3, 2] := by
  simpa using updated_inverse_mulVec (1 : Matrix (Fin 2) (Fin 2) ℚ)
    ![-2, 3] 0 ![3, 2] (by simp) (by norm_num)

-- A zero entering coordinate cannot satisfy the invertible-pivot premise.
example : ¬ ((1 : Matrix (Fin 2) (Fin 2) ℚ)⁻¹.mulVec ![0, 3] 0 ≠ 0) := by
  simp

end GameTheory.Tests.DictionaryPivot
