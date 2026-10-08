import GameTheory.Math.DictionaryReindex
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! A noninvolutive permutation detects inverse-orientation mistakes in basis sorting. -/

namespace GameTheory.Tests.DictionaryReindex

open GameTheory.Math

private def cycle : Fin 3 ≃ Fin 3 := (Equiv.swap 0 1).trans (Equiv.swap 1 2)

example : ((1 : Matrix (Fin 3) (Fin 3) ℚ).submatrix (Equiv.refl _) cycle)⁻¹.mulVec
    ![4, 5, 6] = ![6, 4, 5] := by
  rw [inverse_mulVec_column_permutation]
  funext i
  fin_cases i <;> norm_num [cycle, Equiv.swap_apply_def]

-- Reordering the basis leaves the perturbation powers attached to equation indices.
example : PerturbedDictionary.dictionaryCoefficients
    ((1 : Matrix (Fin 3) (Fin 3) ℚ).submatrix (Equiv.refl _) cycle) ![4, 5, 6] 0 3 = 1 := by
  rw [dictionaryCoefficients_column_permutation]
  change PerturbedDictionary.dictionaryCoefficients (1 : Matrix (Fin 3) (Fin 3) ℚ)
    ![4, 5, 6] (cycle 0) (2 : Fin 3).succ = 1
  rw [PerturbedDictionary.coefficient_succ]
  norm_num [cycle, Equiv.swap_apply_def]

example : ((1 : Matrix (Fin 3) (Fin 3) ℚ).submatrix (Equiv.refl _) cycle).det ≠ 0 := by
  apply (determinant_column_permutation_ne_zero_iff _ cycle).mpr
  simp

-- Original leaving row 0 becomes new row 1 under this cycle.
example : IsLeavingRow (fun i => (![![1], ![2], ![3]] : Fin 3 → Fin 1 → ℚ) (cycle i))
    (fun _ => (1 : ℚ)) 1 := by
  have hc : cycle.symm 0 = 1 := by decide
  have h : IsLeavingRow (![![1], ![2], ![3]] : Fin 3 → Fin 1 → ℚ) (fun _ => 1) 0 := by
    refine ⟨by norm_num, ?_⟩
    intro i _
    fin_cases i
    · exact le_rfl
    · apply le_of_lt
      refine ⟨0, fun j hj => (Fin.not_lt_zero j hj).elim, ?_⟩
      norm_num
    · apply le_of_lt
      refine ⟨0, fun j hj => (Fin.not_lt_zero j hj).elim, ?_⟩
      norm_num
  simpa only [hc] using
    (isLeavingRow_permutation_iff (![![1], ![2], ![3]] : Fin 3 → Fin 1 → ℚ)
      (fun _ => 1) cycle 0).mpr h

example : pivotVector (fun i => (![2, -1, 3] : Fin 3 → ℚ) (cycle i)) 1
    (fun i => (![4, 5, 6] : Fin 3 → ℚ) (cycle i)) =
    fun i => pivotVector ![2, -1, 3] 0 ![4, 5, 6] (cycle i) := by
  have hc : cycle.symm 0 = 1 := by decide
  simpa only [hc] using pivotVector_permutation (![2, -1, 3] : Fin 3 → ℚ)
    ![4, 5, 6] cycle 0

end GameTheory.Tests.DictionaryReindex
