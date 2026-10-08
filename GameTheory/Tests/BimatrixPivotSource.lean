import GameTheory.Finite.BimatrixPivotSource
import Mathlib.Data.Fin.VecNotation

/-! A fully degenerate rectangular game tests symbolic tie breaking and a
strictly feasible successor row with a zero constant coefficient. -/

namespace GameTheory.Tests.BimatrixPivotSource
open GameTheory.Finite GameTheory.Math GameTheory.Math.PerturbedDictionary
private def allOnes : Fin 1 → Fin 2 → ℤ := fun _ _ => 1
private def c : Fin 3 → ℚ := bimatrixEnteringColumn allOnes allOnes (.inl 0)
private theorem c_eq : c = ![0, 1, 1] := by
  funext i
  fin_cases i <;> decide
example : c 1 = c 2 ∧ c 1 = 1 := by rw [c_eq]; decide
private theorem last_leaves : IsLeavingRow
    (dictionaryCoefficients (1 : Matrix (Fin 3) (Fin 3) ℚ) (fun _ => 1)) c 2 := by
  constructor
  · rw [c_eq]; norm_num
  · intro i hi
    rw [c_eq] at hi ⊢
    fin_cases i
    · norm_num at hi
    · apply le_of_lt
      refine ⟨2, ?_, ?_⟩
      · intro j hj
        fin_cases j <;>
          (simp_all [dictionaryCoefficients, Matrix.one_apply, Fin.cons]; try rfl)
      · change dictionaryCoefficients (1 : Matrix (Fin 3) (Fin 3) ℚ)
            (fun _ => 1) 2 2 / 1 <
          dictionaryCoefficients (1 : Matrix (Fin 3) (Fin 3) ℚ) (fun _ => 1) 1 2 / 1
        change (1 : Matrix (Fin 3) (Fin 3) ℚ)⁻¹ 2 1 / 1 <
          (1 : Matrix (Fin 3) (Fin 3) ℚ)⁻¹ 1 1 / 1
        norm_num [Matrix.one_apply]
    · exact le_rfl
example : ((1 : Matrix (Fin 3) (Fin 3) ℚ).updateCol 2 c)⁻¹.mulVec
    (fun _ => 1) = ![1, 0, 1] := by
  rw [updated_inverse_mulVec _ _ _ _ (by simp) (by rw [inv_one, Matrix.one_mulVec, c_eq]; norm_num),
    inv_one, Matrix.one_mulVec, Matrix.one_mulVec, c_eq]
  funext i
  fin_cases i <;> norm_num [pivotVector]
example : dictionaryCoefficients
      ((1 : Matrix (Fin 3) (Fin 3) ℚ).updateCol 2 c) (fun _ => 1) 1 0 = 0 ∧
    0 < toLex (dictionaryCoefficients
      ((1 : Matrix (Fin 3) (Fin 3) ℚ).updateCol 2 c) (fun _ => 1) 1) := by
  constructor
  · rw [coefficient_zero, updated_inverse_mulVec _ _ _ _ (by simp)
      (by rw [inv_one, Matrix.one_mulVec, c_eq]; norm_num),
      inv_one, Matrix.one_mulVec, Matrix.one_mulVec, c_eq]
    norm_num [pivotVector]
  · exact (bimatrixSource_successor_feasible allOnes allOnes (.inl 0) 2 last_leaves).2 1
end GameTheory.Tests.BimatrixPivotSource
