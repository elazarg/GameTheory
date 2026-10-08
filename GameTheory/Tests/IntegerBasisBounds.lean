import GameTheory.Math.IntegerBasisBounds
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Signed determinants and reduced rational solutions satisfy the advertised binary width. -/

namespace GameTheory.Tests.IntegerBasisBounds

open GameTheory.Math.IntegerBasisBounds

private def triangular : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 0, -4]
private def rhs : Fin 2 → ℤ := ![1, 2]

private theorem determinant : triangular.det ≠ 0 := by
  norm_num [triangular, Matrix.det_fin_two]

example : (triangular.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun i => (rhs i : ℚ)) 0 = 3 / 4 := by
  rw [inv_mulVec_eq triangular rhs determinant 0]
  norm_num [triangular, rhs, Matrix.det_fin_two, Matrix.updateCol_apply]

example : ((triangular.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec
    (fun i => (rhs i : ℚ)) 1).num = -1 ∧
    ((triangular.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec
    (fun i => (rhs i : ℚ)) 1).den = 2 := by
  rw [inv_mulVec_eq triangular rhs determinant 1]
  norm_num [triangular, rhs, Matrix.det_fin_two, Matrix.updateCol_apply]

example (i : Fin 2) :
    ((triangular.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (rhs j : ℚ)) i).num.natAbs <
      2 ^ width 2 2 ∧
    ((triangular.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (rhs j : ℚ)) i).den <
      2 ^ width 2 2 := by
  apply inv_mulVec_bounds triangular rhs 2 _ _ determinant
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [triangular]
  · intro i
    fin_cases i <;> norm_num [rhs]

-- The empty determinant is one, and the width still bounds it strictly.
example (M : Matrix (Fin 0) (Fin 0) ℤ) (h : ℕ) : M.det.natAbs < 2 ^ width 0 h := by
  apply determinant_natAbs_lt M h
  intro i
  exact Fin.elim0 i

example : width 0 0 = 1 := rfl

-- Singular matrices cannot meet the premise of the inverse-coordinate theorem.
example : ¬ (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  norm_num [Matrix.det_fin_two]

end GameTheory.Tests.IntegerBasisBounds
