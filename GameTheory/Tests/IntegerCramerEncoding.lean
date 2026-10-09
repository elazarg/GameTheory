import GameTheory.Math.IntegerCramerEncoding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! One determinant denominator avoids multiplying separately reduced denominators. -/

namespace GameTheory.Tests.IntegerCramerEncoding

open GameTheory.Math.IntegerCramerEncoding

private def signedBasis : Matrix (Fin 2) (Fin 2) ℤ := !![-2, -1; 1, 4]
private def rhs : Fin 2 → ℤ := ![-1, 1]

private theorem determinant : signedBasis.det ≠ 0 := by
  norm_num [signedBasis, Matrix.det_fin_two]

example : denominator signedBasis = 7 ∧ numerator signedBasis rhs 0 = 3 ∧
    numerator signedBasis rhs 1 = 1 := by
  have hs : Int.sign (7 : ℤ) = 1 := rfl
  norm_num [denominator, numerator, signedBasis, rhs, Matrix.det_fin_two,
    Matrix.updateCol_apply, hs]

example (i : Fin 2) :
    (numerator signedBasis rhs i : ℚ) / denominator signedBasis =
      (signedBasis.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (rhs j : ℚ)) i := by
  apply decode signedBasis rhs determinant
  intro j
  rw [GameTheory.Math.IntegerBasisBounds.inv_mulVec_eq signedBasis rhs determinant j]
  fin_cases j <;> norm_num [signedBasis, rhs, Matrix.det_fin_two, Matrix.updateCol_apply]

-- Both separately reduced coordinate denominators are seven, whose product is forty-nine.
example : (((signedBasis.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec
      (fun j => (rhs j : ℚ)) 0).den *
    ((signedBasis.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec
      (fun j => (rhs j : ℚ)) 1).den) = 49 := by
  rw [GameTheory.Math.IntegerBasisBounds.inv_mulVec_eq signedBasis rhs determinant 0,
    GameTheory.Math.IntegerBasisBounds.inv_mulVec_eq signedBasis rhs determinant 1]
  norm_num [signedBasis, rhs, Matrix.det_fin_two, Matrix.updateCol_apply]

example (i : Fin 2) : numerator signedBasis rhs i <
    2 ^ GameTheory.Math.IntegerBasisBounds.width 2 2 := by
  apply numerator_lt signedBasis rhs 2 _ _
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [signedBasis]
  · intro i
    fin_cases i <;> norm_num [rhs]

example (M : Matrix (Fin 0) (Fin 0) ℤ) : denominator M = 1 := by
  simp [denominator]

-- Singular systems do not provide a positive determinant denominator.
example : denominator (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) = 0 := by
  norm_num [denominator, Matrix.det_fin_two]

-- Singular systems still produce bounded natural fields before feasibility is checked.
example (i : Fin 2) : numerator !![(1 : ℤ), 2; 2, 4] ![-1, 1] i <
    2 ^ GameTheory.Math.IntegerBasisBounds.width 2 2 := by
  apply numerator_lt _ _ 2
  · decide +kernel
  · decide +kernel

-- Natural numerators require nonnegative solution coordinates for decoding.
example : numerator (1 : Matrix (Fin 1) (Fin 1) ℤ) ![-1] 0 = 0 := by
  norm_num [numerator, Matrix.det_unique, Matrix.updateCol_apply]

end GameTheory.Tests.IntegerCramerEncoding
