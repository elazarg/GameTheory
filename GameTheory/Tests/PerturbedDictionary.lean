import GameTheory.Math.PerturbedDictionary
import Mathlib.Data.Fin.VecNotation

/-! Symbolic perturbations separate constant-term ratio ties, including after
solving a nontrivial triangular basis system. -/

namespace GameTheory.Tests.PerturbedDictionary

open GameTheory.Math.PerturbedDictionary

private def identityBasis : Matrix (Fin 2) (Fin 2) ℚ := 1

-- Both unperturbed ratios are one.
example : dictionaryCoefficients identityBasis (fun _ => 1) 0 0 =
    dictionaryCoefficients identityBasis (fun _ => 1) 1 0 := by
  simp [dictionaryCoefficients, identityBasis]

-- Their first perturbation coefficients differ.
example : dictionaryCoefficients identityBasis (fun _ => 1) 0 ≠
    dictionaryCoefficients identityBasis (fun _ => 1) 1 := by
  intro h
  have hfirst := congrFun h (1 : Fin 3)
  change identityBasis⁻¹ 0 0 = identityBasis⁻¹ 1 0 at hfirst
  norm_num [identityBasis, Matrix.one_apply] at hfirst

private def triangular : Matrix (Fin 2) (Fin 2) ℚ := ![![1, 1], ![0, 1]]
private def triangularInverse : Matrix (Fin 2) (Fin 2) ℚ := ![![1, -1], ![0, 1]]

private theorem triangular_inverse : triangular⁻¹ = triangularInverse := by
  apply Matrix.inv_eq_left_inv
  ext i j
  change (∑ k, triangularInverse i k * triangular k j) = (if i = j then 1 else 0)
  fin_cases i <;> fin_cases j <;>
    norm_num [triangular, triangularInverse, Fin.sum_univ_two]

-- Solving this system produces two equal constant coefficients.
example : dictionaryCoefficients triangular ![2, 1] 0 0 = 1 ∧
    dictionaryCoefficients triangular ![2, 1] 1 0 = 1 := by
  norm_num [coefficient_zero, triangular_inverse, triangularInverse,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

-- The perturbation vector retains the negative coefficient from the inverse.
example : dictionaryCoefficients triangular ![2, 1] 0 2 = -1 := by
  change triangular⁻¹ 0 1 = -1
  rw [triangular_inverse]
  rfl

-- Empty bases have no candidate rows; injectivity still has the correct meaning.
example : Function.Injective (fun i : Fin 0 =>
    fun k => dictionaryCoefficients (1 : Matrix (Fin 0) (Fin 0) ℚ)
      (fun _ => 0) i k / (1 : ℚ)) := by
  intro i
  exact Fin.elim0 i

end GameTheory.Tests.PerturbedDictionary
