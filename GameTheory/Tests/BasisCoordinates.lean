import GameTheory.Math.BasisCoordinates
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Sparse basis coordinates retain zero constants and solve ambient equations. -/

namespace GameTheory.Tests.BasisCoordinates
open GameTheory.Math.BasisCoordinates GameTheory.Math.CanonicalDictionary

private def labels : Finset (Fin 3) := {0, 2}
private theorem labels_card : labels.card = 2 := by decide
private def columns : Matrix (Fin 2) (Fin 3) ℚ := !![1, 99, 0; 0, 99, 1]
private theorem enumeration : (labels.orderEmbOfFin labels_card : Fin 2 → Fin 3) = ![0, 2] := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro j
    fin_cases j <;> decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

example : lift labels labels_card (![0, 2] : Fin 2 → ℚ) 0 = 0 := by
  have h := lift_on_enumeration labels labels_card (![0, 2] : Fin 2 → ℚ) 0
  simpa only [enumeration, Matrix.cons_val_zero] using h
example : lift labels labels_card (![0, 2] : Fin 2 → ℚ) 2 = 2 := by
  have h := lift_on_enumeration labels labels_card (![0, 2] : Fin 2 → ℚ) 1
  simpa only [enumeration, Matrix.cons_val_one, Matrix.cons_val_zero] using h
example : lift labels labels_card (![0, 2] : Fin 2 → ℚ) 1 = 0 :=
  lift_outside _ _ _ _ (by decide)

private theorem basis_identity : basisMatrix columns labels labels_card = 1 := by
  ext i j
  change columns i ((labels.orderEmbOfFin labels_card : Fin 2 → Fin 3) j) = (1 : Matrix _ _ ℚ) i j
  rw [enumeration]
  fin_cases i <;> fin_cases j <;> norm_num [columns, Matrix.one_apply]

-- The unused column has large coefficients but contributes zero.
example (i : Fin 2) :
    ∑ v, columns i v * lift labels labels_card (![0, 2] : Fin 2 → ℚ) v =
      (![0, 2] : Fin 2 → ℚ) i := by
  rw [sum_columns_lift, basis_identity, Matrix.one_mulVec]

example (i : Fin 2) :
    ∑ v, columns i v * inverseCoordinates columns ![0, 2] labels labels_card v =
      (![0, 2] : Fin 2 → ℚ) i :=
  inverseCoordinates_equation _ _ _ _ (by rw [basis_identity]; simp) i

example : inverseCoordinates columns ![0, 2] labels labels_card 1 = 0 :=
  inverseCoordinates_outside _ _ _ _ _ (by decide)

example : ∀ v, 0 ≤ lift labels labels_card (![0, 2] : Fin 2 → ℚ) v := by
  apply lift_nonneg
  intro j
  fin_cases j <;> norm_num

end GameTheory.Tests.BasisCoordinates
