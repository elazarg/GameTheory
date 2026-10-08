import GameTheory.Math.FacetOrientation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Signed cofactors track the sign change caused by canonical sorting of a pivot. -/

namespace GameTheory.Tests.FacetOrientation

open GameTheory.Math.FacetOrientation GameTheory.Math.CanonicalDictionary

private def columns : Matrix (Fin 2) (Fin 3) ℚ := !![1, 0, 1; 0, 1, 1]

example : orientation columns = (![-1, -1, 1] : Fin 3 → ℚ) := by
  funext k
  fin_cases k <;> norm_num [orientation, facetMatrix, columns, Matrix.det_fin_two,
    Matrix.submatrix_apply, Fin.succAbove, Fin.predAbove]

example : columns.mulVec (orientation columns) = 0 := mulVec_orientation columns

example : orientation columns 0 =
    -((facetMatrix columns 2)⁻¹.mulVec (fun i => columns i 2) 0) * orientation columns 2 := by
  have hdet : (facetMatrix columns 2).det ≠ 0 := by
    norm_num [facetMatrix, columns, Matrix.det_fin_two, Matrix.submatrix_apply,
      Fin.succAbove, Fin.predAbove]
  have h := exchange_orientation columns 2 0 hdet
  have hk : (2 : Fin 3).succAbove 0 = 0 := by decide
  rw [hk] at h
  exact h

private def basis : Finset (Fin 3) := {0, 1}
private theorem basis_card : basis.card = 2 := by decide
private theorem entering_new : (2 : Fin 3) ∉ basis := by decide

private theorem initial_matrix : basisMatrix columns basis basis_card = 1 := by
  have he := GameTheory.Math.FiniteBasisExchange.canonical_unique basis_card
    (f := (![0, 1] : Fin 2 → Fin 3)) (by decide) (by decide)
  ext i j
  change columns i (basis.orderEmbOfFin basis_card j) = _
  rw [← congrFun he j]
  fin_cases i <;> fin_cases j <;> norm_num [columns]

-- The augmented set is the same on both sides even when sorting moves the leaving slot.
example : canonicalOrientation columns (insert 2 basis)
    ((Finset.card_insert_of_notMem entering_new).trans (congrArg (· + 1) basis_card))
    (basis.orderEmbOfFin basis_card 0)
    (Finset.mem_insert_of_mem (Finset.orderEmbOfFin_mem basis basis_card 0)) =
    -((basisMatrix columns basis basis_card)⁻¹.mulVec (fun i => columns i 2) 0) *
      canonicalOrientation columns (insert 2 basis)
        ((Finset.card_insert_of_notMem entering_new).trans (congrArg (· + 1) basis_card))
        2 (Finset.mem_insert_self _ _) :=
  canonical_exchange_orientation columns basis basis_card 2 entering_new 0
    (by rw [initial_matrix]; simp)

example : canonicalOrientation columns (insert 2 basis)
    ((Finset.card_insert_of_notMem entering_new).trans (congrArg (· + 1) basis_card))
    2 (Finset.mem_insert_self _ _) ≠ 0 := by
  apply (canonicalOrientation_insert_ne_zero_iff columns basis basis_card 2 entering_new).mpr
  rw [initial_matrix]
  simp

end GameTheory.Tests.FacetOrientation
