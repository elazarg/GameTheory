import GameTheory.Finite.BimatrixPivot

/-! Exact deterministic pivot and reverse-port controls in a positive 1×1 game. -/
namespace GameTheory.Tests.BimatrixPivot
open GameTheory.Finite GameTheory.Math GameTheory.Math.CanonicalDictionary
private def allOnes : Fin 1 → Fin 1 → ℤ := fun _ _ => 1
private def port : BimatrixPivotPort allOnes allOnes where
  basis := bimatrixSourceBasis allOnes allOnes
  entering := toLex ((0 : Fin 2), true)
  nonbasic := by simp [bimatrixSourceBasis, bimatrixSlackVariables]

private theorem leaving : port.leavingRow (by decide) (by decide)
    (by intro _i _j; exact Int.zero_lt_one) (by intro _i _j; exact Int.zero_lt_one) = 1 := by
  have h := (port.leavingRow_spec (by decide) (by decide)
    (by intro _i _j; exact Int.zero_lt_one) (by intro _i _j; exact Int.zero_lt_one)).1
  change 0 < ((basisMatrix (bimatrixBasisColumns allOnes allOnes)
    (bimatrixSlackVariables 1 1) bimatrixSlackVariables_card)⁻¹.mulVec
      (fun i => bimatrixBasisColumns allOnes allOnes i (toLex ((0 : Fin 2), true))))
      (port.leavingRow (by decide) (by decide)
        (by intro _i _j; exact Int.zero_lt_one) (by intro _i _j; exact Int.zero_lt_one)) at h
  rw [bimatrixSlack_basisMatrix, inv_one, Matrix.one_mulVec] at h
  generalize hr : port.leavingRow (by decide) (by decide)
    (by intro _i _j; exact Int.zero_lt_one) (by intro _i _j; exact Int.zero_lt_one) = l at h ⊢
  fin_cases l
  · have hz : (finSumFinEquiv : (Fin 1 ⊕ Fin 1) ≃ Fin 2).symm 0 = .inl 0 := by decide
    simp [bimatrixBasisColumns, bimatrixEnteringColumn, hz, bimatrixComplementaryMatrix] at h
  · rfl

example : port.leavingRow (by decide) (by decide)
    (by intro _i _j; exact Int.zero_lt_one) (by intro _i _j; exact Int.zero_lt_one) = 1 := leaving

example : (port.pivot (by decide) (by decide)
      (by intro _i _j; exact Int.zero_lt_one) (by intro _i _j; exact Int.zero_lt_one)).pivot
      (by decide) (by decide) (by intro _i _j; exact Int.zero_lt_one)
      (by intro _i _j; exact Int.zero_lt_one) = port :=
  port.pivot_pivot _ _ _ _

example : port.pivot (by decide) (by decide) (by intro _i _j; exact Int.zero_lt_one)
    (by intro _i _j; exact Int.zero_lt_one) ≠ port := port.pivot_ne_self _ _ _ _

end GameTheory.Tests.BimatrixPivot
