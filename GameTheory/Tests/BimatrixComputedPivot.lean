import GameTheory.Finite.BimatrixComputedPivot

/-! A rectangular degenerate source and its computed reverse exchange. -/

namespace GameTheory.Tests.BimatrixComputedPivot
open GameTheory.Finite GameTheory.Math

private def allOnes : Fin 1 → Fin 2 → ℤ := fun _ _ => 1

private def port : BimatrixPivotPort allOnes allOnes where
  basis := bimatrixSourceBasis allOnes allOnes
  entering := toLex ((0 : Fin 3), true)
  nonbasic := by simp [bimatrixSourceBasis, bimatrixSlackVariables]

private theorem sourceMatrix : port.basis.integerMatrix = 1 := by
  have hh : port.basis.integerMatrix.map (fun z : ℤ => (z : ℚ)) =
      (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
    rw [port.basis.integerMatrix_map]
    exact bimatrixSlack_basisMatrix allOnes allOnes
  ext i j
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ => M i j) hh
  simp only [Matrix.map_apply, Matrix.one_apply] at he ⊢
  split_ifs at he ⊢ <;> exact_mod_cast he

private theorem selected : port.computedLeavingRow = some 2 := by
  unfold BimatrixPivotPort.computedLeavingRow
  rw [sourceMatrix]
  decide +kernel

-- The two eligible rows have the same constant ratio; perturbations select the last.
example : port.computedLeavingRow = some 2 := selected

example : port.basis.IsLeaving port.entering 2 :=
  port.computedLeavingRow_spec 2 selected

example : port.computedPivot = some (port.pivot (by decide) (by decide)
    (by intro _ _; exact Int.zero_lt_one) (by intro _ _; exact Int.zero_lt_one)) :=
  port.computedPivot_eq_some _ _ _ _

-- Execute the first exchange and the reverse exchange, then compare the stored port data.
example : (port.computedPivot.bind BimatrixPivotPort.computedPivot).map
    (fun p => (p.basis.basic, p.entering)) = some (port.basis.basic, port.entering) := by
  have hA : ∀ i j, 0 < allOnes i j := fun _ _ => Int.zero_lt_one
  rw [port.computedPivot_eq_some (by decide) (by decide) hA hA, Option.bind_some,
    (port.pivot (by decide) (by decide) hA hA).computedPivot_eq_some
      (by decide) (by decide) hA hA, port.pivot_pivot (by decide) (by decide) hA hA]
  rfl

end GameTheory.Tests.BimatrixComputedPivot
