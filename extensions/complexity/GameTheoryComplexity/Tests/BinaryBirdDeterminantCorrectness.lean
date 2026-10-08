import GameTheoryComplexity.Backend.BinaryBirdDeterminantCorrectness

/-! Kernel controls applying the determinant theorem with its polynomial work width. -/
namespace GameTheory.Complexity.Tests.BinaryBirdDeterminantCorrectness
open Backend

private def dim : List Bool := [false, true]
private def width : List Bool := List.replicate (GameTheory.Math.BirdIterationBounds.workWidth 2 3) false
private def field (z : ℤ) : List Bool := decide (z < 0) :: Nat.toBitsLE (width.length - 1) z.natAbs
private def matrix : List Bool := field 0 ++ field 6 ++ field 4 ++ field 0

-- Apply the mathematical correctness theorem to a matrix with zero leading pivot.
example : binarySignedValue (binaryBirdDeterminant ![dim, width, matrix]) =
    (binaryBirdMatrix dim width matrix).det := by
  apply binaryBirdDeterminant_value dim width matrix 3
  · rfl
  · decide +kernel
  · decide +kernel

example : (binaryBirdMatrix dim width matrix).det = -24 := by
  exact (Matrix.det_fin_two (binaryBirdMatrix dim width matrix)).trans (by decide +kernel)

-- Arbitrary unary ruler bits do not alter the recurrence or its stage count.
example : binaryBirdMatrix dim width (binaryBirdStages [false] dim width matrix) =
    BirdDet.Spec.stepEntry (binaryBirdMatrix dim width matrix) (binaryBirdMatrix dim width matrix) := by
  exact binaryBirdStages_eq_spec [false] dim width matrix 3 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : binarySignedValue (binaryBirdDeterminant
    ![[], List.replicate (GameTheory.Math.BirdIterationBounds.workWidth 0 0) true, []]) = 1 := by
  have h := binaryBirdDeterminant_value []
    (List.replicate (GameTheory.Math.BirdIterationBounds.workWidth 0 0) true) [] 0 rfl rfl
    (by intro i; exact Fin.elim0 i)
  exact h.trans (by simp)

end GameTheory.Complexity.Tests.BinaryBirdDeterminantCorrectness
