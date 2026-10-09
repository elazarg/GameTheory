import GameTheoryComplexity.Backend.BinaryBirdDeterminantMachine

/-! Kernel controls for fixed-width, materialized determinant stages. -/
namespace GameTheory.Complexity.Tests.BinaryBirdDeterminantMachine
open Backend

private def field (z : ℤ) : List Bool := decide (z < 0) :: Nat.toBitsLE 7 z.natAbs
private def width : List Bool := List.replicate 8 false

-- A zero leading pivot and a negative determinant need no division or pivot search.
example : binarySignedValue (binaryBirdDeterminant
    ![[false, false], width, field 0 ++ field 6 ++ field 4 ++ field 0]) = -24 := by
  decide +kernel
example : (binaryBirdStages [true] [false, false] width
    (field 0 ++ field 6 ++ field 4 ++ field 0)).length = 32 := by decide +kernel

example : binarySignedValue (binaryBirdDeterminant
    ![[true, false], width, field 2 ++ field 1 ++ field 1 ++ field (-3)]) = -7 := by
  decide +kernel
example : binarySignedValue (binaryBirdDeterminant
    ![[true, true], width, field 1 ++ field 2 ++ field 2 ++ field 4]) = 0 := by
  decide +kernel

-- The empty matrix determinant is one; a zero-width machine remains total.
example : binarySignedValue (binaryBirdDeterminant ![[], width, [true]]) = 1 := by decide +kernel
example : binaryBirdDeterminant ![[true], [], field 2] = [] := by decide +kernel

example : binarySignedValue (binaryBirdSign [false, true, false]) = -1 := by decide +kernel
example : binarySignedValue (binaryBirdSign [false, true]) = 1 := by decide +kernel

end GameTheory.Complexity.Tests.BinaryBirdDeterminantMachine
