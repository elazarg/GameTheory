import GameTheoryComplexity.Backend.BinarySignedAddition
import GameTheoryComplexity.Backend.BinarySignedCrossComparison

/-! Kernel-checked controls for signed binary arithmetic and ratio comparison. -/
namespace GameTheory.Complexity.Tests.BinarySignedArithmetic
open Backend

-- A borrow cascades through all intervening zero bits; underflow saturates.
example : Nat.fromBitsLE (binaryWordSub [false, false, false, false, true] [true]) = 15 := by
  decide +kernel
example : binaryWordSub [true] [false, true] = [] := by decide +kernel
example : Nat.fromBitsLE (binaryWordSub [true, false, false] [true]) = 0 := by
  decide +kernel

-- Opposite signs, carries, cancellation, and unequal padded magnitudes.
example : binarySignedValue (binarySignedAdd [true, true, false, true] [false, true, true]) = -2 := by
  decide +kernel
example : binarySignedValue (binarySignedAdd [false, true, true] [false, true]) = 4 := by
  decide +kernel
example : binarySignedValue (binarySignedAdd [true, true, true] [true, true]) = -4 := by
  decide +kernel
example : binarySignedValue (binarySignedAdd [true, true, false, false] [false, true]) = 0 := by
  decide +kernel
example : binarySignedValue (binarySignedAdd [] [true]) = 0 := by decide +kernel
example : binarySignedValue (binarySignedSub [false, true, true] [true, true, false, true]) = 8 := by
  decide +kernel
example : binarySignedValue (binarySignedSub [true, true] [false, true, true]) = -4 := by
  decide +kernel

example : binarySignedValue (binarySignedMul [true, true, false, true] [true, true, true]) = 15 := by
  decide +kernel
example : binarySignedValue (binarySignedMul [true, true, false, true] [false, true, true]) = -15 := by
  decide +kernel
example : binarySignedValue (binarySignedNeg []) = 0 := by decide +kernel
example : binarySignedLTFlag [true, false, false] [] = [false] := by decide +kernel
example : binarySignedLTFlag [true] [false, true] = [true] := by decide +kernel
example : binarySignedLTFlag [true, true, false, true] [true, true, true] = [true] := by
  decide +kernel

-- Negative numerators and positive denominators: -5/2 < -3/3.
example : binarySignedCrossLT
    ![[true, true, false, true], [true, true, true], [false, false, true], [false, true, true]] =
      [true] := by decide +kernel
-- Equal ratios with different padding and scales.
example : binarySignedCrossLT
    ![[false, true, false], [false, false, true], [false, true], [false, false, true, false]] =
      [false] := by decide +kernel

end GameTheory.Complexity.Tests.BinarySignedArithmetic
