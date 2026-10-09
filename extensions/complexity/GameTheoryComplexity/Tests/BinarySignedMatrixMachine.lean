import GameTheoryComplexity.Backend.BinarySignedMatrixMachine

/-! Kernel controls for fixed-width arithmetic and stored dot-product accumulators. -/
namespace GameTheory.Complexity.Tests.BinarySignedMatrixMachine
open Backend

example : binarySignedFixed [false, false, false, false] [true, true, true, false, false, false] =
    [true, true, true, false] := by decide +kernel
example : binarySignedFixed [true, true, true, true] [] = [false, false, false, false] := by
  decide +kernel
example : binarySignedFixed [] [true, true] = [] := by decide +kernel

example : binarySignedValue
    (binarySignedFixedMul [true, true, true, true] [false, true, true] [false, false, true]) = 6 := by
  decide +kernel
-- Overflow truncates; the exactness theorem requires the result to fit the magnitude capacity.
example : binarySignedValue
    (binarySignedFixedMul [true, true, true] [false, true, true] [false, true, true]) = 1 := by
  decide +kernel

-- The dot product is 3*2 + 2*(-1)=4; its first prefix is6, within width-four capacity8.
example : binarySignedValue (binarySignedDot [false, true] [false, false, false, false]
    [false, true, true, false, false, false, true, false]
    [false, false, true, false, true, true, false, false]) = 4 := by decide +kernel
example : (binarySignedDot [false, true] [false, false, false, false]
    [false, true, true, false, false, false, true, false]
    [false, false, true, false, true, true, false, false]).length = 4 := by decide +kernel
example : binarySignedValue (binarySignedDot [] [true, true, true, true] [] []) = 0 := by
  decide +kernel
example : binarySignedDot [true, true] [] [true] [true] = [] := by decide +kernel

-- Tabulation stores two fields in their original order and normalizes each one.
example : binarySignedTable binarySignedRowField [false, false] [false, false, false, false]
    ![[false, false, false, false], [false, true, true, false, false, false, true, false]] =
      [false, true, true, false, false, false, true, false] := by decide +kernel

end GameTheory.Complexity.Tests.BinarySignedMatrixMachine
