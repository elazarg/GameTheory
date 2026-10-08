import GameTheoryComplexity.Backend.BinaryDictionaryMachine

namespace GameTheory.Complexity.Tests.BinaryDictionaryMachine
open GameTheory.Complexity.Backend

private def width : List Bool := List.replicate 12 false
private def scalar (magnitude : List Bool) : List Bool :=
  binarySignedFixed width (false :: magnitude)
private def matrix : List Bool :=
  scalar [false, true] ++ scalar [true] ++ scalar [true] ++ scalar [false, false, true]
private def coefficients : List Bool := binaryDictionaryCoefficients ![[false, true], width, matrix]
private def direction : List Bool := binaryDictionaryDirection
  ![[true, false], width, matrix, scalar [false, true] ++ scalar [true]]

example : binarySignedRowValue width coefficients 0 = 3 := by decide +kernel
example : binarySignedRowValue width coefficients 1 = 4 := by decide +kernel
example : binarySignedRowValue width coefficients 2 = -1 := by decide +kernel
example : binarySignedRowValue width coefficients 3 = 1 := by decide +kernel
example : binarySignedRowValue width coefficients 4 = -1 := by decide +kernel
example : binarySignedRowValue width coefficients 5 = 2 := by decide +kernel
example : binarySignedRowValue width direction 0 = 7 := by decide +kernel
example : binarySignedRowValue width direction 1 = 0 := by decide +kernel
example : coefficients.length = 72 := by decide +kernel
example : binaryDictionaryCoefficients ![[], width, []] = [] := by decide +kernel
example : binaryDictionaryCoefficients ![[false, true], [], matrix] = [] := by decide +kernel

end GameTheory.Complexity.Tests.BinaryDictionaryMachine
