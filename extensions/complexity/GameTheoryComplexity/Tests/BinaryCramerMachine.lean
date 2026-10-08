import GameTheoryComplexity.Backend.BinaryCramerMachine
import GameTheoryComplexity.Backend.BinaryBirdWidth

namespace GameTheory.Complexity.Tests.BinaryCramerMachine
open GameTheory.Complexity.Backend

private def width : List Bool := List.replicate 12 false
private def scalar (negative : Bool) (magnitude : List Bool) : List Bool :=
  binarySignedFixed width (negative :: magnitude)
private def positiveMatrix : List Bool :=
  scalar false [false, true] ++ scalar false [true] ++
    scalar false [true] ++ scalar false [false, false, true]
private def negativeMatrix : List Bool :=
  scalar false [] ++ scalar false [false, true] ++
    scalar false [true, true] ++ scalar false [false, false, true]
private def ones : List Bool := scalar false [true] ++ scalar false [true]

example : binarySignedValue (binarySignedSign [true, false, false]) = 0 := by decide +kernel
example : binarySignedValue (binarySignedSign [false, false, true]) = 1 := by decide +kernel
example : binarySignedValue (binarySignedSign [true, false, true]) = -1 := by decide +kernel

example : binarySignedValue (binaryCramerDeterminant
    ![[false, true], width, positiveMatrix, ones, []]) = 3 := by decide +kernel
example : binarySignedValue (binaryCramerNumerator
    ![[false, true], width, positiveMatrix, ones, [false]]) = 1 := by decide +kernel
example : binarySignedValue (binaryCramerNumerator
    ![[true, false], width, negativeMatrix, ones, []]) = -2 := by decide +kernel
example : binarySignedValue (binaryCramerNumerator
    ![[true, false], width, negativeMatrix, ones, [true]]) = 3 := by decide +kernel
example : (binaryCramerMatrix ![[true, false], width, negativeMatrix, ones, []]).length = 48 :=
  by decide +kernel
example : binaryCramerNumerator ![[true, false], [], negativeMatrix, ones, []] = [] :=
  by decide +kernel

example : (binaryBirdWorkWidth ![[false, true], [false, false, false]]).length = 57 :=
  by decide +kernel

end GameTheory.Complexity.Tests.BinaryCramerMachine
