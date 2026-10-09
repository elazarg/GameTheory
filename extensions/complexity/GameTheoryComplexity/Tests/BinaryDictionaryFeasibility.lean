import GameTheoryComplexity.Backend.BinaryDictionaryFeasibility
import GameTheoryComplexity.Backend.BinarySignedFixedWidth

namespace GameTheory.Complexity.Tests.BinaryDictionaryFeasibility
open GameTheory.Complexity.Backend

private def width : List Bool := List.replicate 5 false
private def scalar (negative : Bool) (magnitude : List Bool) : List Bool :=
  binarySignedFixed width (negative :: magnitude)

-- Zero constants remain valid when the first nonzero perturbation is positive.
example : binaryDictionaryPositive ![[false], [false, true, false], width,
    scalar false [] ++ scalar false [false, true] ++ scalar true [true, true]] = [true] :=
  by decide +kernel
example : binaryDictionaryPositive ![[true], [true, false, true], width,
    scalar false [] ++ scalar true [false, true] ++ scalar false [true, true]] = [false] :=
  by decide +kernel
example : binaryDictionaryPositive ![[false], [false], width, scalar true []] = [false] :=
  by decide +kernel
example : binaryDictionaryPositive ![[], [], [], []] = [true] := by decide +kernel
example : binaryDictionaryPositive ![[true], [], width, []] = [false] := by decide +kernel
example : binaryDictionaryPositive ![[true], [true], [], [true]] = [false] := by decide +kernel
example : binaryDictionaryPositive ![[false, true], [false], width,
    scalar false [true] ++ scalar true [true]] = [false] := by decide +kernel

end GameTheory.Complexity.Tests.BinaryDictionaryFeasibility
