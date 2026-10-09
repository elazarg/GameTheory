import GameTheoryComplexity.Backend.BinarySubsetMachine

namespace GameTheory.Complexity.Tests.BinarySubsetMachine
open GameTheory.Complexity.Backend

-- False positions do not contribute to ordinals; ordinal bits supply only a length.
example : binarySubsetNthPosition ![[false, true, false, true, true], []] = some 1 := by
  decide +kernel
example : binarySubsetNthPosition ![[false, true, false, true, true], [false]] = some 3 := by
  decide +kernel
example : binarySubsetNthPosition ![[false, true, false, true, true], [false, true]] = some 4 := by
  decide +kernel
example : binarySubsetNthPosition ![[false, true, false, true, true], [true, true, true]] = none := by
  decide +kernel

-- Leading and trailing selected positions distinguish increasing order from a reverse scan.
example : binarySubsetNthPosition ![[true, false, false, true], []] = some 0 := by
  decide +kernel
example : binarySubsetNthPosition ![[true, false, false, true], [true]] = some 3 := by
  decide +kernel

example : binarySubsetNth ![[], []] = [false] := by decide +kernel
example : binarySubsetNth ![[false, false, false], []] = [false] := by decide +kernel
example : binarySubsetTally [false, true, false, true] = [true, true] := by decide +kernel
example : binarySubsetParity [] = [false] := by decide +kernel
example : binarySubsetParity [true, false, true] = [false] := by decide +kernel
example : binarySubsetParity [false, true, true, false, true] = [true] := by decide +kernel

example : _root_.Complexity.Cobham binarySubsetNth := binarySubsetNth_cobham
example : _root_.Complexity.Cobham.FPn binarySubsetNth := binarySubsetNth_mem_FPn

end GameTheory.Complexity.Tests.BinarySubsetMachine
