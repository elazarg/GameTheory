import GameTheoryComplexity.Backend.BinaryRatioExtraction

/-! Binary extraction controls cover interior ratios, dyadic ties, endpoints and clipping. -/
namespace GameTheory.Complexity.Tests.BinaryRatioExtraction
open Backend.BinaryRatioExtraction

example : Nat.fromBitsLE (prefixWord [true] [true, true] [false, false]) = 1 := by
  decide +kernel
example : Nat.fromBitsLE (remainderWord [true] [true, true] [false, false]) = 1 := by
  decide +kernel
example : Nat.fromBitsLE (prefixWord [true] [false, true] [false, false, false]) = 4 := by
  decide +kernel
example : Nat.fromBitsLE (remainderWord [true] [false, true] [false, false, false]) = 0 := by
  decide +kernel
example : Nat.fromBitsLE (prefixWord [true, true] [true, true] [false, false, false]) = 7 := by
  decide +kernel
example : Nat.fromBitsLE (remainderWord [true, true] [true, true] [false, false, false]) = 3 := by
  decide +kernel
example : Nat.fromBitsLE (prefixWord [true, false, true] [true, true] [false, false]) = 3 := by
  decide +kernel
example : Nat.fromBitsLE (remainderWord [true, false, true] [true, true] [false, false]) = 3 := by
  decide +kernel
example : Nat.fromBitsLE (prefixWord [true, false, false] [true, true, false]
    [true, false]) = 1 := by decide +kernel
example : prefixWord [true] [] [false, false] = [true, true] := by decide +kernel

end GameTheory.Complexity.Tests.BinaryRatioExtraction
