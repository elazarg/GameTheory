module

public import GameTheoryComplexity.Backend.BinaryRatioExtraction

@[expose] public section

/-! Binary extraction controls cover interior ratios, dyadic ties, endpoints and clipping. -/
namespace GameTheory.Complexity.Tests.BinaryRatioExtraction
open Backend.BinaryRatioExtraction Turing.MultiTapeTM

example : ofBits (prefixWord [true] [true, true] [false, false]) = 1 := by
  decide +kernel
example : ofBits (remainderWord [true] [true, true] [false, false]) = 1 := by
  decide +kernel
example : ofBits (prefixWord [true] [false, true] [false, false, false]) = 4 := by
  decide +kernel
example : ofBits (remainderWord [true] [false, true] [false, false, false]) = 0 := by
  decide +kernel
example : ofBits (prefixWord [true, true] [true, true] [false, false, false]) = 7 := by
  decide +kernel
example : ofBits (remainderWord [true, true] [true, true] [false, false, false]) = 3 := by
  decide +kernel
example : ofBits (prefixWord [true, false, true] [true, true] [false, false]) = 3 := by
  decide +kernel
example : ofBits (remainderWord [true, false, true] [true, true] [false, false]) = 3 := by
  decide +kernel
example : ofBits (prefixWord [true, false, false] [true, true, false]
    [true, false]) = 1 := by decide +kernel
example : prefixWord [true] [] [false, false] = [true, true] := by decide +kernel

example : ComputableInPolyTime
    (fun v : Fin 3 → List Bool => prefixWord (v 0) (v 1) (v 2)) (encPi encBits) encBits :=
  prefixWord_polyTime (ComputableInPolyTime.pi_apply encBits (0 : Fin 3))
    (ComputableInPolyTime.pi_apply encBits (1 : Fin 3))
    (ComputableInPolyTime.pi_apply encBits (2 : Fin 3))

end GameTheory.Complexity.Tests.BinaryRatioExtraction
