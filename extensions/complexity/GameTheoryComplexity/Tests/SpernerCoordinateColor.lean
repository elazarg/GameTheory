module

public import GameTheoryComplexity.Backend.SpernerCoordinateColor

@[expose] public section

/-! Coordinate queries retain the high boundary bit and the canonical edge priority. -/
namespace GameTheory.Complexity.Tests.SpernerCoordinateColor
open Backend Turing.MultiTapeTM Cslib.BitString

example : gridCoordinateColor (CircuitWords.encodePair [true] []) [false, true, true, false] =
    [false, true] := by decide +kernel

example : gridCoordinateColor (CircuitWords.encodePair [true] []) [false, true, false, false] =
    [true, false] := by decide +kernel

example : gridCoordinateColor (CircuitWords.encodePair [true] []) [false, false, false, true] =
    [false, true] := by decide +kernel

example (source vertex : List Bool) : (gridCoordinateColor source vertex).length = 2 :=
  gridCoordinateColor_length source vertex

example (source : List Bool) : gridCoordinateColor source
    (lowBits ((CircuitWords.first source).length + 1) (2 ^ (CircuitWords.first source).length) ++
      lowBits ((CircuitWords.first source).length + 1) 0) =
    encodeGridColor (spernerColor source (2 ^ (CircuitWords.first source).length) 0) :=
  gridCoordinateColor_encode source _ _ le_rfl (Nat.zero_le _)

example : ComputableInPolyTime (fun p : List Bool × List Bool => gridCoordinateColor p.1 p.2)
    (encPair encBits encBits) encBits :=
  gridCoordinateColor_polyTime (ComputableInPolyTime.fst encBits encBits)
    (ComputableInPolyTime.snd encBits encBits)

end GameTheory.Complexity.Tests.SpernerCoordinateColor
