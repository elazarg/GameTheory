import GameTheoryComplexity.Backend.SpernerCoordinateColor

/-! Coordinate queries retain the high boundary bit and the canonical edge priority. -/
namespace GameTheory.Complexity.Tests.SpernerCoordinateColor
open Backend _root_.Complexity

example : gridCoordinateColor (pair [true] []) [false, true, true, false] =
    [false, true] := by decide +kernel

example : gridCoordinateColor (pair [true] []) [false, true, false, false] =
    [true, false] := by decide +kernel

example : gridCoordinateColor (pair [true] []) [false, false, false, true] =
    [false, true] := by decide +kernel

example (source vertex : List Bool) : (gridCoordinateColor source vertex).length = 2 :=
  gridCoordinateColor_length source vertex

example (source : List Bool) : gridCoordinateColor source
    (Nat.toBitsLE ((pairFst source).length + 1) (2 ^ (pairFst source).length) ++
      Nat.toBitsLE ((pairFst source).length + 1) 0) =
    encodeGridColor (spernerColor source (2 ^ (pairFst source).length) 0) :=
  gridCoordinateColor_encode source _ _ le_rfl (Nat.zero_le _)

end GameTheory.Complexity.Tests.SpernerCoordinateColor
