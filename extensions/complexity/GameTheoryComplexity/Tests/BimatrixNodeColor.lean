import GameTheoryComplexity.Backend.BimatrixNodeColor

namespace GameTheory.Complexity.Backend.Tests.BimatrixNodeColor
open GameTheory.Complexity.Backend

-- Source insertion rank is odd; its payoff kind is excluded at dropped label zero.
example : binarySignedValue (bimatrixNodeOrientationWord
    ![[true], [false, false, false, false], [false], [false, true]]) = -1 := by decide

-- The source is calibrated against the very same score routine.
example : binaryScoreColor ![
    bimatrixNodeOrientationWord ![[true], [false, false, false, false], [false], [false, true]],
    bimatrixNodeOrientationWord ![[false], [false, false, false, false], [true], [false, true]]] =
    [true] := by decide

-- The two internal ports have opposite payoff parity with the same basis determinant.
example : binarySignedValue (bimatrixNodeOrientationWord
    ![[false, true], [false, true, true, false, false, true, true, false], [false, true],
      [false, true, true]]) = 3 := by decide

example : binarySignedValue (bimatrixNodeOrientationWord
    ![[true, false], [false, true, true, false, false, true, false, true], [true, false, false],
      [false, true, true]]) = -3 := by decide

-- Existing nonzero-label payoff membership cancels an odd insertion rank.
example : binarySignedValue (bimatrixNodeOrientationWord
    ![[true, true], [false, false, true, true, false, true, true, false], [true, false],
      [false, false, true]]) = 2 := by decide

-- Determinant sign and padding are preserved numerically without fixed-capacity normalization.
example : binarySignedValue (bimatrixNodeOrientationWord
    ![[true], [true, true, true, true], [], [true, false, true, false, false]]) = -2 := by decide

example : binaryScoreColor ![[false, true], [true, true]] = [false] := by decide
example : binaryScoreColor ![[true, true], [true, false, true]] = [true] := by decide
example : binaryScoreColor ![[true, false, false], [true, true]] = [false] := by decide

-- Zero determinants remain zero and never have a positive calibrated product.
example : binarySignedValue (bimatrixNodeOrientationWord ![[], [], [], []]) = 0 := by decide
example : binaryScoreColor ![[], [false, true]] = [false] := by decide

end GameTheory.Complexity.Backend.Tests.BimatrixNodeColor