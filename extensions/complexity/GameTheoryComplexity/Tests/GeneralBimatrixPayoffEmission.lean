import GameTheoryComplexity.Backend.GeneralBimatrixPayoffEmission

/-! Magnitude emission controls cover positive, negative, padded zero and truncation. -/
namespace GameTheory.Complexity.Tests.GeneralBimatrixPayoffEmission
open Backend

example : generalSignedMagnitude true [false, false, false] [false, true, false, true] =
    [true, false, true] ∧
    generalSignedMagnitude false [false, false, false] [false, true, false, true] =
      [false, false, false] := by decide +kernel

example : generalSignedMagnitude true [false, false, false] [true, true, false, true] =
    [false, false, false] ∧
    generalSignedMagnitude false [false, false, false] [true, true, false, true] =
      [true, false, true] := by decide +kernel

example : generalSignedMagnitude true [false, false, false] [true, false, false, false] =
    [false, false, false] ∧
    generalSignedMagnitude false [false, false, false] [true, false, false, false] =
      [false, false, false] := by decide +kernel

-- The representability premise prevents silently treating a truncated magnitude as its source.
example : generalSignedMagnitude true [false, false, false] [false, true, false, false, true] =
    [true, false, false] ∧ binarySignedValue [false, true, false, false, true] = 9 := by
  decide +kernel

example : (Nat.fromBitsLE (generalSignedMagnitude true [false, false, false]
      [true, true, false, true]) : ℤ) -
    (Nat.fromBitsLE (generalSignedMagnitude false [false, false, false]
      [true, true, false, true]) : ℤ) = binarySignedValue [true, true, false, true] := by
  exact generalSignedMagnitude_value _ _ (by decide +kernel)
end GameTheory.Complexity.Tests.GeneralBimatrixPayoffEmission
