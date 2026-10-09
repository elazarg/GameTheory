import GameTheoryComplexity.Backend.BinaryDictionaryCorrectness

/-! Controls for symbolic column ordering and signed entering directions. -/
namespace GameTheory.Complexity.Tests.BinaryDictionaryCorrectness
open Backend

private def dim : List Bool := [true, false]
private def width : List Bool := List.replicate (GameTheory.Math.BirdIterationBounds.workWidth 2 3) false
private def field (z : ℤ) : List Bool := decide (z < 0) :: Nat.toBitsLE (width.length - 1) z.natAbs
private def matrix : List Bool := field 0 ++ field 6 ++ field 4 ++ field 0
private def entering : List Bool := field (-3) ++ field 5

-- The first coefficient is constant; the next two are ordered perturbation coefficients.
example (i : Fin 2) (k : Fin 3) :
    binarySignedRowValue width (binaryDictionaryCoefficients ![dim, width, matrix])
      (i.val * 3 + k.val) = (!![6, 0, 6; 4, 4, 0] : Matrix (Fin 2) (Fin 3) ℤ) i k := by
  have he := binaryDictionaryCoefficients_value dim width matrix 3 rfl
    (by decide +kernel) (by decide +kernel) i k
  refine he.trans ?_
  fin_cases i <;> fin_cases k <;> decide +kernel

-- Entering directions retain negative coordinates rather than converting them to naturals.
example (i : Fin 2) :
    binarySignedRowValue width (binaryDictionaryDirection ![dim, width, matrix, entering]) i.val =
      (![30, -12] : Fin 2 → ℤ) i := by
  have he := binaryDictionaryDirection_value dim width matrix entering 3 rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) i
  refine he.trans ?_
  fin_cases i <;> decide +kernel

-- Singular matrices still satisfy the computation contract; all sign-adjusted numerators vanish.
example (i : Fin 2) (k : Fin 3) :
    binarySignedRowValue width (binaryDictionaryCoefficients
      ![dim, width, field 0 ++ field 0 ++ field 0 ++ field 0]) (i.val * 3 + k.val) = 0 := by
  have he := binaryDictionaryCoefficients_value dim width
    (field 0 ++ field 0 ++ field 0 ++ field 0) 3 rfl
    (by decide +kernel) (by decide +kernel) i k
  refine he.trans ?_
  fin_cases i <;> fin_cases k <;> decide +kernel

example : binaryDictionaryCoefficients
    ![[], List.replicate (GameTheory.Math.BirdIterationBounds.workWidth 0 0) false, []] = [] := by
  decide +kernel

end GameTheory.Complexity.Tests.BinaryDictionaryCorrectness
