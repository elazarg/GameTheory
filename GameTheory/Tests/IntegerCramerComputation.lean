import GameTheory.Math.IntegerCramerComputation
import GameTheory.Math.IntegerDictionaryComputation
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Controls for materialized determinant computation and exact Cramer fields. -/

namespace GameTheory.Tests.IntegerCramerComputation
open GameTheory.Math.IntegerCramerComputation

-- A zero diagonal must not require a nonzero leading pivot.
example : determinant !![(0 : ℤ), 6; 4, 0] = -24 := by decide +kernel

example : denominator !![(0 : ℤ), 6; 4, 0] = 24 := by decide +kernel

example : numerator !![(0 : ℤ), 6; 4, 0] ![1, 1] 0 = 6 := by decide +kernel

example : numerator !![(0 : ℤ), 6; 4, 0] ![1, 1] 1 = 4 := by decide +kernel

example : determinant !![(2 : ℤ), 1; 1, -3] = -7 := by decide +kernel

example : determinant !![(1 : ℤ), 2; 2, 4] = 0 := by decide +kernel

example : determinant (fun _ _ : Fin 0 => (0 : ℤ)) = 1 := by decide +kernel

-- Three stages exercise materialization beyond one scalar update.
example : determinant !![(1 : ℤ), 2, 3, 4; 0, 2, 5, 6; 0, 0, -3, 7; 0, 0, 0, 4] =
    -24 := by decide +kernel

-- Agreement includes singular and signed systems, without feasibility premises.
example : determinant (fun i j : Fin 6 => if i = j then (2 : ℤ) else 1) = 7 :=
  by decide +kernel

example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (i : Fin n) :
    numerator M b i = GameTheory.Math.IntegerCramerEncoding.numerator M b i :=
  numerator_eq M b i

-- Replacing a column can give a nonzero determinant even when the original is singular.
example : (Matrix.updateCol (!![(1 : ℤ), 2; 2, 4]) 0 ![-1, 1]).det = -6 := by
  decide +kernel

example (i : Fin 2) : signedNumerator !![(1 : ℤ), 2; 2, 4] ![-1, 1] i = 0 := by
  fin_cases i <;> decide +kernel

-- Storage bounds apply to this unchecked singular dictionary without an invertibility premise.
example (i : Fin 2) : (signedNumerator !![(1 : ℤ), 2; 2, 4] ![-1, 1] i).natAbs <
    2 ^ GameTheory.Math.IntegerBasisBounds.width 2 2 :=
  signedNumerator_bound _ _ 2 (by decide +kernel) (by decide +kernel) i

example (i : Fin 2) (k : Fin 3) :
    (GameTheory.Math.IntegerDictionaryComputation.coefficients
      !![(1 : ℤ), 2; 2, 4] ![-1, 1] i k).natAbs <
        2 ^ GameTheory.Math.IntegerBasisBounds.width 2 2 :=
  GameTheory.Math.IntegerDictionaryComputation.coefficients_bound _ _ 2
    (by decide +kernel) (by decide +kernel) i k

example (i j : Fin 2) (k : Fin 3) :
    (GameTheory.Math.IntegerDictionaryComputation.coefficients
      !![(1 : ℤ), 2; 2, 4] ![-1, 1] i k *
      GameTheory.Math.IntegerDictionaryComputation.direction
        !![(1 : ℤ), 2; 2, 4] ![-1, 1] j).natAbs <
          2 ^ (2 * GameTheory.Math.IntegerBasisBounds.width 2 2) :=
  GameTheory.Math.IntegerDictionaryComputation.crossProduct_bound _ _ _ 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) i j k

end GameTheory.Tests.IntegerCramerComputation
