import GameTheory.Math.IntegerDictionaryComputation
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Controls for executable symbolic ratio scans and signed common-scale dictionaries. -/

namespace GameTheory.Tests.IntegerRatioSelection
open GameTheory.Math

-- Equal ordinary ratios are distinguished by later perturbation coefficients.
example : IntegerRatioSelection.select ![![(1 : ℤ), 1, 0], ![1, 0, 1]] ![1, 1] = some 1 :=
  by decide +kernel

-- Exact ties keep the earliest row, even without a uniqueness premise.
example : IntegerRatioSelection.select ![![(1 : ℤ), 0], ![1, 0]] ![1, 1] = some 0 :=
  by decide +kernel

-- Zero and negative directions are excluded regardless of their numerators.
example : IntegerRatioSelection.select ![![(-100 : ℤ)], ![-200], ![3]] ![0, -1, 2] =
    some 2 := by decide +kernel

example : IntegerRatioSelection.select ![![(1 : ℤ)], ![2]] ![0, -1] = none :=
  by decide +kernel

example : IntegerRatioSelection.select (fun _ : Fin 0 => fun _ : Fin 2 => (0 : ℤ))
    (fun _ => 0) = none := by decide +kernel

example : IntegerRatioSelection.select (fun _ : Fin 2 => fun _ : Fin 0 => (0 : ℤ))
    ![1, 2] = some 0 := by decide +kernel

example : IntegerRatioSelection.select ![![(-3 : ℤ), 0], ![-5, 1]] ![1, 2] = some 0 :=
  by decide +kernel

-- Negative determinant, negative direction, and positive direction all survive encoding.
example : IntegerDictionaryComputation.direction !![(0 : ℤ), 6; 4, 0] ![6, -4] =
    ![-24, 24] := by decide +kernel

example : IntegerDictionaryComputation.coefficients !![(0 : ℤ), 6; 4, 0] ![1, 1] =
    !![6, 0, 6; 4, 4, 0] := by decide +kernel

example : IntegerDictionaryComputation.select !![(0 : ℤ), 6; 4, 0] ![1, 1] ![6, -4] =
    some 1 := by decide +kernel

example : IntegerDictionaryComputation.select !![(1 : ℤ), 2; 2, 4] ![1, 1] ![1, 1] =
    none := by decide +kernel

end GameTheory.Tests.IntegerRatioSelection
