import GameTheory.Finite.BimatrixAffineGate
import GameTheory.Finite.BimatrixComparatorGate
import Mathlib.Algebra.BigOperators.Fin

/-! Accepted concrete equilibria exercise affine clipping and strict comparison
on both sides of the output range, including an interior fractional output. -/
namespace GameTheory.Tests.BimatrixAffineGate
open GameTheory.Finite GameTheory.Finite.BimatrixBlockGame
open GameTheory.Finite.BimatrixAffineGate

private def constantSignal (z : ℤ) : Fin 1 → Fin 2 → ℤ := fun _ _ => z

private def below : BimatrixCertificate 2 2 where
  rowWeights := ![1, 0]
  colWeights := ![0, 1]
  rowDenominator := 1
  colDenominator := 1
  rowUtilityNumerator := 12
  colUtilityNumerator := -8

private def interior : BimatrixCertificate 2 2 where
  rowWeights := ![1, 1]
  colWeights := ![1, 1]
  rowDenominator := 2
  colDenominator := 2
  rowUtilityNumerator := 22
  colUtilityNumerator := -18

private def above : BimatrixCertificate 2 2 where
  rowWeights := ![0, 1]
  colWeights := ![1, 0]
  rowDenominator := 1
  colDenominator := 1
  rowUtilityNumerator := 12
  colUtilityNumerator := -6

private theorem below_valid : below.Valid (rowPayoff (k := 1) 10 2)
    (columnPayoff (k := 1) 10 2 (constantSignal 0) (constantSignal 2)) := by decide
private theorem interior_valid : interior.Valid (rowPayoff (k := 1) 10 2)
    (columnPayoff (k := 1) 10 2 (constantSignal 1) (constantSignal 0)) := by decide
private theorem above_valid : above.Valid (rowPayoff (k := 1) 10 2)
    (columnPayoff (k := 1) 10 2 (constantSignal 4) (constantSignal 0)) := by decide

-- Invoke the all-equilibria theorem with actual accepted games and sufficient baseline scale.
example : value (k := 1) below 0 =
    max 0 (min (blockMass (k := 1) below.rowWeights below.rowDenominator 0)
      (target (k := 1) below 2 (constantSignal 0) (constantSignal 2) 0)) := by
  exact all_values_eq_clamp (k := 1) 10 2 4 (constantSignal 0) (constantSignal 2)
    below below_valid (by norm_num) (by norm_num)
    (by intros; norm_num [constantSignal]) (by intros; norm_num [constantSignal]) (by norm_num) 0

example : value (k := 1) interior 0 =
    max 0 (min (blockMass (k := 1) interior.rowWeights interior.rowDenominator 0)
      (target (k := 1) interior 2 (constantSignal 1) (constantSignal 0) 0)) := by
  exact all_values_eq_clamp (k := 1) 10 2 4 (constantSignal 1) (constantSignal 0)
    interior interior_valid (by norm_num) (by norm_num)
    (by intros; norm_num [constantSignal]) (by intros; norm_num [constantSignal]) (by norm_num) 0

example : value (k := 1) above 0 =
    max 0 (min (blockMass (k := 1) above.rowWeights above.rowDenominator 0)
      (target (k := 1) above 2 (constantSignal 4) (constantSignal 0) 0)) := by
  exact all_values_eq_clamp (k := 1) 10 2 4 (constantSignal 4) (constantSignal 0)
    above above_valid (by norm_num) (by norm_num)
    (by intros; norm_num [constantSignal]) (by intros; norm_num [constantSignal]) (by norm_num) 0

-- The computed targets lie below zero, inside the range, and above the total block capacity.
example : target (k := 1) below 2 (constantSignal 0) (constantSignal 2) 0 = -1 ∧
    value (k := 1) below 0 = 0 ∧
    target (k := 1) interior 2 (constantSignal 1) (constantSignal 0) 0 = (1 : ℚ) / 2 ∧
    value (k := 1) interior 0 = (1 : ℚ) / 2 ∧
    target (k := 1) above 2 (constantSignal 4) (constantSignal 0) 0 = 2 ∧
    value (k := 1) above 0 = 1 ∧
    blockMass (k := 1) above.rowWeights above.rowDenominator 0 = 1 := by
  norm_num [target, value, blockMass, constantSignal, below, interior, above,
    Fin.sum_univ_succ, finProdFinEquiv]

private def greater : BimatrixCertificate 2 2 where
  rowWeights := ![0, 1]
  colWeights := ![1, 0]
  rowDenominator := 1
  colDenominator := 1
  rowUtilityNumerator := 12
  colUtilityNumerator := -9

private def lesser : BimatrixCertificate 2 2 where
  rowWeights := ![1, 0]
  colWeights := ![0, 1]
  rowDenominator := 1
  colDenominator := 1
  rowUtilityNumerator := 12
  colUtilityNumerator := -9

private theorem greater_valid : greater.Valid (rowPayoff (k := 1) 10 2)
    (BimatrixComparatorGate.columnPayoff (k := 1) 10 (constantSignal 1) (constantSignal 0)) :=
  by decide
private theorem lesser_valid : lesser.Valid (rowPayoff (k := 1) 10 2)
    (BimatrixComparatorGate.columnPayoff (k := 1) 10 (constantSignal 0) (constantSignal 1)) :=
  by decide

example : auxiliaryValue (k := 1) greater 0 =
      blockMass (k := 1) greater.colWeights greater.colDenominator 0 ∧
    value (k := 1) greater 0 = blockMass (k := 1) greater.rowWeights greater.rowDenominator 0 := by
  apply (BimatrixComparatorGate.comparator (k := 1) 10 2 (constantSignal 1) (constantSignal 0)
    greater greater_valid (by norm_num) 0 ?_).1
  · norm_num [BimatrixComparatorGate.signal, constantSignal, greater, Fin.sum_univ_succ]
  · norm_num [blockMass, greater, Fin.sum_univ_succ, finProdFinEquiv]

example : auxiliaryValue (k := 1) lesser 0 = 0 ∧ value (k := 1) lesser 0 = 0 := by
  apply (BimatrixComparatorGate.comparator (k := 1) 10 2 (constantSignal 0) (constantSignal 1)
    lesser lesser_valid (by norm_num) 0 ?_).2
  · norm_num [BimatrixComparatorGate.signal, constantSignal, lesser, Fin.sum_univ_succ]
  · norm_num [blockMass, lesser, Fin.sum_univ_succ, finProdFinEquiv]

end GameTheory.Tests.BimatrixAffineGate
