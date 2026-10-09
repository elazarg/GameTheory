import GameTheory.Finite.BimatrixGateProgram
import GameTheory.Math.ClippedArithmetic

/-! One accepted game exercises affine and comparator outputs simultaneously,
with nonuniform block masses and zero weights on individual actions. -/
namespace GameTheory.Tests.BimatrixGateProgram
open GameTheory.Finite GameTheory.Finite.BimatrixBlockGame
open GameTheory.Finite.BimatrixGateProgram

private def gates : Fin 2 → Gate 2 := fun i =>
  if i = 0 then ⟨fun _ => -2, .affine⟩ else ⟨fun _ => 2, .comparator⟩

private def certificate : BimatrixCertificate 4 4 where
  rowWeights := ![4, 0, 0, 5]
  colWeights := ![0, 1, 1, 0]
  rowDenominator := 9
  colDenominator := 2
  rowUtilityNumerator := 12
  colUtilityNumerator := -22

private theorem accepted : certificate.Valid (BimatrixAffineGate.rowPayoff (k := 2) 10 2)
    (columnPayoff 10 2 gates) := by decide +kernel


example : BimatrixAffineGate.value (k := 2) certificate 0 = max 0
    (min (blockMass (k := 2) certificate.rowWeights certificate.rowDenominator 0)
      (signal certificate 2 gates 0)) := by
  have equations := all_gate_equations 10 2 2 gates certificate accepted
    (by norm_num) (by norm_num)
    (by intro i r; unfold gates; split_ifs <;> norm_num) (by norm_num)

  exact (equations 0).1 (by decide +kernel)

example : BimatrixAffineGate.value (k := 2) certificate 1 =
    blockMass (k := 2) certificate.rowWeights certificate.rowDenominator 1 := by
  have equations := all_gate_equations 10 2 2 gates certificate accepted
    (by norm_num) (by norm_num)
    (by intro i r; unfold gates; split_ifs <;> norm_num) (by norm_num)

  exact ((equations 1).2 (by decide +kernel)).1 (by decide +kernel)

example : blockMass (k := 2) certificate.rowWeights certificate.rowDenominator 0 =
    (4 : ℚ) / 9 ∧
    blockMass (k := 2) certificate.rowWeights certificate.rowDenominator 1 = (5 : ℚ) / 9 := by
  decide +kernel

-- A nonnegative signal above one still computes the exact minimum of a unit weight.
example : min (1 / 2 : ℚ) 2 =
    max 0 (min 1 (1 / 2 - max 0 (min 1 (1 / 2 - 2)))) := by
  exact GameTheory.Math.min_eq_clipped_sub (by norm_num) (by norm_num) (by norm_num)

-- Perturbed signals above one obey the strengthened two-step error estimate.
example : |(3 / 5 : ℚ) - min (1 / 2) 2| ≤ 2 / 5 := by
  have h := GameTheory.Math.clippedSub_min_error
    (1 / 2 : ℚ) 2 (3 / 5) (21 / 10) (1 / 20) (3 / 5) (1 / 10) (1 / 10) (1 / 20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1; norm_num

end GameTheory.Tests.BimatrixGateProgram
