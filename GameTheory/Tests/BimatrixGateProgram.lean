import GameTheory.Finite.BimatrixGateProgram

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
end GameTheory.Tests.BimatrixGateProgram
