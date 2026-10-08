import GameTheory.Finite.BimatrixCertificateShift
import Mathlib.Data.Fin.VecNotation

/-! Exact payoff-shift controls include negative rectangular payoffs and a
fully degenerate game with a genuinely mixed certificate. -/

namespace GameTheory.Tests.BimatrixCertificateShift

open GameTheory.Finite

private def negativeRow : Fin 1 → Fin 2 → ℤ := fun _ => ![-2, -3]
private def negativeColumn : Fin 1 → Fin 2 → ℤ := fun _ => ![-4, -5]
private def negativePure : BimatrixCertificate 1 2 :=
  ⟨![1], ![1, 0], 1, 1, -2, -4⟩

example : verifyBimatrixCertificate
    (fun i j => negativeRow i j + 9) (fun i j => negativeColumn i j + 9)
    (negativePure.shiftPayoffs 9 9) = true := by decide

example : (negativePure.shiftPayoffs 9 9).rowUtilityNumerator = 7 ∧
    (negativePure.shiftPayoffs 9 9).colUtilityNumerator = 5 := by decide

-- Retaining an old negative utility after shifting payoffs fails verification.
example : verifyBimatrixCertificate
    (fun i j => negativeRow i j + 9) (fun i j => negativeColumn i j + 9)
    { negativePure.shiftPayoffs 9 9 with colUtilityNumerator := -4 } = false := by decide

private def zeroPayoff : Fin 2 → Fin 2 → ℤ := fun _ _ => 0
private def degenerateMixed : BimatrixCertificate 2 2 :=
  ⟨![1, 2], ![2, 3], 3, 5, 0, 0⟩

example : verifyBimatrixCertificate zeroPayoff zeroPayoff degenerateMixed = true := by decide

-- Every action remains tied after shifting; independent denominators are preserved.
example : verifyBimatrixCertificate (fun _ _ => 7) (fun _ _ => 11)
    (degenerateMixed.shiftPayoffs 7 11) = true := by decide

example : (degenerateMixed.shiftPayoffs 7 11).rowUtilityNumerator = 35 ∧
    (degenerateMixed.shiftPayoffs 7 11).colUtilityNumerator = 33 := by decide

example : (degenerateMixed.shiftPayoffs 7 11).shiftPayoffs (-7) (-11) =
    degenerateMixed := BimatrixCertificate.shiftPayoffs_neg_cancel _ _ _

example : 0 < (-8 : ℤ) + (2 ^ 3 + 1) := payoff_add_pow_positive (-8) 3 (by decide)

example : ((8 : ℤ) + (2 ^ 3 + 1)).natAbs < 2 ^ (3 + 2) :=
  payoff_add_pow_bound 8 3 (by decide)

example : ((1 : ℤ) + (2 ^ 0 + 1)).natAbs < 2 ^ (0 + 2) :=
  payoff_add_pow_bound 1 0 (by decide)

end GameTheory.Tests.BimatrixCertificateShift
