import GameTheory.Finite.BimatrixCertificateCompleteness
import Mathlib.Data.Fin.VecNotation

/-! Rectangular, signed-payoff controls and a genuinely mixed equilibrium test
exercise the exact certificate verifier and its canonical correctness theorem. -/

namespace GameTheory.Tests.BimatrixCertificate

open GameTheory.Finite
open GameTheory.Math.Probability

private def negativeRow : Fin 1 → Fin 2 → ℤ := fun _ => ![-2, -3]
private def negativeColumn : Fin 1 → Fin 2 → ℤ := fun _ => ![-4, -5]
private def negativePure : BimatrixCertificate 1 2 :=
  ⟨![1], ![1, 0], 1, 1, -2, -4⟩

-- Independent matrices and negative utility numerators are accepted.
example : verifyBimatrixCertificate negativeRow negativeColumn negativePure = true := by
  decide

-- Probability numerators must sum to their advertised denominator.
example : verifyBimatrixCertificate negativeRow negativeColumn
    { negativePure with colDenominator := 2 } = false := by decide

-- A supported action must attain its claimed best-response utility.
example : verifyBimatrixCertificate negativeRow negativeColumn
    { negativePure with colUtilityNumerator := -3 } = false := by decide

-- Giving all mass to the worse column cannot certify an equilibrium, even
-- when both utility numerators are its exact realized payoffs.
example : verifyBimatrixCertificate negativeRow negativeColumn
    { negativePure with
      colWeights := ![0, 1]
      rowUtilityNumerator := -3
      colUtilityNumerator := -5 } = false := by decide

private def matchingRow : Fin 2 → Fin 2 → ℤ := ![![1, -1], ![-1, 1]]
private def matchingColumn : Fin 2 → Fin 2 → ℤ := ![![-1, 1], ![1, -1]]
private def matchingMixed : BimatrixCertificate 2 2 :=
  ⟨![1, 1], ![1, 1], 2, 2, 0, 0⟩

example : verifyBimatrixCertificate matchingRow matchingColumn matchingMixed = true := by
  decide

-- Bounded witness completeness also applies to independent negative rectangular tables.
example : ∃ c : BimatrixCertificate 1 2, c.Valid negativeRow negativeColumn ∧
    c.FitsWidth (GameTheory.bimatrixCertificateWidth 1 2 3) :=
  (GameTheory.bimatrix_nash_exists_iff_bounded_certificate
    negativeRow negativeColumn 3 (by decide) (by decide)).mp
    (negativePure.hasNash_of_valid negativeRow negativeColumn (by decide))

-- The executable certificate gives Nash for the ordinary independently mixed
-- matrix game, rather than a separate certificate-specific equilibrium notion.
noncomputable example :
    GameTheory.IsNash (GameTheory.MatrixGame.form (Fin 2) (Fin 2)).mixed
      (GameTheory.euPreference (GameTheory.MatrixGame.bimatrixUtility
        (fun i j => (matchingRow i j : ℝ)) (fun i j => (matchingColumn i j : ℝ))))
      (GameTheory.MatrixGame.mixedProfile
        (numeratorLaw matchingMixed.rowWeights matchingMixed.rowDenominator
          (by decide) (by decide))
        (numeratorLaw matchingMixed.colWeights matchingMixed.colDenominator
          (by decide) (by decide))) :=
  matchingMixed.isNash_of_valid matchingRow matchingColumn (by decide)

end GameTheory.Tests.BimatrixCertificate
