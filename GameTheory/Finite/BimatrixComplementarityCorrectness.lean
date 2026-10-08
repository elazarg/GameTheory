import GameTheory.Finite.BimatrixComplementarity
import GameTheory.Finite.BimatrixCertificateShift
import GameTheory.Finite.BimatrixCertificateCorrectness

/-! Nonzero complementary points decode to the canonical mixed Nash semantics.
Payoff shifts support signed games; positivity is used only to scale Nash
certificates back into complementary coordinates. -/

namespace GameTheory.Finite

open scoped BigOperators
open GameTheory.Math.LinearComplementarity

/-- Positive certified utilities permit the complementary scaling, without
requiring a unique best response or strictly positive probability weights. -/
theorem complementaryNashCertificate_of_positive_valid {m n : ℕ}
    (A B : Fin m → Fin n → ℤ) (c : BimatrixCertificate m n)
    (hc : c.Valid A B) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    complementaryNashCertificate c.rowWeights c.colWeights
      c.colUtilityNumerator.toNat c.rowUtilityNumerator.toNat = c := by
  have hr := c.positive_rowUtilityNumerator A B hc hA
  have hs := c.positive_colUtilityNumerator A B hc hB
  cases c
  simp only [complementaryNashCertificate]
  congr
  · exact hc.2.2.1
  · exact hc.2.2.2.1
  · exact Int.toNat_of_nonneg (le_of_lt hr)
  · exact Int.toNat_of_nonneg (le_of_lt hs)

/-- A positive-payoff Nash certificate gives a nonzero complementary solution. -/
theorem BimatrixCertificate.complementarySolution_of_valid {m n : ℕ}
    (A B : Fin m → Fin n → ℤ) (c : BimatrixCertificate m n)
    (hc : c.Valid A B) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    IsSolution (fun _ => 1) (bimatrixComplementaryMatrix A B)
      (bimatrixComplementaryPoint c.rowWeights c.colWeights
        c.colUtilityNumerator.toNat c.rowUtilityNumerator.toNat) ∧
      bimatrixComplementaryPoint c.rowWeights c.colWeights
        c.colUtilityNumerator.toNat c.rowUtilityNumerator.toNat ≠ 0 := by
  have hr := c.positive_rowUtilityNumerator A B hc hA
  have hs := c.positive_colUtilityNumerator A B hc hB
  apply (complementaryNashCertificate_valid_iff A B c.rowWeights c.colWeights
    c.colUtilityNumerator.toNat c.rowUtilityNumerator.toNat
    (by omega) (by omega)).mp
  rwa [complementaryNashCertificate_of_positive_valid A B c hc hA hB]

/-- Undo payoff shifts in the certificate decoded from a nonzero solution. -/
theorem unshiftedComplementaryCertificate_valid {m n : ℕ}
    (A B : Fin m → Fin n → ℤ) (a b : ℤ) (r : Fin m → ℕ) (s : Fin n → ℕ)
    (Dx Dy : ℕ) (hDx : 0 < Dx) (hDy : 0 < Dy)
    (hsol : IsSolution (fun _ => 1)
      (bimatrixComplementaryMatrix (fun i j => A i j + a) (fun i j => B i j + b))
      (bimatrixComplementaryPoint r s Dx Dy))
    (hne : bimatrixComplementaryPoint r s Dx Dy ≠ 0) :
    ((complementaryNashCertificate r s Dx Dy).shiftPayoffs (-a) (-b)).Valid A B := by
  apply (BimatrixCertificate.valid_unshiftPayoffs_iff A B _ a b).mpr
  exact (complementaryNashCertificate_valid_iff _ _ r s Dx Dy hDx hDy).mpr ⟨hsol, hne⟩

/-- Nonzero complementary solutions yield canonical PMF equilibria of the
original signed payoff tables. -/
theorem hasNash_of_shifted_complementarySolution {m n : ℕ}
    (A B : Fin m → Fin n → ℤ) (a b : ℤ) (r : Fin m → ℕ) (s : Fin n → ℕ)
    (Dx Dy : ℕ) (hDx : 0 < Dx) (hDy : 0 < Dy)
    (hsol : IsSolution (fun _ => 1)
      (bimatrixComplementaryMatrix (fun i j => A i j + a) (fun i j => B i j + b))
      (bimatrixComplementaryPoint r s Dx Dy))
    (hne : bimatrixComplementaryPoint r s Dx Dy ≠ 0) :
    ∃ (p : PMF (Fin m)) (q : PMF (Fin n)),
      IsNash (MatrixGame.form (Fin m) (Fin n)).mixed
        (euPreference (MatrixGame.bimatrixUtility
          (fun i j => (A i j : ℝ)) (fun i j => (B i j : ℝ))))
        (MatrixGame.mixedProfile p q) :=
  BimatrixCertificate.hasNash_of_valid A B _
    (unshiftedComplementaryCertificate_valid A B a b r s Dx Dy hDx hDy hsol hne)

end GameTheory.Finite
