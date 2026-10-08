import GameTheory.Finite.BimatrixCertificate
import GameTheory.Core.BimatrixGame
import GameTheory.Math.Probability.Numerator

/-! Accepted rectangular integer certificates produce mixed Nash equilibria
for the canonical bimatrix game. Real-valued probability semantics are confined
to this correctness module. -/

noncomputable section

namespace GameTheory.Finite.BimatrixCertificate

open GameTheory.Math.Probability
open scoped BigOperators

/-- Valid numerator data define a Nash equilibrium of the two payoff matrices. -/
theorem isNash_of_valid {m n : ℕ} (A B : Fin m → Fin n → ℤ)
    (c : BimatrixCertificate m n) (hc : c.Valid A B) :
    IsNash (MatrixGame.form (Fin m) (Fin n)).mixed
      (euPreference (MatrixGame.bimatrixUtility
        (fun i j => (A i j : ℝ)) (fun i j => (B i j : ℝ))))
      (MatrixGame.mixedProfile
        (numeratorLaw c.rowWeights c.rowDenominator hc.1 hc.2.2.1)
        (numeratorLaw c.colWeights c.colDenominator hc.2.1 hc.2.2.2.1)) := by
  rcases hc with ⟨hdp, hdq, hsp, hsq, hr, hc⟩
  let p := numeratorLaw c.rowWeights c.rowDenominator hdp hsp
  let q := numeratorLaw c.colWeights c.colDenominator hdq hsq
  have er (i : Fin m) : expect q (fun j => (A i j : ℝ)) =
      (rowScore A c i : ℝ) / c.colDenominator := by
    rw [expect_numeratorLaw]
    congr 1
    simp only [rowScore, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have ec (j : Fin n) : expect p (fun i => (B i j : ℝ)) =
      (colScore B c j : ℝ) / c.rowDenominator := by
    rw [expect_numeratorLaw]
    congr 1
    simp only [colScore, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have vr : expect (bindPairLaw p (fun _ => q)) (fun x => (A x.1 x.2 : ℝ)) =
      (c.rowUtilityNumerator : ℝ) / c.colDenominator := by
    rw [expect_bindPairLaw_tower _ _ _ (payoffIntegrable_of_finite _ _)]
    apply expect_numeratorLaw_eq
    intro i hi
    rw [er, (hr i).2 hi]
  have vc : expect (bindPairLaw p (fun _ => q)) (fun x => (B x.1 x.2 : ℝ)) =
      (c.colUtilityNumerator : ℝ) / c.rowDenominator := by
    have hswap : expect (bindPairLaw p (fun _ => q)) (fun x => (B x.1 x.2 : ℝ)) =
        expect (bindPairLaw q (fun _ => p)) (fun x => (B x.2 x.1 : ℝ)) := by
      rw [← bindPairLaw_const_map_swap, expect_map]
      rfl
    rw [hswap, expect_bindPairLaw_tower _ _ _ (payoffIntegrable_of_finite _ _)]
    apply expect_numeratorLaw_eq
    intro j hj
    rw [ec, (hc j).2 hj]
  rw [MatrixGame.isNash_bimatrix_iff, vr, vc]
  constructor
  · intro i
    rw [er]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (hr i).1
  · intro j
    rw [ec]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (hc j).1

/-- Every valid certificate supplies ordinary PMF mixed strategies in equilibrium. -/
theorem hasNash_of_valid {m n : ℕ} (A B : Fin m → Fin n → ℤ)
    (c : BimatrixCertificate m n) (hc : c.Valid A B) :
    ∃ (p : PMF (Fin m)) (q : PMF (Fin n)),
      IsNash (MatrixGame.form (Fin m) (Fin n)).mixed
        (euPreference (MatrixGame.bimatrixUtility
          (fun i j => (A i j : ℝ)) (fun i j => (B i j : ℝ))))
        (MatrixGame.mixedProfile p q) :=
  ⟨_, _, isNash_of_valid A B c hc⟩

end GameTheory.Finite.BimatrixCertificate
