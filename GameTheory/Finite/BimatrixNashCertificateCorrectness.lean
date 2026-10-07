import GameTheory.Finite.BimatrixNashCertificate
import GameTheory.Finite.BimatrixTableProblem
import GameTheory.Math.Probability.Numerator

/-! Verified integer numerator certificates yield ordinary PMF mixed strategies
and the canonical payoff-constrained Nash predicate. -/

noncomputable section

namespace GameTheory.Finite

open GameTheory.Math.Probability
open scoped BigOperators

namespace NumeratorCertificate

/-- An accepted numerator certificate gives a canonical symmetric bimatrix
equilibrium with both expected payoffs at least one. -/
theorem hasNash_of_valid {q : ℕ} (A : Fin q → Fin q → ℤ)
    (c : NumeratorCertificate q) (hc : c.Valid A) :
    (MatrixGame.bimatrixGame (fun i j => (A i j : ℝ))
      (fun i j => (A j i : ℝ))).HasNashWithPayoffAtLeast (fun _ => 1) := by
  rcases hc with ⟨hdp, hdq, hsp, hsq, hU, hV, hr, hc⟩
  let p := numeratorLaw c.rowWeights c.rowDenominator hdp hsp
  let r := numeratorLaw c.colWeights c.colDenominator hdq hsq
  have er (i : Fin q) : expect r (fun j => (A i j : ℝ)) =
      (rowScore A c i : ℝ) / c.colDenominator := by
    rw [expect_numeratorLaw]
    congr 1
    simp only [rowScore, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have ec (j : Fin q) : expect p (fun i => (A j i : ℝ)) =
      (colScore A c j : ℝ) / c.rowDenominator := by
    rw [expect_numeratorLaw]
    congr 1
    simp only [colScore, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have vr : expect (bindPairLaw p (fun _ => r)) (fun x => (A x.1 x.2 : ℝ)) =
      (c.rowUtilityNumerator : ℝ) / c.colDenominator := by
    rw [expect_bindPairLaw_tower _ _ _ (payoffIntegrable_of_finite _ _)]
    apply expect_numeratorLaw_eq
    intro i hi
    rw [er, (hr i).2 hi]
    simp
  have vc : expect (bindPairLaw p (fun _ => r)) (fun x => (A x.2 x.1 : ℝ)) =
      (c.colUtilityNumerator : ℝ) / c.rowDenominator := by
    have hswap : expect (bindPairLaw p (fun _ => r)) (fun x => (A x.2 x.1 : ℝ)) =
        expect (bindPairLaw r (fun _ => p)) (fun x => (A x.1 x.2 : ℝ)) := by
      rw [← bindPairLaw_const_map_swap, expect_map]
      rfl
    rw [hswap, expect_bindPairLaw_tower _ _ _ (payoffIntegrable_of_finite _ _)]
    apply expect_numeratorLaw_eq
    intro j hj
    rw [ec, (hc j).2 hj]
    simp
  apply MatrixGame.hasNashWithPayoffAtLeast_iff _ _ |>.mpr
  refine ⟨p, r, ?_, ?_, ?_⟩
  · rw [MatrixGame.isNash_bimatrix_iff, vr, vc]
    constructor
    · intro i
      rw [er]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast (hr i).1
    · intro j
      rw [ec]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast (hc j).1
  · rw [vr]
    apply (le_div_iff₀ (by exact_mod_cast hdq)).mpr
    simpa using (show (c.colDenominator : ℝ) ≤ c.rowUtilityNumerator by exact_mod_cast hU)
  · rw [vc]
    apply (le_div_iff₀ (by exact_mod_cast hdp)).mpr
    simpa using (show (c.rowDenominator : ℝ) ≤ c.colUtilityNumerator by exact_mod_cast hV)

end NumeratorCertificate

/-- Acceptance for the actual decoded integer table implies membership in the
payoff-constrained equilibrium language. -/
theorem mem_unitPayoffLanguage_of_verify (input : List Bool)
    (c : NumeratorCertificate (BimatrixTable.decodeDimension input))
    (hc : verifyNashNumerators
      (fun i j => BimatrixTable.decodedPayoff input i j) c = true) :
    input ∈ BimatrixTable.unitPayoffLanguage := by
  exact c.hasNash_of_valid _ ((verifyNashNumerators_eq_true_iff _ c).mp hc)

end GameTheory.Finite
