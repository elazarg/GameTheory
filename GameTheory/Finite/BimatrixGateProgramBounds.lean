import GameTheory.Finite.BimatrixGateProgram
import GameTheory.Math.ClippedArithmetic

/-!
# Uniform mass and wire bounds for canonical game programs

Dominant matching payoffs place both block capacities near their uniform value, regardless of
which gate kinds the program uses. A wire occupies part of its row block, so its normalized
value is nonnegative and exceeds one by at most the common matching error. Clipping such a
wire to the unit interval introduces no larger error.
-/

namespace GameTheory.Finite.BimatrixGateProgramBounds
open BimatrixAffineGate BimatrixGateProgram BimatrixBlockGame
open scoped BigOperators
variable {k : ℕ}

/-- Matching-mass estimates apply to every accepted program, independently of gate kinds. -/
theorem blockMass_uniform (H C M : ℤ) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H C) (columnPayoff H C g))
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + C) < H) :
    (∀ i, 0 < blockMass c.rowWeights c.rowDenominator i ∧
      0 < blockMass c.colWeights c.colDenominator i) ∧
    ∀ i, |blockMass c.rowWeights c.rowDenominator i - 1 / (k : ℚ)| ≤
      (((M + C : ℤ) : ℚ) / H) ∧
      |blockMass c.colWeights c.colDenominator i - 1 / (k : ℚ)| ≤
      (((M + C : ℤ) : ℚ) / H) := by
  exact BimatrixBlockGame.blockMass_uniform H (M + C)
    (rowPerturbation C)
    (columnPerturbation C (positiveCoefficients C g) (negativeCoefficients g)) c hc
    (rowPerturbation_bounds C (M + C) hC (by linarith))
    (columnPerturbation_bounds C (M + C) _ _ hC
      (positiveCoefficients_bounds C M hC hM g hg)
      (negativeCoefficients_bounds C M hM g hg)) hscale

/-- Both normalized block capacities have the common game error bound. -/
theorem normalized_blockMass_error (H C M : ℤ) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H C) (columnPayoff H C g))
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + C) < H) (i : Fin k) :
    |(k : ℚ) * blockMass c.rowWeights c.rowDenominator i - 1| ≤
      (k : ℚ) * (((M + C : ℤ) : ℚ) / H) ∧
    |(k : ℚ) * blockMass c.colWeights c.colDenominator i - 1| ≤
      (k : ℚ) * (((M + C : ℤ) : ℚ) / H) := by
  have hm := blockMass_uniform H C M g c hc hC hM hg hscale
  have hk : (k : ℚ) ≠ 0 := by
    exact_mod_cast (show k ≠ 0 by have hi := i.isLt; omega)
  have hnorm (x : ℚ) (hx : |x - 1 / (k : ℚ)| ≤ (((M + C : ℤ) : ℚ) / H)) :
      |(k : ℚ) * x - 1| ≤ (k : ℚ) * (((M + C : ℤ) : ℚ) / H) := by
    have he : (k : ℚ) * x - 1 = (k : ℚ) * (x - 1 / (k : ℚ)) := by field_simp
    rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg k)
  exact ⟨hnorm _ (hm.2 i).1, hnorm _ (hm.2 i).2⟩

/-- Every normalized wire is nonnegative and exceeds one by at most the game error. -/
theorem normalized_value_bounds (H C M : ℤ) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H C) (columnPayoff H C g))
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + C) < H) (i : Fin k) :
    0 ≤ (k : ℚ) * value c i ∧ (k : ℚ) * value c i ≤
      1 + (k : ℚ) * (((M + C : ℤ) : ℚ) / H) := by
  have hm := (normalized_blockMass_error H C M g c hc hC hM hg hscale i).1
  have hv0 : 0 ≤ value c i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hv : value c i ≤ blockMass c.rowWeights c.rowDenominator i := by
    rw [value, blockMass_pair]
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_left (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg k)
  rw [abs_le] at hm
  exact ⟨mul_nonneg (Nat.cast_nonneg k) hv0, by linarith [hm.2]⟩

/-- Clipping any normalized wire introduces at most the matching-block error. -/
theorem normalized_value_clipping_error (H C M : ℤ) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H C) (columnPayoff H C g))
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + C) < H) (i : Fin k) :
    |(k : ℚ) * value c i - max 0 (min 1 ((k : ℚ) * value c i))| ≤
      (k : ℚ) * (((M + C : ℤ) : ℚ) / H) := by
  have hv := normalized_value_bounds H C M g c hc hC hM hg hscale i
  have hm := (normalized_blockMass_error H C M g c hc hC hM hg hscale i).1
  have hδ : 0 ≤ (k : ℚ) * (((M + C : ℤ) : ℚ) / H) := (abs_nonneg _).trans hm
  by_cases h : (k : ℚ) * value c i ≤ 1
  · rw [GameTheory.Math.unitClamp_eq_self hv.1 h, sub_self, abs_zero]
    exact hδ
  · have ht : 1 ≤ (k : ℚ) * value c i := le_of_not_ge h
    rw [min_eq_left ht, max_eq_right (by norm_num : (0 : ℚ) ≤ 1),
      abs_of_nonneg (sub_nonneg.mpr ht)]
    linarith [hv.2]

end GameTheory.Finite.BimatrixGateProgramBounds
