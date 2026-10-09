import GameTheory.Finite.BimatrixGateProgram

/-! Affine comparator-program blocks evaluate integer linear combinations of paired inputs.
The normalized outputs approximate unit-clipped arithmetic expressions, with error controlled
by the common matching-block scale. -/

namespace GameTheory.Finite.BimatrixArithmeticGate
open BimatrixCertificate BimatrixAffineGate BimatrixGateProgram
open scoped BigOperators
variable {k : ℕ}

/-- A shared constant offset and one coefficient for each positive input action. -/
def coefficients (a : Fin k → ℤ) (b : ℤ) (r : Fin (k * 2)) : ℤ :=
  (if (finProdFinEquiv.symm r).2 = 1 then a (finProdFinEquiv.symm r).1 else 0) + b

/-- An affine gate with aggregated signed input coefficients. -/
def gate (a : Fin k → ℤ) (b : ℤ) : Gate k := ⟨coefficients a b, .affine⟩

/-- The positive action carries its input coefficient and constant offset. -/
theorem coefficients_one (a : Fin k → ℤ) (b : ℤ) (j : Fin k) :
    coefficients a b (finProdFinEquiv (j, 1)) = a j + b := by
  simp [coefficients]

/-- The zero action carries only the constant offset. -/
theorem coefficients_zero (a : Fin k → ℤ) (b : ℤ) (j : Fin k) :
    coefficients a b (finProdFinEquiv (j, 0)) = b := by
  simp [coefficients]

/-- Input coefficient bounds control every aggregated action coefficient. -/
theorem coefficients_bound (a : Fin k → ℤ) (b A : ℤ)
    (ha : ∀ j, |a j| ≤ A) (r : Fin (k * 2)) :
    |coefficients a b r| ≤ A + |b| := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (ha (finProdFinEquiv.symm r).1)
  unfold coefficients
  split_ifs
  · exact (abs_add_le _ _).trans (add_le_add (ha _) le_rfl)
  · simpa only [zero_add] using add_le_add hA (le_refl |b|)

/-- Row normalization turns the signed signal into the intended affine expression. -/
theorem signal_eq (a : Fin k → ℤ) (b C : ℤ) (hC : 0 < C)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hd : 0 < c.rowDenominator) (hs : (∑ r, c.rowWeights r) = c.rowDenominator)
    (g : Fin k → Gate k) (i : Fin k) (hi : g i = gate a b) :
    (k : ℚ) * signal c C g i =
      (∑ j, (a j : ℚ) / C * ((k : ℚ) * value c j)) + (k : ℚ) * b / C := by
  have hinput : (∑ r : Fin (k * 2),
      (if (finProdFinEquiv.symm r).2 = 1 then a (finProdFinEquiv.symm r).1 else 0) *
        (c.rowWeights r : ℤ)) =
      ∑ j, a j * (c.rowWeights (finProdFinEquiv (j, 1)) : ℤ) := by
    rw [← Equiv.sum_comp finProdFinEquiv]
    rw [Fintype.sum_prod_type]
    simp
  have hsum : (∑ r, (g i).coefficients r * (c.rowWeights r : ℤ)) =
      (∑ j, a j * (c.rowWeights (finProdFinEquiv (j, 1)) : ℤ)) + b * c.rowDenominator := by
    simp only [hi, gate, coefficients, add_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rw [hinput, ← Nat.cast_sum, hs]
  unfold signal value
  rw [hsum]
  push_cast
  rw [add_div, mul_add, Finset.sum_div, Finset.mul_sum]
  have hCq : (C : ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  have hdq : (c.rowDenominator : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    field_simp

  · field_simp


/-- Every valid certificate approximates the unit-clipped affine expression. -/
theorem normalized_value_error (H C M : ℤ) (a : Fin k → ℤ) (b : ℤ)
    (g : Fin k → Gate k) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H C) (columnPayoff H C g))
    (hC : 0 < C) (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + C) < H) (i : Fin k) (hi : g i = gate a b) :
    |(k : ℚ) * value c i - max 0 (min 1
      ((∑ j, (a j : ℚ) / C * ((k : ℚ) * value c j)) + (k : ℚ) * b / C))| ≤
      (k : ℚ) * (((M + C : ℤ) : ℚ) / H) := by
  have he := BimatrixAffineGate.normalized_value_error H C (M + C)
    (positiveCoefficients C g) (negativeCoefficients g) c hc hC (by linarith)
    (positiveCoefficients_bounds C M hC.le hM g hg)
    (negativeCoefficients_bounds C M hM g hg) hscale i
  rw [target_affine c C g i (by simp [hi, gate]),
    signal_eq a b C hC c hc.1 hc.2.2.1 g i hi] at he
  exact he

end GameTheory.Finite.BimatrixArithmeticGate
