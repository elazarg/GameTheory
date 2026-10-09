import GameTheory.Finite.BimatrixGateProgram
import GameTheory.Math.BooleanThreshold

/-! Boolean gates specialize the common paired-action comparator program.
Aggregated integer coefficients support aliased inputs, and normalized signals have
strict Boolean signs even when their scalar input representations have small errors. -/
namespace GameTheory.Finite.BimatrixBooleanGate
open BimatrixCertificate BimatrixBlockGame BimatrixAffineGate BimatrixGateProgram
open scoped BigOperators
variable {k : ℕ}

/-- Aggregated threshold coefficients retain both contributions when inputs coincide. -/
def binaryCoefficients (a b : Fin k) (threshold : ℤ) (r : Fin (k * 2)) : ℤ :=
  2 * (k : ℤ) * ((if r = finProdFinEquiv (a, 1) then 1 else 0) +
    (if r = finProdFinEquiv (b, 1) then 1 else 0)) - threshold

/-- A strict-sign comparator implements conjunction on approximately Boolean inputs. -/
def andGate (a b : Fin k) : Gate k := ⟨binaryCoefficients a b 3, .comparator⟩
/-- A strict-sign comparator implements disjunction on approximately Boolean inputs. -/
def orGate (a b : Fin k) : Gate k := ⟨binaryCoefficients a b 1, .comparator⟩
/-- A strict-sign comparator implements negation on an approximately Boolean input. -/
def notGate (a : Fin k) : Gate k :=
  ⟨fun r => 1 - 2 * (k : ℤ) * (if r = finProdFinEquiv (a, 1) then 1 else 0),
    .comparator⟩

/-- The normalized two-input signal is the sum of normalized inputs minus its threshold. -/
theorem signal_binary (c : BimatrixCertificate (k * 2) (k * 2))
    (hk : 0 < k) (hd : 0 < c.rowDenominator)
    (hs : (∑ r, c.rowWeights r) = c.rowDenominator)
    (g : Fin k → Gate k) (i a b : Fin k) (t : ℤ)
    (hi : (g i).coefficients = binaryCoefficients a b t) :
    (k : ℚ) * signal c (2 * (k : ℤ)) g i =
      (k : ℚ) * value c a + (k : ℚ) * value c b - (t : ℚ) / 2 := by
  have hsum : (∑ r, (g i).coefficients r * (c.rowWeights r : ℤ)) =
      2 * (k : ℤ) * ((c.rowWeights (finProdFinEquiv (a, 1)) : ℤ) +
        c.rowWeights (finProdFinEquiv (b, 1))) - t * c.rowDenominator := by
    simp only [hi, binaryCoefficients, sub_mul, mul_assoc, add_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [ite_mul, ← Nat.cast_sum, hs]
  unfold signal value
  rw [hsum]
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hdq : (c.rowDenominator : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp


/-- The normalized negation signal subtracts its input from one half. -/
theorem signal_not (c : BimatrixCertificate (k * 2) (k * 2))
    (hk : 0 < k) (hd : 0 < c.rowDenominator)
    (hs : (∑ r, c.rowWeights r) = c.rowDenominator)
    (g : Fin k → Gate k) (i a : Fin k) (hi : g i = notGate a) :
    (k : ℚ) * signal c (2 * (k : ℤ)) g i = 1 / 2 - (k : ℚ) * value c a := by
  have hsum : (∑ r, (g i).coefficients r * (c.rowWeights r : ℤ)) =
      (c.rowDenominator : ℤ) - 2 * (k : ℤ) *
        c.rowWeights (finProdFinEquiv (a, 1)) := by
    simp only [hi, notGate, sub_mul, one_mul, mul_assoc,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [ite_mul, ← Nat.cast_sum, hs]
  unfold signal value
  rw [hsum]
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hdq : (c.rowDenominator : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp

private theorem value_of_sign (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (i : Fin k) (hi : (g i).kind = .comparator) (bit : Bool)
    (hsign : (0 < (k : ℚ) * signal c (2 * (k : ℤ)) g i ↔ bit = true) ∧
      ((k : ℚ) * signal c (2 * (k : ℤ)) g i < 0 ↔ bit = false)) :
    value c i = if bit then blockMass c.rowWeights c.rowDenominator i else 0 := by
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hk
  have he := (all_gate_equations H (2 * (k : ℤ)) M g c hc hC hM hg hscale i).2 hi
  have hkq : (0 : ℚ) < k := Nat.cast_pos.mpr hk
  cases bit
  · simp only [Bool.false_eq_true, ite_false]
    apply he.2
    have hn := hsign.2.mpr rfl
    nlinarith
  · simp only [ite_true]
    exact he.1 ((mul_pos_iff_of_pos_left hkq).mp (hsign.1.mpr rfl))

/-- Every valid certificate places the conjunction output at its full capacity or zero. -/
theorem andGate_value (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (i a b : Fin k) (hi : g i = andGate a b) (ba bb : Bool) (ε : ℚ)
    (ha : |(k : ℚ) * value c a - (if ba then 1 else 0)| ≤ ε)
    (hb : |(k : ℚ) * value c b - (if bb then 1 else 0)| ≤ ε) (hε : ε < 1 / 4) :
    value c i = if ba && bb then blockMass c.rowWeights c.rowDenominator i else 0 := by
  apply value_of_sign H M hk g c hc hM hg hscale i (by simp [hi, andGate])
  rw [signal_binary c hk hc.1 hc.2.2.1 g i a b 3 (by simp [hi, andGate])]
  exact GameTheory.Math.booleanThreshold_and ba bb _ _ ε ha hb hε

/-- Every valid certificate places the disjunction output at its full capacity or zero. -/
theorem orGate_value (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (i a b : Fin k) (hi : g i = orGate a b) (ba bb : Bool) (ε : ℚ)
    (ha : |(k : ℚ) * value c a - (if ba then 1 else 0)| ≤ ε)
    (hb : |(k : ℚ) * value c b - (if bb then 1 else 0)| ≤ ε) (hε : ε < 1 / 4) :
    value c i = if ba || bb then blockMass c.rowWeights c.rowDenominator i else 0 := by
  apply value_of_sign H M hk g c hc hM hg hscale i (by simp [hi, orGate])
  rw [signal_binary c hk hc.1 hc.2.2.1 g i a b 1 (by simp [hi, orGate])]
  exact GameTheory.Math.booleanThreshold_or ba bb _ _ ε ha hb hε

/-- Every valid certificate places the negated output at its full capacity or zero. -/
theorem notGate_value (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (i a : Fin k) (hi : g i = notGate a) (ba : Bool) (ε : ℚ)
    (ha : |(k : ℚ) * value c a - (if ba then 1 else 0)| ≤ ε) (hε : ε < 1 / 4) :
    value c i = if !ba then blockMass c.rowWeights c.rowDenominator i else 0 := by
  apply value_of_sign H M hk g c hc hM hg hscale i (by simp [hi, notGate])
  rw [signal_not c hk hc.1 hc.2.2.1 g i a hi]
  exact GameTheory.Math.booleanThreshold_not ba _ ε ha hε

/-- The bound counts both inputs, including repeated inputs. -/
theorem binaryCoefficients_bound (a b : Fin k) (t : ℤ) (r : Fin (k * 2)) :
    |binaryCoefficients a b t r| ≤ 4 * (k : ℤ) + |t| := by
  have hk : 0 ≤ (k : ℤ) := Nat.cast_nonneg k
  have ht := abs_le.mp (le_refl |t|)
  unfold binaryCoefficients
  split_ifs <;> (try simp only [add_zero, zero_add, mul_zero, mul_one]) <;>
    rw [abs_le] <;> constructor <;> nlinarith

/-- A uniform coefficient bound for conjunction gates. -/
theorem andGate_coefficients_bound (a b : Fin k) (r : Fin (k * 2)) :
    |(andGate a b).coefficients r| ≤ 4 * (k : ℤ) + 3 := by
  exact binaryCoefficients_bound a b 3 r

/-- A uniform coefficient bound for disjunction gates. -/
theorem orGate_coefficients_bound (a b : Fin k) (r : Fin (k * 2)) :
    |(orGate a b).coefficients r| ≤ 4 * (k : ℤ) + 1 := by
  exact binaryCoefficients_bound a b 1 r

/-- A uniform coefficient bound for negation gates. -/
theorem notGate_coefficients_bound (a : Fin k) (r : Fin (k * 2)) :
    |(notGate a).coefficients r| ≤ 2 * (k : ℤ) + 1 := by
  have hk : 0 ≤ (k : ℤ) := Nat.cast_nonneg k
  change |1 - 2 * (k : ℤ) * (if r = finProdFinEquiv (a, 1) then 1 else 0)| ≤ _
  split_ifs <;> simp only [mul_zero, mul_one] <;>
    rw [abs_le] <;> constructor <;> nlinarith

/-- A saturated Boolean output has only the matching-block normalization error. -/
theorem normalized_output_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (i : Fin k) (bit : Bool)
    (he : value c i = if bit then blockMass c.rowWeights c.rowDenominator i else 0) :
    |(k : ℚ) * value c i - (if bit then 1 else 0)| ≤
      (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) := by
  have hC : 0 ≤ 2 * (k : ℤ) := mul_nonneg (by decide) (Nat.cast_nonneg k)
  have hm := blockMass_uniform H (M + 2 * (k : ℤ))
    (rowPerturbation (2 * (k : ℤ)))
    (columnPerturbation (2 * (k : ℤ)) (positiveCoefficients (2 * (k : ℤ)) g)
      (negativeCoefficients g)) c hc
    (rowPerturbation_bounds _ _ hC (by linarith))
    (columnPerturbation_bounds _ _ _ _ hC
      (positiveCoefficients_bounds _ M hC hM g hg)
      (negativeCoefficients_bounds _ M hM g hg)) hscale
  have hH : 0 < H :=
    (mul_nonneg (Nat.cast_nonneg k) (add_nonneg hM hC)).trans_lt hscale
  cases bit
  · simp only [Bool.false_eq_true, ite_false] at he ⊢
    rw [he, mul_zero, sub_zero, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg k)
      (div_nonneg (by exact_mod_cast add_nonneg hM hC)
        (by exact_mod_cast hH.le))
  · simp only [ite_true] at he ⊢
    rw [he]
    have hid : (k : ℚ) * blockMass c.rowWeights c.rowDenominator i - 1 =
        (k : ℚ) * (blockMass c.rowWeights c.rowDenominator i - 1 / (k : ℚ)) := by
      have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp
    rw [hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact mul_le_mul_of_nonneg_left (hm.2 i).1 (Nat.cast_nonneg k)

end GameTheory.Finite.BimatrixBooleanGate
