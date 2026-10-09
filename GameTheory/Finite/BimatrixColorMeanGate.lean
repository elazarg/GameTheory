import GameTheory.Finite.BimatrixArithmeticGate
import GameTheory.Math.ClippedArithmetic

/-!
# Affine averaging of weighted color channels

Integer coefficients aggregate all occurrences of each input wire. At common scale `2 * k`,
with `k = 123 * u`, the normalized signal averages forty-one samples and scales the dominant
and secondary channels by two and one. Unit convex weights bound the ideal minimum-weight
mean without requiring exclusive color indicators. Independent wire errors contribute four
times their common bound because each sample contains four corners.
-/

namespace GameTheory.Finite.BimatrixColorMeanGate
open BimatrixAffineGate BimatrixGateProgram
open scoped BigOperators
variable {k : ℕ}

/-- Repeated wire occurrences contribute separately, including aliased channels. -/
def meanCoefficients (u : ℕ) (dominant secondary : Fin 41 → Fin 4 → Fin k)
    (j : Fin k) : ℤ :=
  ∑ t, ∑ a, 2 * (u : ℤ) *
    (2 * (if j = dominant t a then 1 else 0) +
      (if j = secondary t a then 1 else 0))

/-- The mean block specializes the canonical affine gate factory. -/
abbrev meanGate (u : ℕ) (dominant secondary : Fin 41 → Fin 4 → Fin k) : Gate k :=
  BimatrixArithmeticGate.gate (meanCoefficients u dominant secondary) 0

/-- The normalized signal is the exact scaled arithmetic mean of the actual wires. -/
theorem mean_signal (u : ℕ) (hu : 0 < u) (hk : k = 123 * u)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (dominant secondary : Fin 41 → Fin 4 → Fin k) :
    (∑ j, ((meanCoefficients u dominant secondary j : ℤ) : ℚ) /
      ((2 * (k : ℤ) : ℤ) : ℚ) * ((k : ℚ) * value c j)) +
      (k : ℚ) * (0 : ℤ) / ((2 * (k : ℤ) : ℤ) : ℚ) =
      (∑ t, ∑ a, (2 * ((k : ℚ) * value c (dominant t a)) +
        ((k : ℚ) * value c (secondary t a)))) / 123 := by
  have huq : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hu.ne'
  simp only [meanCoefficients, Int.cast_sum, Int.cast_mul, Int.cast_ofNat,
    Int.cast_natCast, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
    Finset.sum_div, Finset.sum_mul, mul_zero, zero_div, add_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_add, add_div, add_mul, Finset.sum_add_distrib,
    mul_ite, mul_one, mul_zero, ite_div, zero_div, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  subst k
  push_cast
  field_simp

private theorem min_mean_error (X Y w z₀ z₁ : Fin 41 → Fin 4 → ℚ) (ζ : ℚ)
    (hX : ∀ t a, |X t a - min (w t a) (z₀ t a)| ≤ ζ)
    (hY : ∀ t a, |Y t a - min (w t a) (z₁ t a)| ≤ ζ) :
    |(∑ t, ∑ a, (2 * X t a + Y t a)) / 123 -
      (∑ t, ∑ a, (2 * min (w t a) (z₀ t a) + min (w t a) (z₁ t a))) / 123| ≤ 4 * ζ := by
  have he : ∀ t a, |(2 * X t a + Y t a) -
      (2 * min (w t a) (z₀ t a) + min (w t a) (z₁ t a))| ≤ 3 * ζ := by
    intro t a
    have ht := abs_add_le (2 * (X t a - min (w t a) (z₀ t a)))
      (Y t a - min (w t a) (z₁ t a))
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 2)] at ht
    have hid : (2 * X t a + Y t a) -
        (2 * min (w t a) (z₀ t a) + min (w t a) (z₁ t a)) =
        2 * (X t a - min (w t a) (z₀ t a)) +
          (Y t a - min (w t a) (z₁ t a)) := by ring
    rw [hid]
    linarith [hX t a, hY t a]
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 123)]
  apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 123)).mpr
  calc
    _ ≤ ∑ t : Fin 41, ∑ a : Fin 4, |(2 * X t a + Y t a) -
        (2 * min (w t a) (z₀ t a) + min (w t a) (z₁ t a))| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ =>
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _t : Fin 41, ∑ _a : Fin 4, (3 * ζ) :=
      Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun a _ => he t a
    _ = 4 * ζ * 123 := by simp; ring

/-- Convex weights keep the ideal mean in the unit interval, without exclusive indicators. -/
theorem min_mean_mem_unit (w z₀ z₁ : Fin 41 → Fin 4 → ℚ)
    (hw : ∀ t a, 0 ≤ w t a) (hsum : ∀ t, ∑ a, w t a = 1)
    (hz₀ : ∀ t a, 0 ≤ z₀ t a) (hz₁ : ∀ t a, 0 ≤ z₁ t a) :
    0 ≤ (∑ t, ∑ a, (2 * min (w t a) (z₀ t a) + min (w t a) (z₁ t a))) / 123 ∧
    (∑ t, ∑ a, (2 * min (w t a) (z₀ t a) + min (w t a) (z₁ t a))) / 123 ≤ 1 := by
  constructor
  · apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro t _
    apply Finset.sum_nonneg
    intro a _
    exact add_nonneg (mul_nonneg (by norm_num) (le_min (hw t a) (hz₀ t a)))
      (le_min (hw t a) (hz₁ t a))
  · apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 123)).mpr
    calc
      _ ≤ ∑ t : Fin 41, ∑ a : Fin 4, (3 * w t a) := by
        apply Finset.sum_le_sum
        intro t _
        apply Finset.sum_le_sum
        intro a _
        linarith only [min_le_left (w t a) (z₀ t a), min_le_left (w t a) (z₁ t a)]
      _ = 1 * 123 := by simp only [← Finset.mul_sum, hsum]; norm_num

/-- An accepted averaging block approximates the ideal minimum-weight mean. -/
theorem mean_gate_error (u : ℕ) (hu : 0 < u) (hk : k = 123 * u)
    (H M : ℤ) (g : Fin k → Gate k) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (dominant secondary : Fin 41 → Fin 4 → Fin k) (out : Fin k)
    (hi : g out = meanGate u dominant secondary)
    (w z₀ z₁ : Fin 41 → Fin 4 → ℚ) (ζ : ℚ)
    (hw : ∀ t a, 0 ≤ w t a) (hsum : ∀ t, ∑ a, w t a = 1)
    (hz₀ : ∀ t a, 0 ≤ z₀ t a) (hz₁ : ∀ t a, 0 ≤ z₁ t a)
    (hdom : ∀ t a, |(k : ℚ) * value c (dominant t a) - min (w t a) (z₀ t a)| ≤ ζ)
    (hsec : ∀ t a, |(k : ℚ) * value c (secondary t a) - min (w t a) (z₁ t a)| ≤ ζ) :
    |(k : ℚ) * value c out -
      (∑ t, ∑ a, (2 * min (w t a) (z₀ t a) + min (w t a) (z₁ t a))) / 123| ≤
      (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) + 4 * ζ := by
  have hkpos : 0 < k := by omega
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hkpos
  have ha := BimatrixArithmeticGate.normalized_value_error H (2 * (k : ℤ)) M
    (meanCoefficients u dominant secondary) 0 g c hc hC hM hg hscale out hi
  rw [mean_signal u hu hk c dominant secondary] at ha
  have he := min_mean_error (fun t a => (k : ℚ) * value c (dominant t a))
    (fun t a => (k : ℚ) * value c (secondary t a)) w z₀ z₁ ζ hdom hsec
  have hunit := min_mean_mem_unit w z₀ z₁ hw hsum hz₀ hz₁
  have hcl := GameTheory.Math.unitClamp_nonexpansive
    ((∑ t, ∑ a, (2 * ((k : ℚ) * value c (dominant t a)) +
      (k : ℚ) * value c (secondary t a))) / 123)
    ((∑ t, ∑ a, (2 * min (w t a) (z₀ t a) + min (w t a) (z₁ t a))) / 123)
  rw [GameTheory.Math.unitClamp_eq_self hunit.1 hunit.2] at hcl
  exact (abs_sub_le _ _ _).trans (add_le_add ha (hcl.trans he))

end GameTheory.Finite.BimatrixColorMeanGate
