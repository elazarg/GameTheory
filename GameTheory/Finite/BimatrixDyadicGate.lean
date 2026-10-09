import GameTheory.Finite.BimatrixArithmeticGate
import GameTheory.Math.ClippedArithmetic

/-!
# Dyadic scaling in canonical affine game programs

Halving uses the same integer coefficient scale as comparator and binary extraction gates.
Every accepted certificate approximates the clipped half of its actual input. Chaining these
blocks yields dyadic scaling with uniformly bounded game error, using one block per halving.
-/

namespace GameTheory.Finite.BimatrixDyadicGate
open BimatrixAffineGate BimatrixGateProgram
open scoped BigOperators
variable {k : ℕ}

/-- A single normalized input carries half the common affine coefficient scale. -/
def halvingCoefficients (a : Fin k) (j : Fin k) : ℤ := if j = a then k else 0

/-- Halving specializes the canonical affine gate factory. -/
abbrev halvingGate (a : Fin k) : Gate k :=
  BimatrixArithmeticGate.gate (halvingCoefficients a) 0

private theorem halving_signal (hk : 0 < k)
    (c : BimatrixCertificate (k * 2) (k * 2)) (a : Fin k) :
    (∑ j, ((halvingCoefficients a j : ℤ) : ℚ) / ((2 * (k : ℤ) : ℤ) : ℚ) *
      ((k : ℚ) * value c j)) + (k : ℚ) * (0 : ℤ) / ((2 * (k : ℤ) : ℤ) : ℚ) =
      ((k : ℚ) * value c a) / 2 := by
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  simp [halvingCoefficients, ite_div, ite_mul]
  field_simp

/-- Every accepted halving block approximates the clipped half of its actual input. -/
theorem halving_gate_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (a out : Fin k)
    (hi : g out = halvingGate a) :
    |(k : ℚ) * value c out - max 0 (min 1 (((k : ℚ) * value c a) / 2))| ≤
      (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) := by
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hk
  have h := BimatrixArithmeticGate.normalized_value_error H (2 * (k : ℤ)) M
    (halvingCoefficients a) 0 g c hc hC hM hg hscale out hi
  rw [halving_signal hk c a] at h
  exact h

/-- Clipping preserves an exact unit input while halving its representation error. -/
theorem halving_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (a out : Fin k)
    (hi : g out = halvingGate a) (x E : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (herr : |(k : ℚ) * value c a - x| ≤ E) :
    |(k : ℚ) * value c out - x / 2| ≤
      (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) + E / 2 := by
  have ha := halving_gate_error H M hk g c hc hM hg hscale a out hi
  have hcl := GameTheory.Math.unitClamp_nonexpansive (((k : ℚ) * value c a) / 2) (x / 2)
  have hx20 : 0 ≤ x / 2 := div_nonneg hx0 (by norm_num)
  have hx21 : x / 2 ≤ 1 := by linarith
  rw [GameTheory.Math.unitClamp_eq_self hx20 hx21, ← sub_div, abs_div,
    abs_of_pos (by norm_num : (0 : ℚ) < 2)] at hcl
  have hd := div_le_div_of_nonneg_right herr (by norm_num : (0 : ℚ) ≤ 2)
  have ht := abs_sub_le ((k : ℚ) * value c out)
    (max 0 (min 1 (((k : ℚ) * value c a) / 2))) (x / 2)
  linarith

/-- A halving chain has game error at most twice the common per-block bound. -/
theorem halving_chain_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (r : ℕ → Fin k) (n : ℕ) (a ε δ : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (hchain : ∀ j < n, g (r (j + 1)) = halvingGate (r j))
    (hinit : |(k : ℚ) * value c (r 0) - a| ≤ ε) :
    ∀ j ≤ n, |(k : ℚ) * value c (r j) - a / (2 : ℚ) ^ j| ≤
      2 * δ + ε / (2 : ℚ) ^ j := by
  intro j hj
  induction j with
  | zero => simp only [pow_zero, div_one]; linarith only [hinit, hδ0]
  | succ j ih =>
    have hjn : j < n := by omega
    have hi := ih (by omega)
    have hp : (0 : ℚ) < 2 ^ j := pow_pos (by norm_num) j
    have hp1 : (1 : ℚ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hx0 : 0 ≤ a / (2 : ℚ) ^ j := div_nonneg ha0 hp.le
    have hx1 : a / (2 : ℚ) ^ j ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
    have he := halving_error H M hk g c hc hM hg hscale (r j) (r (j + 1))
      (hchain j hjn) (a / (2 : ℚ) ^ j) (2 * δ + ε / (2 : ℚ) ^ j) hx0 hx1 hi
    have heq : a / (2 : ℚ) ^ j / 2 = a / (2 : ℚ) ^ (j + 1) := by
      rw [div_div, pow_succ]
    rw [heq] at he
    have heε : ε / (2 : ℚ) ^ j / 2 = ε / (2 : ℚ) ^ (j + 1) := by
      rw [div_div, pow_succ]
    rw [add_div, mul_div_cancel_left₀ δ (by norm_num : (2 : ℚ) ≠ 0), heε] at he
    linarith only [he, hδ]

end GameTheory.Finite.BimatrixDyadicGate
