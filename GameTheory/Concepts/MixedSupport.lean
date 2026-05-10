import GameTheory.Concepts.MixedExtension

/-!
# Support Lemma for Mixed Nash Equilibria

The support lemma states that in a mixed Nash equilibrium, every pure
strategy played with positive probability must be a best response
(i.e., its gain is exactly zero, not just nonpositive).

## Main results

* `mixedNash_support_gain_zero` — if `σ` is mixed Nash and `(σ who) a > 0`,
  then `mixedGain σ who a = 0`
* `mixedNash_support_eu_eq` — all strategies in the support yield the same EU
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

attribute [local instance] Fintype.ofFinite

variable {ι : Type} [Fintype ι]
  (G : KernelGame ι) [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
  [Finite G.Outcome]

open Classical in
/-- **Support lemma**: in a mixed Nash equilibrium, any pure strategy
    played with positive probability has zero gain (is a best response). -/
theorem mixedNash_support_gain_zero
    {σ : ∀ i, PMF (G.Strategy i)}
    (hN : G.mixedExtension.IsNash σ)
    {who : ι} {a : G.Strategy who}
    (hpos : (σ who) a ≠ 0) :
    G.mixedGain σ who a = 0 := by
  have hgains := (G.isNash_iff_gains_nonpos σ).mp hN
  have hwg := G.weighted_gain_sum_zero σ who
  rw [expect_eq_sum] at hwg
  have hle : ∀ b : G.Strategy who,
      ((σ who) b).toReal * G.mixedGain σ who b ≤ 0 :=
    fun b => mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg (hgains who b)
  have hsum_zero := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hle b)).mp hwg
  have ha_zero := hsum_zero a (Finset.mem_univ a)
  have hpos_real : (0 : ℝ) < ((σ who) a).toReal :=
    ENNReal.toReal_pos hpos (PMF.apply_ne_top _ _)
  exact (mul_eq_zero.mp ha_zero).resolve_left (ne_of_gt hpos_real)

open Classical in
/-- In a mixed Nash equilibrium, all pure strategies in the support
    yield the same expected utility. -/
theorem mixedNash_support_eu_eq
    {σ : ∀ i, PMF (G.Strategy i)}
    (hN : G.mixedExtension.IsNash σ)
    {who : ι} {a b : G.Strategy who}
    (ha : (σ who) a ≠ 0) (hb : (σ who) b ≠ 0) :
    G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who =
    G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who := by
  have hga := mixedNash_support_gain_zero G hN ha
  have hgb := mixedNash_support_gain_zero G hN hb
  simp only [mixedGain, sub_eq_zero] at hga hgb
  exact hga.trans hgb.symm

end KernelGame

-- ============================================================================
-- Bounded-utility variants of the support lemma
-- ============================================================================

namespace KernelGame

open Classical in
/-- Bounded-utility variant of `mixedNash_support_gain_zero`. -/
theorem mixedNash_support_gain_zero_of_bounded
    {ι : Type} [Fintype ι]
    (G : KernelGame ι) [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {σ : ∀ i, PMF (G.Strategy i)}
    (hN : G.mixedExtension.IsNash σ)
    {who : ι} {a : G.Strategy who} (hpos : (σ who) a ≠ 0)
    {C : ι → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who -
      G.mixedExtension.eu σ who = 0 := by
  have hgains := (G.isNash_iff_gains_nonpos_of_bounded σ hbd).mp hN
  have hwg := G.weighted_gain_sum_zero_of_bounded σ who (hbd who)
  rw [Math.Probability.expect_eq_sum] at hwg
  have hle : ∀ b : G.Strategy who,
      ((σ who) b).toReal * (G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who -
        G.mixedExtension.eu σ who) ≤ 0 :=
    fun b => mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg (hgains who b)
  have hsum_zero := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hle b)).mp hwg
  have ha_zero := hsum_zero a (Finset.mem_univ a)
  have hpos_real : (0 : ℝ) < ((σ who) a).toReal :=
    ENNReal.toReal_pos hpos (PMF.apply_ne_top _ _)
  exact (mul_eq_zero.mp ha_zero).resolve_left (ne_of_gt hpos_real)

open Classical in
/-- Bounded-utility variant of `mixedNash_support_eu_eq`. -/
theorem mixedNash_support_eu_eq_of_bounded
    {ι : Type} [Fintype ι]
    (G : KernelGame ι) [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {σ : ∀ i, PMF (G.Strategy i)}
    (hN : G.mixedExtension.IsNash σ)
    {who : ι} {a b : G.Strategy who}
    (ha : (σ who) a ≠ 0) (hb : (σ who) b ≠ 0)
    {C : ι → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who =
    G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who := by
  have hga := G.mixedNash_support_gain_zero_of_bounded hN ha hbd
  have hgb := G.mixedNash_support_gain_zero_of_bounded hN hb hbd
  linarith

end KernelGame

end GameTheory
