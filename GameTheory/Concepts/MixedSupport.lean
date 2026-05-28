/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

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
  (G : KernelGame ι) [Finite G.Outcome]

open Classical in
/-- **Support lemma**: in a mixed Nash equilibrium, any pure strategy
    played with positive probability has zero gain (is a best response). -/
theorem mixedNash_support_gain_zero
    {σ : ∀ i, PMF (G.Strategy i)}
    (hN : G.mixedExtension.IsNash σ)
    {who : ι} {a : G.Strategy who}
    (hpos : (σ who) a ≠ 0) :
    G.mixedGain σ who a = 0 := by
  classical
  have hgains := (G.isNash_iff_gains_nonpos σ).mp hN
  have hwg := G.weighted_gain_sum_zero σ who
  -- Each term `(σ who b).toReal * mixedGain σ who b` is nonpositive (PMF mass ≥ 0,
  -- gain ≤ 0). If the term at `a` were strictly negative, the negated sum would be
  -- strictly positive by `Summable.tsum_pos`, contradicting `hwg`.
  have hpos_real : (0 : ℝ) < ((σ who) a).toReal :=
    ENNReal.toReal_pos hpos (PMF.apply_ne_top _ _)
  -- Bound on `mixedGain` derived from a uniform utility bound (Finite outcome).
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun ω => |G.utility ω who|) :=
    Finite.bddAbove_range _
  have hbd_util : ∀ ω, |G.utility ω who| ≤ C := fun ω => hC ⟨ω, rfl⟩
  have hbd_gain : ∀ b, |G.mixedGain σ who b| ≤ 2 * C := fun b => by
    have h1 := G.mixedExtension.eu_abs_le_of_bounded who hbd_util
      (Function.update σ who (PMF.pure b))
    have h2 := G.mixedExtension.eu_abs_le_of_bounded who hbd_util σ
    calc |G.mixedGain σ who b|
        = |G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who -
            G.mixedExtension.eu σ who| := rfl
      _ ≤ |G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who| +
            |G.mixedExtension.eu σ who| := abs_sub _ _
      _ ≤ C + C := add_le_add h1 h2
      _ = 2 * C := by ring
  have h_summable :
      Summable (fun b => (σ who b).toReal * G.mixedGain σ who b) :=
    Math.Probability.expect_summable_of_bounded (σ who) _ hbd_gain
  by_contra hne
  have hlt : G.mixedGain σ who a < 0 := lt_of_le_of_ne (hgains who a) hne
  let h : G.Strategy who → ℝ :=
    fun b => -((σ who b).toReal * G.mixedGain σ who b)
  have h_nn : ∀ b, 0 ≤ h b := fun b => neg_nonneg.mpr
    (mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg (hgains who b))
  have h_summable' : Summable h := h_summable.neg
  have h_sum_zero : ∑' b, h b = 0 := by
    change ∑' b, -((σ who b).toReal * G.mixedGain σ who b) = 0
    rw [tsum_neg]
    have : (∑' b, (σ who b).toReal * G.mixedGain σ who b) =
        Math.Probability.expect (σ who) (G.mixedGain σ who) := rfl
    rw [this, hwg, neg_zero]
  have h_at_a_pos : 0 < h a :=
    neg_pos.mpr (mul_neg_of_pos_of_neg hpos_real hlt)
  have := h_summable'.tsum_pos h_nn a h_at_a_pos
  linarith

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

namespace KernelGame

open Classical in
/-- Support lemma under bounded utility: in a mixed Nash equilibrium, any pure
    strategy played with positive probability has zero EU gain. -/
theorem mixedNash_support_gain_zero_of_bounded
    {ι : Type} [Fintype ι]
    (G : KernelGame ι)
    {σ : ∀ i, PMF (G.Strategy i)}
    (hN : G.mixedExtension.IsNash σ)
    {who : ι} {a : G.Strategy who} (hpos : (σ who) a ≠ 0)
    {C : ι → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who -
      G.mixedExtension.eu σ who = 0 := by
  have hgains := (G.isNash_iff_gains_nonpos_of_bounded σ hbd).mp hN
  have hwg := G.weighted_gain_sum_zero_of_bounded σ who (hbd who)
  have hpos_real : (0 : ℝ) < ((σ who) a).toReal :=
    ENNReal.toReal_pos hpos (PMF.apply_ne_top _ _)
  -- `mixedGain` is bounded by `2 * C who` (each EU bounded by `C who`).
  have hbd_gain : ∀ b, |G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who -
      G.mixedExtension.eu σ who| ≤ 2 * C who := fun b => by
    have h1 := G.mixedExtension.eu_abs_le_of_bounded who (hbd who)
      (Function.update σ who (PMF.pure b))
    have h2 := G.mixedExtension.eu_abs_le_of_bounded who (hbd who) σ
    calc |G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who -
          G.mixedExtension.eu σ who|
        ≤ |G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who| +
            |G.mixedExtension.eu σ who| := abs_sub _ _
      _ ≤ C who + C who := add_le_add h1 h2
      _ = 2 * C who := by ring
  have h_summable :
      Summable (fun b => (σ who b).toReal *
        (G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who -
          G.mixedExtension.eu σ who)) :=
    Math.Probability.expect_summable_of_bounded (σ who) _ hbd_gain
  by_contra hne
  have hlt : G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who -
      G.mixedExtension.eu σ who < 0 := lt_of_le_of_ne (hgains who a) hne
  let h : G.Strategy who → ℝ :=
    fun b => -((σ who b).toReal *
      (G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who -
        G.mixedExtension.eu σ who))
  have h_nn : ∀ b, 0 ≤ h b := fun b => neg_nonneg.mpr
    (mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg (hgains who b))
  have h_summable' : Summable h := h_summable.neg
  have h_sum_zero : ∑' b, h b = 0 := by
    change ∑' b, -((σ who b).toReal *
      (G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who -
        G.mixedExtension.eu σ who)) = 0
    rw [tsum_neg]
    have : (∑' b, (σ who b).toReal *
        (G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who -
          G.mixedExtension.eu σ who)) =
        Math.Probability.expect (σ who) (fun b =>
          G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who -
            G.mixedExtension.eu σ who) := rfl
    rw [this, hwg, neg_zero]
  have h_at_a_pos : 0 < h a :=
    neg_pos.mpr (mul_neg_of_pos_of_neg hpos_real hlt)
  have := h_summable'.tsum_pos h_nn a h_at_a_pos
  linarith

open Classical in
/-- Under bounded utility, all pure strategies in the support of a mixed Nash
    equilibrium yield the same expected utility. -/
theorem mixedNash_support_eu_eq_of_bounded
    {ι : Type} [Fintype ι]
    (G : KernelGame ι)
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
