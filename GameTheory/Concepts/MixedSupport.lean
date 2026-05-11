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
  let C : ι → ℝ := fun who =>
    (Math.Probability.exists_abs_bound_of_finite
      (fun ω => G.utility ω who)).choose
  have hbd : ∀ who ω, |G.utility ω who| ≤ C who := fun who =>
    (Math.Probability.exists_abs_bound_of_finite
      (fun ω => G.utility ω who)).choose_spec
  have hgains := (G.isNash_iff_gains_nonpos_of_bounded σ hbd).mp hN
  have hwg := G.weighted_gain_sum_zero_of_bounded σ who (hbd who)
  let gain : G.Strategy who → ℝ := fun b =>
    G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who -
      G.mixedExtension.eu σ who
  have hgain_nonpos : ∀ b, gain b ≤ 0 := by
    intro b
    exact hgains who b
  have hgain_bounded : ∀ b, |gain b| ≤ |C who| + |G.mixedExtension.eu σ who| := by
    intro b
    have hb : |G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who| ≤ |C who| := by
      have h := G.mixedExtension.eu_abs_le_of_bounded who (hbd who)
        (Function.update σ who (PMF.pure b))
      exact h.trans (le_abs_self (C who))
    have habs_sub : |G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who -
        G.mixedExtension.eu σ who| ≤
        |G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who| +
          |G.mixedExtension.eu σ who| :=
      abs_sub _ _
    linarith
  have hsummable :
      Summable (fun b => ((σ who) b).toReal * gain b) :=
    Math.Probability.expect_summable_of_bounded (σ who) gain hgain_bounded
  simpa [mixedGain, gain] using
    Math.ProbabilityMassFunction.eq_zero_of_expect_eq_zero_of_nonpos_of_pos
      (σ who) gain hgain_nonpos (by simpa [gain] using hwg) hsummable hpos

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
  let gain : G.Strategy who → ℝ := fun b =>
    G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who -
      G.mixedExtension.eu σ who
  have hgain_nonpos : ∀ b, gain b ≤ 0 := by
    intro b
    exact hgains who b
  have hgain_bounded : ∀ b, |gain b| ≤ |C who| + |G.mixedExtension.eu σ who| := by
    intro b
    have hb : |G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who| ≤ |C who| := by
      have h := G.mixedExtension.eu_abs_le_of_bounded who (hbd who)
        (Function.update σ who (PMF.pure b))
      exact h.trans (le_abs_self (C who))
    have habs_sub : |G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who -
        G.mixedExtension.eu σ who| ≤
        |G.mixedExtension.eu (Function.update σ who (PMF.pure b)) who| +
          |G.mixedExtension.eu σ who| :=
      abs_sub _ _
    linarith
  have hsummable :
      Summable (fun b => ((σ who) b).toReal * gain b) :=
    Math.Probability.expect_summable_of_bounded (σ who) gain hgain_bounded
  exact Math.ProbabilityMassFunction.eq_zero_of_expect_eq_zero_of_nonpos_of_pos
    (σ who) gain hgain_nonpos (by simpa [gain] using hwg) hsummable hpos

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
