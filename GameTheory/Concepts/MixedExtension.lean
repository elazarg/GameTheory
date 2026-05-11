import Math.PMFProduct
import Math.Probability
import GameTheory.Concepts.SolutionConcepts

/-!
# Mixed Extension Properties

Basic properties of the mixed extension of a kernel game: EU decomposition,
gain characterization, and the Nash gain-sum identity.

These are definitions and properties of the mixed extension concept, not
the existence theorem (which lives in `Theorems.NashExistenceMixed`).
-/

noncomputable section

open scoped BigOperators
namespace GameTheory

open Math.Probability

namespace KernelGame
open Math.PMFProduct

variable {ι : Type} [DecidableEq ι]

-- ============================================================================
-- EU in the mixed extension
-- ============================================================================

omit [DecidableEq ι] in
/-- EU in the mixed extension under bounded utility, for a kernel game whose
outcome type may be countably infinite. -/
theorem mixedExtension_eu_of_bounded (G : KernelGame ι)
    [Fintype ι]
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι)
    {C : ℝ} (hbd : ∀ ω, |G.utility ω who| ≤ C) :
    G.mixedExtension.eu σ who =
      expect (pmfPi σ) (fun s => G.eu s who) := by
  simp only [mixedExtension, eu]
  exact expect_bind_of_bounded (pmfPi σ) G.outcomeKernel
    (fun ω => G.utility ω who) hbd

omit [DecidableEq ι] in
/-- EU in the mixed extension equals expectation of pure-profile EU
    under the independent product distribution. -/
theorem mixedExtension_eu (G : KernelGame ι)
    [Fintype ι]
    [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) :
    G.mixedExtension.eu σ who =
      expect (pmfPi σ) (fun s => G.eu s who) := by
  obtain ⟨C, hbd⟩ :=
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω who)
  exact G.mixedExtension_eu_of_bounded σ who hbd

open Classical in
/-- EU under a unilateral mixed-strategy update equals the expectation, under the
new mixed strategy `τ`, of EUs under the corresponding pure deviations. -/
theorem mixedExtension_eu_update_of_bounded (G : KernelGame ι)
    [Fintype ι]
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) (τ : PMF (G.Strategy who))
    {C : ℝ} (hbd : ∀ ω, |G.utility ω who| ≤ C) :
    G.mixedExtension.eu (Function.update σ who τ) who =
      expect τ (fun a =>
        G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who) := by
  change expect ((pmfPi (Function.update σ who τ)).bind G.outcomeKernel)
      (fun ω => G.utility ω who) = _
  rw [pmfPi_update_bind, PMF.bind_bind]
  rw [expect_bind_of_bounded τ
      (fun a => (pmfPi (Function.update σ who (PMF.pure a))).bind G.outcomeKernel)
      (fun ω => G.utility ω who) hbd]
  apply tsum_congr; intro a
  rfl

open Classical in
/-- EU when player `who` deviates to `τ` equals expectation of pure-deviation
    EUs under `τ`. -/
theorem mixedExtension_eu_update (G : KernelGame ι)
    [Fintype ι]
    [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) (τ : PMF (G.Strategy who)) :
    G.mixedExtension.eu (Function.update σ who τ) who =
      expect τ (fun a =>
        G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who) := by
  obtain ⟨C, hbd⟩ :=
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω who)
  exact G.mixedExtension_eu_update_of_bounded σ who τ hbd

omit [DecidableEq ι] in
/-- For a kernel game `G` with bounded utility for player `who`, the EU at any
    profile is also bounded by the same constant. Useful for chaining bounded-EU
    lemmas. -/
theorem eu_abs_le_of_bounded (G : KernelGame ι) (who : ι)
    {C : ℝ} (hbd : ∀ ω, |G.utility ω who| ≤ C)
    (s : G.Profile) : |G.eu s who| ≤ C := by
  -- Pointwise bounds: -((d ω).toReal * C) ≤ (d ω).toReal * f ω ≤ (d ω).toReal * C.
  have h_summable :=
    Math.Probability.expect_summable_of_bounded (G.outcomeKernel s)
      (fun ω => G.utility ω who) hbd
  have h_summable_bd : Summable (fun ω => (G.outcomeKernel s ω).toReal * C) :=
    (Math.Probability.pmf_toReal_summable (G.outcomeKernel s)).mul_right C
  have h_sum_one : ∑' ω, (G.outcomeKernel s ω).toReal * C = C := by
    rw [tsum_mul_right, Math.Probability.pmf_toReal_tsum_one, one_mul]
  have h_upper : G.eu s who ≤ C := by
    have h_le : ∀ ω, (G.outcomeKernel s ω).toReal * G.utility ω who ≤
        (G.outcomeKernel s ω).toReal * C := by
      intro ω
      have hd : 0 ≤ (G.outcomeKernel s ω).toReal := ENNReal.toReal_nonneg
      exact mul_le_mul_of_nonneg_left (le_of_abs_le (hbd ω)) hd
    calc G.eu s who
        = ∑' ω, (G.outcomeKernel s ω).toReal * G.utility ω who := rfl
      _ ≤ ∑' ω, (G.outcomeKernel s ω).toReal * C :=
          h_summable.tsum_le_tsum h_le h_summable_bd
      _ = C := h_sum_one
  have h_lower : -C ≤ G.eu s who := by
    have h_le : ∀ ω, -((G.outcomeKernel s ω).toReal * C) ≤
        (G.outcomeKernel s ω).toReal * G.utility ω who := by
      intro ω
      have hd : 0 ≤ (G.outcomeKernel s ω).toReal := ENNReal.toReal_nonneg
      have h_neg_le : -C ≤ G.utility ω who := neg_le_of_abs_le (hbd ω)
      have := mul_le_mul_of_nonneg_left h_neg_le hd
      linarith [this]
    calc (-C : ℝ)
        = -∑' ω, (G.outcomeKernel s ω).toReal * C := by rw [h_sum_one]
      _ = ∑' ω, -((G.outcomeKernel s ω).toReal * C) := (tsum_neg).symm
      _ ≤ ∑' ω, (G.outcomeKernel s ω).toReal * G.utility ω who :=
          h_summable_bd.neg.tsum_le_tsum h_le h_summable
      _ = G.eu s who := rfl
  exact abs_le.mpr ⟨h_lower, h_upper⟩

-- ============================================================================
-- Bounded-utility analogs of NashGain results
-- ============================================================================

section NashGainBounded

variable [Fintype ι]
variable (G : KernelGame ι)

open Classical in
/-- The gain of player `who` from a pure deviation to action `a`.

The definition itself is distribution-level and does not require finite outcomes;
boundedness or finiteness assumptions enter only when proving EU decomposition
and Nash-characterization lemmas. -/
def mixedGain (σ : ∀ i, PMF (G.Strategy i)) (who : ι) (a : G.Strategy who) : ℝ :=
  G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who -
  G.mixedExtension.eu σ who

open Classical in
/-- Expected pure-deviation gain under the current mixed strategy is zero. -/
theorem weighted_gain_sum_zero_of_bounded
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι)
    {C : ℝ} (hbd : ∀ ω, |G.utility ω who| ≤ C) :
    expect (σ who)
      (fun a => G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who
        - G.mixedExtension.eu σ who) = 0 := by
  -- Split the expectation of the difference into two pieces.
  have h_eu_bd : ∀ a, |G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who| ≤ C :=
    fun a => G.mixedExtension.eu_abs_le_of_bounded who hbd _
  have h_summable_eu : Summable (fun a => ((σ who) a).toReal *
      G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who) :=
    Math.Probability.expect_summable_of_bounded (σ who) _ h_eu_bd
  have h_summable_const : Summable (fun a : G.Strategy who =>
      ((σ who) a).toReal * G.mixedExtension.eu σ who) :=
    (Math.Probability.pmf_toReal_summable (σ who)).mul_right _
  -- The first piece is `eu σ who` (via `mixedExtension_eu_update_of_bounded` at τ = σ who).
  have hdecomp :
      (∑' a, ((σ who) a).toReal *
        G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who) =
      G.mixedExtension.eu σ who := by
    have h := G.mixedExtension_eu_update_of_bounded σ who (σ who) hbd
    simp only [Function.update_eq_self] at h
    exact h.symm
  -- The second piece is `eu σ who` (constant times PMF mass).
  have hconst :
      (∑' a : G.Strategy who, ((σ who) a).toReal * G.mixedExtension.eu σ who) =
      G.mixedExtension.eu σ who := by
    rw [tsum_mul_right, Math.Probability.pmf_toReal_tsum_one, one_mul]
  -- Subtract the two.
  unfold Math.Probability.expect
  simp_rw [mul_sub]
  rw [h_summable_eu.tsum_sub h_summable_const, hdecomp, hconst, sub_self]

open Classical in
/-- A mixed profile is Nash iff all pure-deviation gains are non-positive,
    under bounded utility. -/
theorem isNash_iff_gains_nonpos_of_bounded
    (σ : ∀ i, PMF (G.Strategy i))
    {C : ι → ℝ} (hbd : ∀ who ω, |G.utility ω who| ≤ C who) :
    G.mixedExtension.IsNash σ ↔
      ∀ who (a : G.Strategy who),
        G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who -
          G.mixedExtension.eu σ who ≤ 0 := by
  constructor
  · intro hN who a
    have h := hN who (PMF.pure a)
    linarith
  · intro hgain who τ
    rw [ge_iff_le]
    have hdecomp := G.mixedExtension_eu_update_of_bounded σ who τ (hbd who)
    rw [hdecomp]
    letI : Nonempty (G.Strategy who) := ⟨τ.support_nonempty.choose⟩
    conv_rhs => rw [show G.mixedExtension.eu σ who =
        expect τ (fun _ => G.mixedExtension.eu σ who) from by
      simp [expect_const]]
    apply Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
      (C := |C who| + |G.mixedExtension.eu σ who|)
    · intro a
      have hga := hgain who a
      linarith
    · -- |G.mixedExtension.eu (update σ who (pure a)) who| ≤ |C who| + |...eu σ who|
      intro a
      have hb : |G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who| ≤ |C who| := by
        have h := G.mixedExtension.eu_abs_le_of_bounded who (hbd who)
          (Function.update σ who (PMF.pure a))
        exact h.trans (le_abs_self (C who))
      have habs_sub : |G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who -
          G.mixedExtension.eu σ who| ≤
          |G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who| +
            |G.mixedExtension.eu σ who| :=
        abs_sub _ _
      linarith [abs_nonneg (G.mixedExtension.eu σ who)]
    · -- |G.mixedExtension.eu σ who| ≤ |C who| + |...eu σ who| trivially
      intro a
      have := abs_nonneg (C who)
      linarith [abs_nonneg (G.mixedExtension.eu σ who)]

end NashGainBounded

-- ============================================================================
-- Gains and Nash characterization
-- ============================================================================

section NashGain

variable [Fintype ι]
variable (G : KernelGame ι)
variable [Finite G.Outcome]

open Classical in
/-- Weighted gain sum is zero: the expectation of gain under the current
    mixed strategy is zero. -/
theorem weighted_gain_sum_zero
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) :
    expect (σ who) (fun a => G.mixedGain σ who a) = 0 := by
  obtain ⟨C, hbd⟩ :=
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω who)
  simpa [mixedGain] using G.weighted_gain_sum_zero_of_bounded σ who hbd

open Classical in
/-- A mixed profile is Nash iff all pure-deviation gains are non-positive. -/
theorem isNash_iff_gains_nonpos
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedExtension.IsNash σ ↔
      ∀ who (a : G.Strategy who), G.mixedGain σ who a ≤ 0 := by
  let C : ι → ℝ := fun who =>
    (Math.Probability.exists_abs_bound_of_finite
      (fun ω => G.utility ω who)).choose
  have hbd : ∀ who ω, |G.utility ω who| ≤ C who := fun who =>
    (Math.Probability.exists_abs_bound_of_finite
      (fun ω => G.utility ω who)).choose_spec
  simpa [mixedGain] using G.isNash_iff_gains_nonpos_of_bounded σ hbd

end NashGain

end KernelGame

end GameTheory
