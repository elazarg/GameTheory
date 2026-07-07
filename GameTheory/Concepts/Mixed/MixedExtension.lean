/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.PMFProduct
import Math.Probability
import Mathlib.Probability.Distributions.Uniform
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Foundations.Convergence

/-!
# Mixed Extension Properties

Basic properties of the mixed extension of a kernel game: EU decomposition,
gain characterization, and the Nash gain-sum identity.

These are definitions and properties of the mixed extension concept, not
the existence theorem (which lives in `Concepts.Existence.NashExistenceMixed`).
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
open Classical in
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
theorem mixedExtension_eu (G : KernelGame ι) [Fintype ι] [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) :
    G.mixedExtension.eu σ who =
      expect (pmfPi σ) (fun s => G.eu s who) := by
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun ω => |G.utility ω who|) :=
    Finite.bddAbove_range _
  exact G.mixedExtension_eu_of_bounded σ who (fun ω => hC ⟨ω, rfl⟩)

omit [DecidableEq ι] in
/-- Embed a pure stage-game profile as a mixed profile of the mixed extension. -/
def pureMixedProfile (G : KernelGame ι) [Fintype ι] (σ : Profile G) :
    Profile G.mixedExtension :=
  fun i => PMF.pure (σ i)

omit [DecidableEq ι] in
@[simp] theorem pureMixedProfile_apply (G : KernelGame ι) [Fintype ι]
    (σ : Profile G) (i : ι) :
    G.pureMixedProfile σ i = PMF.pure (σ i) :=
  rfl

/-- Updating a pure profile before embedding is the same as embedding first and
updating the mixed profile by the corresponding point mass. -/
@[simp] theorem pureMixedProfile_update (G : KernelGame ι) [Fintype ι]
    (σ : Profile G) (who : ι) (a : G.Strategy who) :
    G.pureMixedProfile (Function.update σ who a) =
      Function.update (G.pureMixedProfile σ) who (PMF.pure a) := by
  funext i
  by_cases hi : i = who
  · subst hi
    simp [pureMixedProfile]
  · simp [pureMixedProfile, Function.update_of_ne hi]

omit [DecidableEq ι] in
/-- Pure profiles embedded in the mixed extension preserve expected utility. -/
theorem mixedExtension_eu_pureMixedProfile (G : KernelGame ι) [Fintype ι]
    (σ : Profile G) (who : ι) :
    G.mixedExtension.eu (G.pureMixedProfile σ) who = G.eu σ who := by
  simp only [mixedExtension, eu]
  change expect
      ((pmfPi (fun i => (PMF.pure (σ i) : PMF (G.Strategy i)))).bind
        G.outcomeKernel) (fun ω => G.utility ω who) =
    expect (G.outcomeKernel σ) (fun ω => G.utility ω who)
  rw [pmfPi_pure, PMF.pure_bind]

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
    [Fintype ι] [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) (τ : PMF (G.Strategy who)) :
    G.mixedExtension.eu (Function.update σ who τ) who =
      expect τ (fun a =>
        G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who) := by
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun ω => |G.utility ω who|) :=
    Finite.bddAbove_range _
  exact G.mixedExtension_eu_update_of_bounded σ who τ (fun ω => hC ⟨ω, rfl⟩)

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
/-- The gain of player `who` from a pure deviation to action `a`. -/
def mixedGain (σ : ∀ i, PMF (G.Strategy i)) (who : ι) (a : G.Strategy who) : ℝ :=
  G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who -
  G.mixedExtension.eu σ who

open Classical in
/-- Weighted gain sum is zero: the expectation of gain under the current
    mixed strategy is zero. -/
theorem weighted_gain_sum_zero
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) :
    expect (σ who) (fun a => G.mixedGain σ who a) = 0 := by
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun ω => |G.utility ω who|) :=
    Finite.bddAbove_range _
  exact G.weighted_gain_sum_zero_of_bounded σ who (fun ω => hC ⟨ω, rfl⟩)

open Classical in
/-- A mixed profile is Nash iff all pure-deviation gains are non-positive. -/
theorem isNash_iff_gains_nonpos
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedExtension.IsNash σ ↔
      ∀ who (a : G.Strategy who), G.mixedGain σ who a ≤ 0 := by
  have hbd : ∀ who, ∃ C : ℝ, ∀ ω, |G.utility ω who| ≤ C := fun who =>
    let ⟨C, hC⟩ := (Finite.bddAbove_range fun ω => |G.utility ω who|)
    ⟨C, fun ω => hC ⟨ω, rfl⟩⟩
  choose C hC using hbd
  simpa [mixedGain] using G.isNash_iff_gains_nonpos_of_bounded σ
    (C := C) (fun who => hC who)

end NashGain

-- ============================================================================
-- Convergence of mixed-extension expected utility
-- ============================================================================

section MixedExtensionConvergence

variable [Fintype ι]
variable (G : KernelGame ι)
variable [Finite G.Outcome]

open Filter

omit [DecidableEq ι] in
/--
If each marginal mixed strategy converges pointwise as a PMF, then mixed
expected utility converges.
-/
theorem mixedExtension_eu_tendsto_of_forall_pmfConvergesPointwise
    {σs : ℕ → Profile G.mixedExtension} {σ : Profile G.mixedExtension}
    (hσ : ∀ i, PMFConvergesPointwise (fun n : ℕ => σs n i) (σ i))
    (who : ι) :
    Tendsto (fun n : ℕ => G.mixedExtension.eu (σs n) who) atTop
      (nhds (G.mixedExtension.eu σ who)) := by
  have hprod : ∀ s : Profile G,
      Tendsto (fun n : ℕ => pmfPi (A := G.Strategy) (σs n) s) atTop
        (nhds (pmfPi (A := G.Strategy) σ s)) := by
    intro s
    exact Math.PMFProduct.pmfPi_apply_tendsto (A := G.Strategy) s
      (fun i => (hσ i).apply (s i))
  have hexpect :
      Tendsto
        (fun n : ℕ => expect (pmfPi (A := G.Strategy) (σs n))
          (fun s : Profile G => G.eu s who))
        atTop
        (nhds (expect (pmfPi (A := G.Strategy) σ)
          (fun s : Profile G => G.eu s who))) :=
    by
      obtain ⟨C, hC⟩ :=
        Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω who)
      exact Math.Probability.expect_tendsto_of_forall_tendsto_of_bounded
        (fun s : Profile G => G.eu s who)
        (fun s => G.eu_abs_le_of_bounded who hC s) hprod
  rw [show (fun n : ℕ => G.mixedExtension.eu (σs n) who) =
      fun n : ℕ => expect (pmfPi (A := G.Strategy) (σs n))
        (fun s : Profile G => G.eu s who) by
        funext n
        rw [G.mixedExtension_eu]]
  rw [G.mixedExtension_eu σ who]
  exact hexpect

omit [DecidableEq ι] in
/--
Version of `mixedExtension_eu_tendsto_of_forall_pmfConvergesPointwise` phrased
with the library's generic profile-convergence predicate.
-/
theorem mixedExtension_eu_tendsto_of_profileConvergesPointwise
    {σs : ℕ → Profile G.mixedExtension} {σ : Profile G.mixedExtension}
    (hσ : ProfileConvergesWith
      (fun i => @PMFConvergesPointwise (G.Strategy i)) σs σ)
    (who : ι) :
    Tendsto (fun n : ℕ => G.mixedExtension.eu (σs n) who) atTop
      (nhds (G.mixedExtension.eu σ who)) :=
  G.mixedExtension_eu_tendsto_of_forall_pmfConvergesPointwise hσ who

/--
Pure-deviation expected utility is continuous under pointwise convergence of
the ambient mixed profile.
-/
theorem mixedExtension_eu_update_pure_tendsto_of_forall_pmfConvergesPointwise
    {σs : ℕ → Profile G.mixedExtension} {σ : Profile G.mixedExtension}
    (hσ : ∀ i, PMFConvergesPointwise (fun n : ℕ => σs n i) (σ i))
    (who : ι) (a : G.Strategy who) :
    Tendsto
      (fun n : ℕ =>
        G.mixedExtension.eu (Function.update (σs n) who (PMF.pure a)) who)
      atTop
      (nhds (G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who)) := by
  refine G.mixedExtension_eu_tendsto_of_forall_pmfConvergesPointwise
    (σs := fun n : ℕ => Function.update (σs n) who (PMF.pure a))
    (σ := Function.update σ who (PMF.pure a)) ?_ who
  intro i b
  by_cases hi : i = who
  · subst hi
    simp
  · simpa [hi] using (hσ i).apply b

/--
Pure-deviation gains are continuous under pointwise convergence of the mixed
profile.
-/
theorem mixedGain_tendsto_of_forall_pmfConvergesPointwise
    {σs : ℕ → Profile G.mixedExtension} {σ : Profile G.mixedExtension}
    (hσ : ∀ i, PMFConvergesPointwise (fun n : ℕ => σs n i) (σ i))
    (who : ι) (a : G.Strategy who) :
    Tendsto (fun n : ℕ => G.mixedGain (σs n) who a) atTop
      (nhds (G.mixedGain σ who a)) := by
  unfold mixedGain
  exact
    (G.mixedExtension_eu_update_pure_tendsto_of_forall_pmfConvergesPointwise
      hσ who a).sub
    (G.mixedExtension_eu_tendsto_of_forall_pmfConvergesPointwise hσ who)

end MixedExtensionConvergence

-- ============================================================================
-- Uniform mixed profiles
-- ============================================================================

section UniformMixed

variable [Fintype ι]
variable (G : KernelGame ι)
variable [∀ i, Fintype (G.Strategy i)]
variable [∀ i, Nonempty (G.Strategy i)]

/-- The independent profile where every player uses the uniform distribution on
their finite strategy set. -/
def uniformMixedProfile : Profile G.mixedExtension :=
  fun i => PMF.uniformOfFintype (G.Strategy i)

/-- A game is balanced at the uniform mixed profile if every pure unilateral
deviation gives the same expected utility as the uniform profile itself.

For a two-player matrix game, this is the semantic version of every row and
column having the same average payoff against uniform play. -/
def IsUniformMixedBalanced : Prop :=
  ∀ who (a : G.Strategy who),
    G.mixedExtension.eu (Function.update G.uniformMixedProfile who (PMF.pure a)) who =
      G.mixedExtension.eu G.uniformMixedProfile who

open Classical in
/-- Under bounded utility, balance at the uniform mixed profile implies that the
uniform mixed profile is Nash. -/
theorem IsUniformMixedBalanced.uniformMixedProfile_isNash_of_bounded
    (hbal : G.IsUniformMixedBalanced)
    {C : ι → ℝ} (hbd : ∀ who ω, |G.utility ω who| ≤ C who) :
    G.mixedExtension.IsNash G.uniformMixedProfile := by
  rw [G.isNash_iff_gains_nonpos_of_bounded G.uniformMixedProfile (C := C) hbd]
  intro who a
  rw [hbal who a]
  simp

/-- For finite-outcome games, uniform balance is equivalently zero pure-deviation
gain at the uniform mixed profile. -/
theorem isUniformMixedBalanced_iff_mixedGain_eq_zero :
    G.IsUniformMixedBalanced ↔
      ∀ who (a : G.Strategy who), G.mixedGain G.uniformMixedProfile who a = 0 := by
  simp [IsUniformMixedBalanced, mixedGain, sub_eq_zero]

variable [Finite G.Outcome]

/-- With finite outcomes, balance at the uniform mixed profile implies that the
uniform mixed profile is Nash. -/
theorem IsUniformMixedBalanced.uniformMixedProfile_isNash
    (hbal : G.IsUniformMixedBalanced) :
    G.mixedExtension.IsNash G.uniformMixedProfile := by
  rw [G.isNash_iff_gains_nonpos G.uniformMixedProfile]
  intro who a
  unfold mixedGain
  rw [hbal who a]
  simp

end UniformMixed

end KernelGame

end GameTheory
