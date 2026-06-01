/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.CorrelatedNashMixed
import Math.PMFProduct
import Math.ProbabilityMassFunction

/-!
# Correlation Regimes

Public-signal Nash is weaker than mediated correlation.  A public signal can
select a mixed Nash equilibrium, but because the signal is common knowledge,
players condition on the signal before choosing actions.  The induced profile
law is therefore a mixture of product distributions coming from Nash profiles.

This file records the basic ladder:

* mixtures of correlated equilibria are correlated equilibria;
* every public-signal Nash regime induces a correlated equilibrium;
* public-regime payoffs are PMF-supported mixtures of mixed-Nash payoffs.
-/

noncomputable section

namespace GameTheory

open Math.Probability

namespace KernelGame

open Math.PMFProduct

variable {ι Signal : Type}

/-! ## Mixtures of correlated equilibria -/

theorem expect_mono_of_ne_zero_bounded
    {α : Type} (d : PMF α) (f g : α → ℝ)
    (hfg : ∀ a, d a ≠ 0 → f a ≤ g a)
    {C : ℝ} (hf : ∀ a, |f a| ≤ C) (hg : ∀ a, |g a| ≤ C) :
    expect d f ≤ expect d g := by
  let f' : α → ℝ := fun a => if d a = 0 then g a else f a
  have hf_eq : expect d f = expect d f' := by
    exact Math.ProbabilityMassFunction.expect_congr_of_ne_zero d f f'
      (fun a ha => by simp [f', ha])
  rw [hf_eq]
  apply Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
    (d := d) (f := f') (g := g)
    (hfg := fun a => by
      by_cases ha : d a = 0
      · simp [f', ha]
      · simp [f', ha, hfg a ha])
    (C := C)
    (hf := fun a => by
      by_cases ha : d a = 0
      · simp [f', ha, hg a]
      · simp [f', ha, hf a])
    (hg := hg)

theorem correlatedEu_abs_le_of_bounded
    {G : KernelGame ι} (μ : PMF (Profile G)) (who : ι)
    {C : ℝ} (hbd : ∀ ω, |G.utility ω who| ≤ C) :
    |G.correlatedEu μ who| ≤ C := by
  let d : PMF G.Outcome := G.correlatedOutcome μ
  have h_summable :=
    Math.Probability.expect_summable_of_bounded d
      (fun ω => G.utility ω who) hbd
  have h_summable_bd : Summable (fun ω : G.Outcome => (d ω).toReal * C) :=
    (Math.Probability.pmf_toReal_summable d).mul_right C
  have h_sum_one : ∑' ω : G.Outcome, (d ω).toReal * C = C := by
    rw [tsum_mul_right, Math.Probability.pmf_toReal_tsum_one, one_mul]
  have h_upper : G.correlatedEu μ who ≤ C := by
    have h_le : ∀ ω : G.Outcome,
        (d ω).toReal * G.utility ω who ≤ (d ω).toReal * C := by
      intro ω
      exact mul_le_mul_of_nonneg_left (le_of_abs_le (hbd ω)) ENNReal.toReal_nonneg
    calc
      G.correlatedEu μ who
          = ∑' ω : G.Outcome, (d ω).toReal * G.utility ω who := rfl
      _ ≤ ∑' ω : G.Outcome, (d ω).toReal * C :=
          h_summable.tsum_le_tsum h_le h_summable_bd
      _ = C := h_sum_one
  have h_lower : -C ≤ G.correlatedEu μ who := by
    have h_le : ∀ ω : G.Outcome,
        -((d ω).toReal * C) ≤ (d ω).toReal * G.utility ω who := by
      intro ω
      have h_neg_le : -C ≤ G.utility ω who := neg_le_of_abs_le (hbd ω)
      have hd : 0 ≤ (d ω).toReal := ENNReal.toReal_nonneg
      have := mul_le_mul_of_nonneg_left h_neg_le hd
      linarith
    calc
      (-C : ℝ) = -∑' ω : G.Outcome, (d ω).toReal * C := by rw [h_sum_one]
      _ = ∑' ω : G.Outcome, -((d ω).toReal * C) := (tsum_neg).symm
      _ ≤ ∑' ω : G.Outcome, (d ω).toReal * G.utility ω who :=
          h_summable_bd.neg.tsum_le_tsum h_le h_summable
      _ = G.correlatedEu μ who := rfl
  exact abs_le.mpr ⟨h_lower, h_upper⟩

theorem correlatedEu_abs_le
    {G : KernelGame ι} [Finite G.Outcome]
    (μ : PMF (Profile G)) (who : ι) :
    |G.correlatedEu μ who| ≤
      Classical.choose (Math.Probability.exists_abs_bound_of_finite
        (fun ω => G.utility ω who)) := by
  classical
  exact G.correlatedEu_abs_le_of_bounded μ who
    (Classical.choose_spec (Math.Probability.exists_abs_bound_of_finite
      (fun ω => G.utility ω who)))

theorem correlatedEu_bind_of_bounded
    {G : KernelGame ι} (ν : PMF Signal) (κ : Signal → PMF (Profile G))
    (who : ι) {C : ℝ} (hbd : ∀ ω, |G.utility ω who| ≤ C) :
    G.correlatedEu (ν.bind κ) who =
      expect ν (fun z => G.correlatedEu (κ z) who) := by
  rw [G.correlatedEu_eq_expect_eu_of_bounded (μ := ν.bind κ) who hbd]
  rw [expect_bind_of_bounded ν κ (fun σ => G.eu σ who)
    (fun σ => G.eu_abs_le_of_bounded who hbd σ)]
  apply congrArg
  funext z
  rw [G.correlatedEu_eq_expect_eu_of_bounded (μ := κ z) who hbd]

theorem correlatedEu_bind
    {G : KernelGame ι} [Finite G.Outcome]
    (ν : PMF Signal) (κ : Signal → PMF (Profile G)) (who : ι) :
    G.correlatedEu (ν.bind κ) who =
      expect ν (fun z => G.correlatedEu (κ z) who) := by
  classical
  obtain ⟨C, hbd⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun ω => G.utility ω who)
  exact G.correlatedEu_bind_of_bounded ν κ who hbd

theorem unilateralDeviationDistribution_bind
    [DecidableEq ι] {G : KernelGame ι}
    (ν : PMF Signal) (κ : Signal → PMF (Profile G))
    (who : ι) (dev : G.Strategy who → G.Strategy who) :
    G.unilateralDeviationDistribution (ν.bind κ) who dev =
      ν.bind (fun z => G.unilateralDeviationDistribution (κ z) who dev) := by
  simp [unilateralDeviationDistribution, deviationDistribution, unilateralDeviation,
    PMF.bind_bind]

theorem isCorrelatedEq_bind_of_bounded
    [DecidableEq ι] {G : KernelGame ι}
    (ν : PMF Signal) (κ : Signal → PMF (Profile G))
    (hκ : ∀ z, ν z ≠ 0 → G.IsCorrelatedEq (κ z))
    {C : ι → ℝ} (hbd : ∀ who ω, |G.utility ω who| ≤ C who) :
    G.IsCorrelatedEq (ν.bind κ) := by
  intro who dev
  rw [G.correlatedEu_bind_of_bounded ν κ who (hbd who)]
  rw [G.unilateralDeviationDistribution_bind ν κ who dev]
  rw [G.correlatedEu_bind_of_bounded ν
    (fun z => G.unilateralDeviationDistribution (κ z) who dev) who (hbd who)]
  exact expect_mono_of_ne_zero_bounded
    (d := ν)
    (f := fun z => G.correlatedEu (G.unilateralDeviationDistribution (κ z) who dev) who)
    (g := fun z => G.correlatedEu (κ z) who)
    (hfg := fun z hz => hκ z hz who dev)
    (C := C who)
    (hf := fun z => G.correlatedEu_abs_le_of_bounded
      (G.unilateralDeviationDistribution (κ z) who dev) who (hbd who))
    (hg := fun z => G.correlatedEu_abs_le_of_bounded (κ z) who (hbd who))

theorem isCorrelatedEq_bind
    [DecidableEq ι] {G : KernelGame ι} [Finite G.Outcome]
    (ν : PMF Signal) (κ : Signal → PMF (Profile G))
    (hκ : ∀ z, ν z ≠ 0 → G.IsCorrelatedEq (κ z)) :
    G.IsCorrelatedEq (ν.bind κ) := by
  classical
  choose C hbd using fun who =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω who)
  exact G.isCorrelatedEq_bind_of_bounded ν κ hκ hbd

/-! ## Public-signal Nash -/

/-- The law over pure profiles induced by a public signal that selects a mixed
profile.  Conditional on signal `z`, players independently sample actions from
`play z`. -/
noncomputable def publicCorrelatedLaw
    (G : KernelGame ι) [Fintype ι]
    (ν : PMF Signal) (play : Signal → Profile G.mixedExtension) :
    PMF (Profile G) :=
  ν.bind fun z => pmfPi (play z)

/-- Public-signal Nash: every positive-probability public signal selects a
mixed Nash equilibrium of the base game. -/
def PublicSignalNash
    (G : KernelGame ι) [Fintype ι] [DecidableEq ι] (ν : PMF Signal)
    (play : Signal → Profile G.mixedExtension) : Prop :=
  ∀ z, ν z ≠ 0 → G.mixedExtension.IsNash (play z)

theorem correlatedEu_pmfPi_eq_mixedExtension_eu_of_bounded
    {G : KernelGame ι} [Fintype ι]
    (σ : Profile G.mixedExtension) (who : ι)
    {C : ℝ} (hbd : ∀ ω, |G.utility ω who| ≤ C) :
    G.correlatedEu (pmfPi σ) who = G.mixedExtension.eu σ who := by
  rw [G.correlatedEu_eq_expect_eu_of_bounded (μ := pmfPi σ) who hbd]
  exact (G.mixedExtension_eu_of_bounded σ who hbd).symm

theorem correlatedEu_pmfPi_eq_mixedExtension_eu
    {G : KernelGame ι} [Fintype ι] [Finite G.Outcome]
    (σ : Profile G.mixedExtension) (who : ι) :
    G.correlatedEu (pmfPi σ) who = G.mixedExtension.eu σ who := by
  classical
  obtain ⟨C, hbd⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun ω => G.utility ω who)
  exact G.correlatedEu_pmfPi_eq_mixedExtension_eu_of_bounded σ who hbd

theorem PublicSignalNash.isCorrelatedEq_of_bounded
    [Fintype ι] [DecidableEq ι] {G : KernelGame ι}
    {ν : PMF Signal} {play : Signal → Profile G.mixedExtension}
    (hpub : G.PublicSignalNash ν play)
    {C : ι → ℝ} (hbd : ∀ who ω, |G.utility ω who| ≤ C who) :
    G.IsCorrelatedEq (G.publicCorrelatedLaw ν play) := by
  unfold publicCorrelatedLaw
  apply G.isCorrelatedEq_bind_of_bounded ν (fun z => pmfPi (play z)) ?_ hbd
  intro z hz
  exact G.mixed_nash_isCorrelatedEq_of_bounded (play z) (hpub z hz) hbd

theorem PublicSignalNash.isCorrelatedEq
    [Fintype ι] [DecidableEq ι] {G : KernelGame ι} [Finite G.Outcome]
    {ν : PMF Signal} {play : Signal → Profile G.mixedExtension}
    (hpub : G.PublicSignalNash ν play) :
    G.IsCorrelatedEq (G.publicCorrelatedLaw ν play) := by
  classical
  choose C hbd using fun who =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω who)
  exact hpub.isCorrelatedEq_of_bounded hbd

/-! ## Payoff mixtures over Nash equilibria -/

/-- A payoff vector is a PMF-supported mixture of mixed-Nash payoff vectors. -/
def IsMixedNashPayoffMixture
    (G : KernelGame ι) [Fintype ι] [DecidableEq ι] (x : ι → ℝ) : Prop :=
  ∃ (α : Type) (ν : PMF α) (play : α → Profile G.mixedExtension),
    (∀ z, ν z ≠ 0 → G.mixedExtension.IsNash (play z)) ∧
      ∀ i, x i = expect ν (fun z => G.mixedExtension.eu (play z) i)

/-- Payoff vector generated directly by the public signal regime. -/
noncomputable def publicRegimePayoff
    (G : KernelGame ι) [Fintype ι] (ν : PMF Signal)
    (play : Signal → Profile G.mixedExtension) : ι → ℝ :=
  fun i => expect ν (fun z => G.mixedExtension.eu (play z) i)

theorem PublicSignalNash.publicRegimePayoff_isMixedNashPayoffMixture
    [Fintype ι] [DecidableEq ι] {G : KernelGame ι} {ν : PMF Signal}
    {play : Signal → Profile G.mixedExtension}
    (hpub : G.PublicSignalNash ν play) :
    G.IsMixedNashPayoffMixture (G.publicRegimePayoff ν play) :=
  ⟨Signal, ν, play, hpub, fun _ => rfl⟩

theorem correlatedEu_publicCorrelatedLaw_eq_publicRegimePayoff_of_bounded
    [Fintype ι] {G : KernelGame ι}
    (ν : PMF Signal) (play : Signal → Profile G.mixedExtension)
    (who : ι) {C : ℝ} (hbd : ∀ ω, |G.utility ω who| ≤ C) :
    G.correlatedEu (G.publicCorrelatedLaw ν play) who =
      G.publicRegimePayoff ν play who := by
  unfold publicCorrelatedLaw publicRegimePayoff
  rw [G.correlatedEu_bind_of_bounded ν (fun z => pmfPi (play z)) who hbd]
  apply congrArg
  funext z
  rw [G.correlatedEu_pmfPi_eq_mixedExtension_eu_of_bounded (play z) who hbd]

theorem correlatedEu_publicCorrelatedLaw_eq_publicRegimePayoff
    [Fintype ι] {G : KernelGame ι} [Finite G.Outcome]
    (ν : PMF Signal) (play : Signal → Profile G.mixedExtension) (who : ι) :
    G.correlatedEu (G.publicCorrelatedLaw ν play) who =
      G.publicRegimePayoff ν play who := by
  classical
  obtain ⟨C, hbd⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun ω => G.utility ω who)
  exact G.correlatedEu_publicCorrelatedLaw_eq_publicRegimePayoff_of_bounded
    ν play who hbd

theorem PublicSignalNash.correlatedPayoff_isMixedNashPayoffMixture_of_bounded
    [Fintype ι] [DecidableEq ι] {G : KernelGame ι}
    {ν : PMF Signal} {play : Signal → Profile G.mixedExtension}
    (hpub : G.PublicSignalNash ν play)
    {C : ι → ℝ} (hbd : ∀ who ω, |G.utility ω who| ≤ C who) :
    G.IsMixedNashPayoffMixture
      (fun i => G.correlatedEu (G.publicCorrelatedLaw ν play) i) := by
  refine ⟨Signal, ν, play, hpub, ?_⟩
  intro i
  exact G.correlatedEu_publicCorrelatedLaw_eq_publicRegimePayoff_of_bounded
    ν play i (hbd i)

theorem PublicSignalNash.correlatedPayoff_isMixedNashPayoffMixture
    [Fintype ι] [DecidableEq ι] {G : KernelGame ι} [Finite G.Outcome]
    {ν : PMF Signal} {play : Signal → Profile G.mixedExtension}
    (hpub : G.PublicSignalNash ν play) :
    G.IsMixedNashPayoffMixture
      (fun i => G.correlatedEu (G.publicCorrelatedLaw ν play) i) := by
  classical
  choose C hbd using fun who =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω who)
  exact hpub.correlatedPayoff_isMixedNashPayoffMixture_of_bounded hbd

end KernelGame

end GameTheory
