/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.Correlation.CorrelatedEqProperties
import Math.ProbabilityMassFunction

/-!
# GameTheory.Concepts.Correlation.CorrelatedNashMixed

Relates correlated expected utility under point-mass distributions to standard
expected utility, and establishes how deviation distributions simplify under
product (mixed) profile distributions. Point-mass deviation simplifications
live in `GameTheory.Concepts.Foundations.Deviation`.

Provides:
- `correlatedEu_pure` — correlated EU under `PMF.pure σ` equals `eu σ`
- `unilateralDeviationDistribution_pmfPi` — deviation of a product distribution equals
  the product with the deviated component's pushforward
- `correlatedEu_eq_expect_eu` — correlated EU is the expectation of EU
  over the profile distribution
- `mixed_nash_isCorrelatedEq` — a mixed Nash profile induces a CE
- `correlatedEq_exists` — every finite game has a correlated equilibrium
- `coarseCorrelatedEq_exists` — corollary: every finite game has a CCE
-/

namespace GameTheory

open Math.Probability
open Math.ProbabilityMassFunction
namespace KernelGame
open Math.PMFProduct

attribute [local instance] Fintype.ofFinite

variable {ι : Type} {G : KernelGame ι}

/-- Correlated EU under a point-mass distribution equals the standard EU. -/
theorem correlatedEu_pure (σ : Profile G) (who : ι) :
    G.correlatedEu (PMF.pure σ) who = G.eu σ who := by
  simp [correlatedEu, eu, correlatedOutcome, Kernel.pushforward]

/-- Correlated EU equals the expectation of standard EU over the profile distribution,
    under bounded utility. -/
theorem correlatedEu_eq_expect_eu_of_bounded
    (μ : PMF (Profile G)) (who : ι)
    {C : ℝ} (hbd : ∀ ω, |G.utility ω who| ≤ C) :
    G.correlatedEu μ who = expect μ (fun σ => G.eu σ who) := by
  simp only [correlatedEu, eu, correlatedOutcome, Kernel.pushforward]
  exact expect_bind_of_bounded μ G.outcomeKernel (fun ω => G.utility ω who) hbd

/-- Correlated EU is the expectation of standard EU over the profile
    distribution. -/
theorem correlatedEu_eq_expect_eu [Finite G.Outcome]
    (μ : PMF (Profile G)) (who : ι) :
    G.correlatedEu μ who = expect μ (fun σ => G.eu σ who) := by
  obtain ⟨C, hbd⟩ :=
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω who)
  exact G.correlatedEu_eq_expect_eu_of_bounded μ who hbd

variable [DecidableEq ι]

/-! ### Correlated EU after a deviation distribution

These express the correlated EU of a (constant or recommendation-dependent)
deviation distribution as the expectation of the deviated per-recommendation EU.
They are general facts about `correlatedEu`, used wherever deviation incentives
are reasoned about (constant-sum value, signal timing, …). -/

theorem correlatedEu_constantDeviationDistribution_eq_expect_update_of_bounded
    {G : KernelGame ι} (μ : PMF (Profile G)) (who : ι) (s' : G.Strategy who)
    {C : ℝ} (hbd : ∀ ω, |G.utility ω who| ≤ C) :
    G.correlatedEu (G.constantDeviationDistribution μ who s') who =
      expect μ (fun σ => G.eu (Function.update σ who s') who) := by
  rw [G.correlatedEu_eq_expect_eu_of_bounded
    (μ := G.constantDeviationDistribution μ who s') who hbd]
  unfold constantDeviationDistribution deviationDistribution constantDeviation
  rw [expect_bind_of_bounded μ (fun σ => PMF.pure (Function.update σ who s'))
    (fun τ => G.eu τ who)
    (fun τ => G.eu_abs_le_of_bounded who hbd τ)]
  apply tsum_congr
  intro σ
  simp [expect_pure]

theorem correlatedEu_constantDeviationDistribution_eq_expect_update
    {G : KernelGame ι} [Finite G.Outcome]
    (μ : PMF (Profile G)) (who : ι) (s' : G.Strategy who) :
    G.correlatedEu (G.constantDeviationDistribution μ who s') who =
      expect μ (fun σ => G.eu (Function.update σ who s') who) := by
  classical
  obtain ⟨C, hbd⟩ :=
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω who)
  exact correlatedEu_constantDeviationDistribution_eq_expect_update_of_bounded
    (G := G) μ who s' hbd

theorem correlatedEu_unilateralDeviationDistribution_eq_expect_update_of_bounded
    {G : KernelGame ι} (μ : PMF (Profile G)) (who : ι)
    (dev : G.Strategy who → G.Strategy who)
    {C : ℝ} (hbd : ∀ ω, |G.utility ω who| ≤ C) :
    G.correlatedEu (G.unilateralDeviationDistribution μ who dev) who =
      expect μ (fun σ => G.eu (Function.update σ who (dev (σ who))) who) := by
  rw [G.correlatedEu_eq_expect_eu_of_bounded
    (μ := G.unilateralDeviationDistribution μ who dev) who hbd]
  unfold unilateralDeviationDistribution deviationDistribution unilateralDeviation
  rw [expect_bind_of_bounded μ
    (fun σ => PMF.pure (Function.update σ who (dev (σ who))))
    (fun τ => G.eu τ who)
    (fun τ => G.eu_abs_le_of_bounded who hbd τ)]
  apply tsum_congr
  intro σ
  simp [expect_pure]

theorem correlatedEu_unilateralDeviationDistribution_eq_expect_update
    {G : KernelGame ι} [Finite G.Outcome]
    (μ : PMF (Profile G)) (who : ι)
    (dev : G.Strategy who → G.Strategy who) :
    G.correlatedEu (G.unilateralDeviationDistribution μ who dev) who =
      expect μ (fun σ => G.eu (Function.update σ who (dev (σ who))) who) := by
  classical
  obtain ⟨C, hbd⟩ :=
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω who)
  exact correlatedEu_unilateralDeviationDistribution_eq_expect_update_of_bounded
    (G := G) μ who dev hbd

open Classical in
/-- Conditional obedience form of correlated equilibrium: after any
positive-probability recommendation, obeying that recommendation beats any
fixed replacement action in conditional expected utility. -/
theorem IsCorrelatedEq.conditional_obedience [Finite (Profile G)] [Finite G.Outcome]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    (who : ι) [Finite (G.Strategy who)] (s t : G.Strategy who)
    (hs : pmfMass (μ := μ) (fun σ => σ who = s) ≠ 0) :
    expect (pmfCond (μ := μ) (fun σ => σ who = s) hs)
        (fun σ => G.eu σ who) ≥
      expect (pmfCond (μ := μ) (fun σ => σ who = s) hs)
        (fun σ => G.eu (Function.update σ who t) who) := by
  letI : Fintype (Profile G) := Fintype.ofFinite (Profile G)
  let dev : G.Strategy who → G.Strategy who := fun a => if a = s then t else a
  have hle : expect μ
      (fun σ => G.eu (Function.update σ who (dev (σ who))) who) ≤
        expect μ (fun σ => G.eu σ who) := by
    have hce' := hce who dev
    rw [G.correlatedEu_eq_expect_eu μ who] at hce'
    rw [G.correlatedEu_unilateralDeviationDistribution_eq_expect_update μ who dev] at hce'
    exact hce'
  have hcond := expect_cond_le_of_expect_le_of_eq_off
    (μ := μ) (E := fun σ => σ who = s) (hE := hs)
    (f := fun σ => G.eu σ who)
    (g := fun σ => G.eu (Function.update σ who (dev (σ who))) who)
    hle ?_
  · have hdev_eq :
        expect (pmfCond (μ := μ) (fun σ => σ who = s) hs)
            (fun σ => G.eu (Function.update σ who (dev (σ who))) who) =
          expect (pmfCond (μ := μ) (fun σ => σ who = s) hs)
            (fun σ => G.eu (Function.update σ who t) who) := by
      exact expect_congr_of_ne_zero
        (pmfCond (μ := μ) (fun σ => σ who = s) hs)
        (fun σ => G.eu (Function.update σ who (dev (σ who))) who)
        (fun σ => G.eu (Function.update σ who t) who)
        (by
          intro σ hσ
          have hσs := pmfCond_ne_zero_implies μ (fun σ => σ who = s) hs hσ
          simp [dev, hσs])
    simpa [hdev_eq] using hcond
  · intro σ hσ
    have hdev : dev (σ who) = σ who := by
      simp [dev, hσ]
    simp [hdev, Function.update_eq_self]

open Classical in
/-- Deviation of a product distribution equals the product with the deviated
    component replaced by the pushforward of the original through `dev`. -/
theorem unilateralDeviationDistribution_pmfPi
    {G : KernelGame ι}
    [Fintype ι]
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι)
    (dev : G.Strategy who → G.Strategy who) :
    G.unilateralDeviationDistribution (pmfPi σ) who dev =
      pmfPi (Function.update σ who (PMF.map dev (σ who))) := by
  unfold KernelGame.unilateralDeviationDistribution KernelGame.deviationDistribution
  unfold KernelGame.unilateralDeviation
  exact pmfPi_bind_update_map σ who dev

open Classical in
/-- A mixed Nash profile induces a correlated equilibrium under bounded utility.

This assumes only a finite player index and bounded utility. Strategy carriers
may be countable, since `unilateralDeviationDistribution_pmfPi` is now proved
directly for product PMFs over arbitrary coordinate carriers. -/
theorem mixed_nash_isCorrelatedEq_of_bounded
    {G : KernelGame ι}
    [Fintype ι]
    (σ : ∀ i, PMF (G.Strategy i))
    (hN : G.mixedExtension.IsNash σ)
    {C : ι → ℝ} (hbd : ∀ who ω, |G.utility ω who| ≤ C who) :
    G.IsCorrelatedEq (pmfPi σ) := by
  intro who dev
  have hN' : G.mixedExtension.eu σ who ≥
      G.mixedExtension.eu (Function.update σ who (PMF.map dev (σ who))) who :=
    hN who (PMF.map dev (σ who))
  have hbase :
      G.correlatedEu (pmfPi σ) who = G.mixedExtension.eu σ who := by
    rw [G.correlatedEu_eq_expect_eu_of_bounded (μ := pmfPi σ) who (hbd who)]
    symm; exact G.mixedExtension_eu_of_bounded σ who (hbd who)
  have hdev :
      G.correlatedEu (G.unilateralDeviationDistribution (pmfPi σ) who dev) who =
      G.mixedExtension.eu
        (Function.update σ who (PMF.map dev (σ who))) who := by
    rw [G.correlatedEu_eq_expect_eu_of_bounded
      (μ := G.unilateralDeviationDistribution (pmfPi σ) who dev) who (hbd who)]
    rw [G.unilateralDeviationDistribution_pmfPi σ who dev]
    symm
    exact G.mixedExtension_eu_of_bounded
      (Function.update σ who (PMF.map dev (σ who))) who (hbd who)
  rw [hbase, hdev]
  exact hN'

open Classical in
/-- A mixed Nash profile induces a correlated equilibrium on pure profiles
    via the independent product distribution `pmfPi σ`.

    For any deviation function `dev`, the deviated distribution
    `unilateralDeviationDistribution (pmfPi σ) who dev` equals
    `pmfPi (update σ who (PMF.map dev (σ who)))`. By Nash optimality,
    the pushforward mixed strategy `PMF.map dev (σ who)` cannot improve
    player `who`'s EU. -/
theorem mixed_nash_isCorrelatedEq
    {G : KernelGame ι}
    [Fintype ι] [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i))
    (hN : G.mixedExtension.IsNash σ) :
    G.IsCorrelatedEq (pmfPi σ) := by
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact G.mixed_nash_isCorrelatedEq_of_bounded σ hN hbd

open Classical in
/-- **Correlated equilibrium support avoids relatively dominated actions.** If
`t` beats `s` in expected utility for player `who` at every profile satisfying
`S`, and `μ`'s support satisfies `S`, then no positive-probability profile in
`μ` recommends `s` to `who`. The relativization to `S` is what makes this the
right building block for an induction over rounds of iterated dominance (`S` =
"every player plays a round-`n` survivor"); the unrestricted case
(`S := fun _ => True`) recovers "CE support avoids a globally strictly
dominated action". -/
theorem IsCorrelatedEq.support_avoids_dominated_relative
    {G : KernelGame ι} [Finite (Profile G)] [Finite G.Outcome]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    (S : Profile G → Prop) (hS : ∀ σ, μ σ ≠ 0 → S σ)
    (who : ι) {s t : G.Strategy who}
    (hdom : ∀ σ, S σ →
      G.eu (Function.update σ who t) who > G.eu (Function.update σ who s) who) :
    ∀ σ, μ σ ≠ 0 → σ who ≠ s := by
  intro σ0 hσ0 hσ0eq
  set dev : G.Strategy who → G.Strategy who := fun a => if a = s then t else a with hdev_def
  have hce' := hce who dev
  rw [G.correlatedEu_eq_expect_eu μ who] at hce'
  rw [G.correlatedEu_unilateralDeviationDistribution_eq_expect_update μ who dev] at hce'
  have hle : ∀ σ, G.eu σ who ≤
      (if S σ then G.eu (Function.update σ who (dev (σ who))) who else G.eu σ who) := by
    intro σ
    by_cases hSσ : S σ
    · rw [if_pos hSσ]
      by_cases h : σ who = s
      · have hdevσ : dev (σ who) = t := by simp [hdev_def, h]
        have heq : Function.update σ who s = σ := by rw [← h]; exact Function.update_eq_self _ _
        rw [hdevσ]
        have hd := hdom σ hSσ
        have heu : G.eu σ who = G.eu (Function.update σ who s) who := by rw [heq]
        rw [heu]
        exact le_of_lt hd
      · have hdevσ : dev (σ who) = σ who := by simp [hdev_def, h]
        rw [hdevσ, Function.update_eq_self]
    · rw [if_neg hSσ]
  have hlt0 : G.eu σ0 who <
      (if S σ0 then G.eu (Function.update σ0 who (dev (σ0 who))) who else G.eu σ0 who) := by
    rw [if_pos (hS σ0 hσ0)]
    have hdevσ0 : dev (σ0 who) = t := by simp [hdev_def, hσ0eq]
    have heq : Function.update σ0 who s = σ0 := by rw [← hσ0eq]; exact Function.update_eq_self _ _
    rw [hdevσ0]
    have hd := hdom σ0 (hS σ0 hσ0)
    calc G.eu σ0 who = G.eu (Function.update σ0 who s) who := by rw [heq]
      _ < G.eu (Function.update σ0 who t) who := hd
  have hstrict := Math.Probability.expect_lt_of_le_of_exists_lt μ
    (fun σ => G.eu σ who)
    (fun σ => if S σ then G.eu (Function.update σ who (dev (σ who))) who else G.eu σ who)
    hle ⟨σ0, hσ0, hlt0⟩
  have hcongr : Math.Probability.expect μ
      (fun σ => if S σ then G.eu (Function.update σ who (dev (σ who))) who else G.eu σ who) =
      Math.Probability.expect μ (fun σ => G.eu (Function.update σ who (dev (σ who))) who) := by
    apply Math.ProbabilityMassFunction.expect_congr_of_ne_zero
    intro σ hσ
    rw [if_pos (hS σ hσ)]
  rw [hcongr] at hstrict
  linarith

end KernelGame
end GameTheory
