/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Correlation.CorrelationRegimes
import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import GameTheory.Concepts.Correlation.CorrelatedEqProperties
import GameTheory.Concepts.Equilibrium.NashCorrelatedEq
import GameTheory.Concepts.Dominance.StrictDominance
import GameTheory.Concepts.Dominance.DominanceSolvability

/-!
# GameTheory.Concepts.Correlation.CorrelationSaturation

**Correlation saturation**: a game is saturated when no correlation device buys
anything beyond public randomization over its mixed Nash equilibria. Every
correlated (or coarse correlated) equilibrium law is already realizable as a
public signal that selects a mixed Nash equilibrium
(`PublicSignalNash.isCorrelatedEq`, in `CorrelationRegimes.lean`, gives the
reverse containment for free, for any game). Saturation is the nontrivial
direction: `IsCorrelatedEq`/`IsCoarseCorrelatedEq` give nothing that
`PublicSignalNash` didn't already.

This is strictly more general than a game having a unique (dominant-strategy)
equilibrium: any game whose correlated-equilibrium set of *laws* coincides with
the public-randomization hull of its mixed-Nash laws is saturated, even with
many equilibria. (This is a statement about probability laws, not payoff
vectors — different correlated laws can realize the same payoff vector, so
payoff-level saturation would be a strictly weaker notion.) The
dominant-strategy case is the degenerate one-signal instance.

The dominant-strategy singleton fact is proved at the **coarse** correlated
equilibrium level (`strictDominant_isCoarseCorrelatedEq_iff`), which is
strictly stronger than the correlated-equilibrium version
(`strictDominant_isCorrelatedEq_iff`, now a one-line corollary via
`IsCorrelatedEq.toCoarseCorrelatedEq`): the proof only ever tests the
*unconditional* deviation "always play the dominant action", which is exactly
the class of deviations a CCE, not just a CE, already rules out.

Provides:
- `strictDominant_isCoarseCorrelatedEq_iff` / `strictDominant_isCorrelatedEq_iff`
  — with a strictly dominant strategy for every player, a distribution is a
  (coarse) correlated equilibrium iff it is the point mass at the
  dominant-strategy profile.
- `IsSaturatedFor` — `G` is saturated for an equilibrium predicate `E` when
  every `μ` satisfying `E` is a public-signal-Nash law; `IsSaturatedFor.mono`
  transports saturation along an implication between predicates.
- `IsCorrelationSaturated`, `IsCoarseCorrelationSaturated` — `IsSaturatedFor`
  specialized to CE and CCE; the latter is the stronger notion, since CE ⊆ CCE.
- `strictDominant_isCoarseCorrelationSaturated` / `strictDominant_isCorrelationSaturated`
  — a strictly dominant-strategy profile saturates (coarse) correlation, via
  the single constant signal selecting it.
-/

namespace GameTheory

open Math.Probability
open Math.ProbabilityMassFunction

namespace KernelGame

variable {ι : Type} [DecidableEq ι] {G : KernelGame ι}

open Classical in
/-- **Dominant strategies saturate coarse correlated equilibrium.** If every
player has a strictly dominant strategy, the profile of those strategies is the
*unique* coarse correlated equilibrium. The proof only ever tests the
unconditional deviation "always play the dominant action", so it already
defeats every CCE deviation, not just CE deviations. -/
theorem strictDominant_isCoarseCorrelatedEq_iff [Finite G.Outcome]
    {σ : Profile G} (hdom : ∀ i, G.IsStrictDominant i (σ i)) {μ : PMF (Profile G)} :
    G.IsCoarseCorrelatedEq μ ↔ μ = PMF.pure σ := by
  constructor
  · intro hCE
    have hcoord : ∀ (who : ι) (τ : Profile G), μ τ ≠ 0 → τ who = σ who := by
      intro who
      obtain ⟨C0, hbd0⟩ := Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω who)
      set C := max C0 0 with hC_def
      have hCnn : (0:ℝ) ≤ C := le_max_right _ _
      have hbd : ∀ ω, |G.utility ω who| ≤ C := fun ω => (hbd0 ω).trans (le_max_left _ _)
      set f : Profile G → ℝ :=
        fun τ => G.eu τ who - G.eu (Function.update τ who (σ who)) who with hf_def
      have hnonpos : ∀ τ, f τ ≤ 0 := by
        intro τ
        by_cases h : τ who = σ who
        · have hself : Function.update τ who (σ who) = τ := by
            rw [← h]; exact Function.update_eq_self _ _
          simp [hf_def, hself]
        · have hself : Function.update τ who (τ who) = τ := Function.update_eq_self _ _
          have hgt := hdom who τ (τ who) h
          rw [hself] at hgt
          simp only [hf_def]
          linarith
      have hbdf : ∀ τ, |f τ| ≤ 2 * C := by
        intro τ
        have h1 : |G.eu τ who| ≤ C := G.eu_abs_le_of_bounded who hbd τ
        have h2 : |G.eu (Function.update τ who (σ who)) who| ≤ C :=
          G.eu_abs_le_of_bounded who hbd _
        have := abs_sub (G.eu τ who) (G.eu (Function.update τ who (σ who)) who)
        simp only [hf_def]
        linarith
      have hge0 : (0 : ℝ) ≤ Math.Probability.expect μ f := by
        have hce' := hCE who (σ who)
        rw [G.correlatedEu_eq_expect_eu μ who] at hce'
        rw [G.correlatedEu_constantDeviationDistribution_eq_expect_update μ who
          (σ who)] at hce'
        simp only [hf_def]
        have : Math.Probability.expect μ f
            = expect μ (fun σ' => G.eu σ' who)
              - expect μ (fun σ' => G.eu (Function.update σ' who (σ who)) who) := by
          simp only [hf_def, Math.Probability.expect]
          rw [← (Math.Probability.expect_summable_of_bounded μ
              (fun σ' => G.eu σ' who) (G.eu_abs_le_of_bounded who hbd)).tsum_sub
            (Math.Probability.expect_summable_of_bounded μ
              (fun σ' => G.eu (Function.update σ' who (σ who)) who)
              (fun τ' => G.eu_abs_le_of_bounded who hbd _))]
          congr 1; ext τ'; ring
        rw [this]
        linarith
      have hle0 : Math.Probability.expect μ f ≤ 0 := by
        have := Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
          μ f (fun _ => 0) hnonpos hbdf (fun _ => by simpa using (by linarith : (0:ℝ) ≤ 2 * C))
        simpa using this
      have hfeq0 : Math.Probability.expect μ f = 0 := le_antisymm hle0 hge0
      intro τ hμτ
      have hfτ : f τ = 0 := Math.ProbabilityMassFunction.eq_zero_of_expect_eq_zero_of_nonpos_of_pos
        μ f hnonpos hfeq0 (Math.Probability.expect_summable_of_bounded μ f hbdf) hμτ
      by_contra hne
      have hgt := hdom who τ (τ who) hne
      have hself : Function.update τ who (τ who) = τ := Function.update_eq_self _ _
      rw [hself] at hgt
      simp only [hf_def] at hfτ
      linarith
    have hsub : ∀ τ, τ ≠ σ → μ τ = 0 := by
      intro τ hτne
      by_contra hτ
      exact hτne (funext fun who => hcoord who τ hτ)
    apply PMF.ext
    intro τ
    by_cases hτσ : τ = σ
    · subst hτσ
      have hsum : (∑' x, μ x) = 1 := μ.tsum_coe
      have hsingle : (∑' x, μ x) = μ τ := by
        apply tsum_eq_single τ
        intro x hx
        exact hsub x hx
      rw [hsingle] at hsum
      rw [hsum, PMF.pure_apply, if_pos rfl]
    · rw [hsub τ hτσ, PMF.pure_apply, if_neg hτσ]
  · intro hμ
    subst hμ
    exact (nash_pure_isCorrelatedEq (G.dominant_is_nash σ (fun i => (hdom i).toDominant)))
      |>.toCoarseCorrelatedEq

/-- **Dominant strategies saturate correlated equilibrium**, as a corollary of the
coarse version: every CE is a CCE, and the CCE singleton fact already pins it
down. -/
theorem strictDominant_isCorrelatedEq_iff [Finite G.Outcome]
    {σ : Profile G} (hdom : ∀ i, G.IsStrictDominant i (σ i)) {μ : PMF (Profile G)} :
    G.IsCorrelatedEq μ ↔ μ = PMF.pure σ := by
  constructor
  · intro h
    exact (G.strictDominant_isCoarseCorrelatedEq_iff hdom).mp h.toCoarseCorrelatedEq
  · intro hμ
    subst hμ
    exact nash_pure_isCorrelatedEq (G.dominant_is_nash σ (fun i => (hdom i).toDominant))

/-- **Saturation for an equilibrium predicate `E`.** Every distribution
satisfying `E` is realizable as a public signal selecting a mixed Nash
equilibrium — `E` gives nothing that public randomization over Nash
equilibria didn't already. -/
def IsSaturatedFor (G : KernelGame ι) [Fintype ι] (E : PMF (Profile G) → Prop) : Prop :=
  ∀ μ, E μ →
    ∃ (Signal : Type) (ν : PMF Signal) (play : Signal → Profile G.mixedExtension),
      G.PublicSignalNash ν play ∧ μ = G.publicCorrelatedLaw ν play

/-- Saturation transports along an implication between equilibrium predicates:
the weaker predicate is easier to saturate for. -/
theorem IsSaturatedFor.mono {G : KernelGame ι} [Fintype ι] {E₁ E₂ : PMF (Profile G) → Prop}
    (hsat : G.IsSaturatedFor E₂) (h : ∀ μ, E₁ μ → E₂ μ) : G.IsSaturatedFor E₁ :=
  fun μ hμ => hsat μ (h μ hμ)

/-- **Correlation saturation.** Every correlated equilibrium of `G` is realizable
as a public signal selecting a mixed Nash equilibrium. -/
def IsCorrelationSaturated (G : KernelGame ι) [Fintype ι] : Prop :=
  G.IsSaturatedFor G.IsCorrelatedEq

/-- **Coarse correlation saturation.** Every coarse correlated equilibrium of `G`
is realizable as a public signal selecting a mixed Nash equilibrium. Strictly
stronger than `IsCorrelationSaturated`, since every CE is a CCE. -/
def IsCoarseCorrelationSaturated (G : KernelGame ι) [Fintype ι] : Prop :=
  G.IsSaturatedFor G.IsCoarseCorrelatedEq

/-- Coarse correlation saturation implies correlation saturation, since every CE
is a CCE. -/
theorem IsCoarseCorrelationSaturated.isCorrelationSaturated
    {G : KernelGame ι} [Fintype ι] (h : G.IsCoarseCorrelationSaturated) :
    G.IsCorrelationSaturated :=
  IsSaturatedFor.mono h (fun _ hμ => hμ.toCoarseCorrelatedEq)

/-- **Dominant strategies saturate coarse correlation.** With a strictly
dominant strategy for every player, the only coarse correlated equilibrium is
the point mass at the dominant-strategy profile, which is trivially a (single,
constant) public signal selecting a mixed Nash equilibrium. -/
theorem strictDominant_isCoarseCorrelationSaturated [Fintype ι] [Finite G.Outcome]
    {σ : Profile G} (hdom : ∀ i, G.IsStrictDominant i (σ i)) :
    G.IsCoarseCorrelationSaturated := by
  intro μ hCE
  have hμ : μ = PMF.pure σ := (G.strictDominant_isCoarseCorrelatedEq_iff hdom).mp hCE
  refine ⟨PUnit, PMF.pure PUnit.unit, fun _ => G.pureMixedProfile σ, ?_, ?_⟩
  · intro _ _
    exact (G.dominant_is_nash σ (fun i => (hdom i).toDominant)).pureMixedProfile_isNash
  · rw [hμ]
    unfold publicCorrelatedLaw
    rw [PMF.pure_bind]
    exact (Math.PMFProduct.pmfPi_pure σ).symm

/-- **Dominant strategies saturate correlation**, as a corollary of the coarse
version. -/
theorem strictDominant_isCorrelationSaturated [Fintype ι] [Finite G.Outcome]
    {σ : Profile G} (hdom : ∀ i, G.IsStrictDominant i (σ i)) :
    G.IsCorrelationSaturated :=
  (G.strictDominant_isCoarseCorrelationSaturated hdom).isCorrelationSaturated

/-- **Dominance-solvable games are correlation saturated**, given the surviving
profile is Nash: the unique correlated equilibrium is the point mass at `σ`
(`IsIESDSSolvable.correlatedEq_eq_pure`), trivially realized by the constant
public signal on `σ`. Strictly more general than
`strictDominant_isCorrelationSaturated`, since iterated elimination only ever
tests domination relative to surviving opponent actions, not against every
profile in one round.

The `IsNash σ` hypothesis is not derived from `hsolv` here: for the iterated
notion this needs mixed Nash existence plus "no mixed Nash puts weight on a
dominated action", which is not yet formalized (see the module docstring). For
`IsDominantStrategySolvable`, by contrast, `dominant_is_nash` gives it for
free — that is why `strictDominant_isCorrelationSaturated` needs no such
hypothesis. -/
theorem IsIESDSSolvable.isCorrelationSaturated
    [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    {σ : Profile G} (hsolv : G.IsIESDSSolvable σ) (hNash : G.IsNash σ) :
    G.IsCorrelationSaturated := by
  intro μ hCE
  have hμ : μ = PMF.pure σ := hsolv.correlatedEq_eq_pure hCE
  refine ⟨PUnit, PMF.pure PUnit.unit, fun _ => G.pureMixedProfile σ, ?_, ?_⟩
  · intro _ _
    exact hNash.pureMixedProfile_isNash
  · rw [hμ]
    unfold publicCorrelatedLaw
    rw [PMF.pure_bind]
    exact (Math.PMFProduct.pmfPi_pure σ).symm

end KernelGame

end GameTheory
