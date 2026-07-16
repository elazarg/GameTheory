/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Equilibrium.NashCorrelatedEq
import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import GameTheory.Concepts.Dominance.StrictDominance

/-!
# GameTheory.Concepts.Correlation.DominantCorrelatedEq

Dominant-strategy profiles saturate the correlated-equilibrium set: once every
player has a strictly dominant strategy, no correlation device — however
elaborate — can move play away from the dominant-strategy profile.

Provides:
- `strictDominant_isCorrelatedEq_iff` — with a strictly dominant strategy for
  every player, a distribution is a correlated equilibrium iff it is the point
  mass at the dominant-strategy profile.
-/

namespace GameTheory

open Math.Probability
open Math.ProbabilityMassFunction

namespace KernelGame

variable {ι : Type} [DecidableEq ι] {G : KernelGame ι}

open Classical in
/-- **Dominant strategies saturate correlated equilibrium.** If every player has a
strictly dominant strategy, the profile of those strategies is the *unique*
correlated equilibrium. Any correlation device, no matter how it signals or
mediates, cannot move a rational player off their dominant strategy, so the
correlated-equilibrium set collapses to the single point mass a Nash analysis
already predicts. -/
theorem strictDominant_isCorrelatedEq_iff [Finite G.Outcome]
    {σ : Profile G} (hdom : ∀ i, G.IsStrictDominant i (σ i)) {μ : PMF (Profile G)} :
    G.IsCorrelatedEq μ ↔ μ = PMF.pure σ := by
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
        have hce' := hCE who (fun _ => σ who)
        rw [G.correlatedEu_eq_expect_eu μ who] at hce'
        rw [G.correlatedEu_unilateralDeviationDistribution_eq_expect_update μ who
          (fun _ => σ who)] at hce'
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
    exact nash_pure_isCorrelatedEq (G.dominant_is_nash σ (fun i => (hdom i).toDominant))

end KernelGame

end GameTheory
