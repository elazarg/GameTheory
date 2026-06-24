/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Welfare.PriceOfAnarchy
import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import GameTheory.Concepts.Correlation.CorrelationRegimes
import GameTheory.Concepts.Equilibrium.NashCorrelatedEq

/-!
# Value of correlation

The *value of correlation* (Ashlagi–Monderer–Tennenholtz, *On the Value of
Correlation*, JAIR 2008) measures how much social welfare a correlation device
can add over the best Nash equilibrium. Because every Nash equilibrium, viewed
as a point-mass recommendation, is a correlated equilibrium of equal welfare,
the value of correlation is always nonnegative: correlation never hurts.

## Main definitions

* `KernelGame.correlatedSocialWelfare` — social welfare of a correlated play `μ`
* `KernelGame.bestCorrelatedWelfare` — best welfare over all correlated equilibria
* `KernelGame.valueOfCorrelation` — `bestCorrelatedWelfare - bestNashWelfare`

## Main results

* `correlatedSocialWelfare_pure` — for a pure profile it reduces to `socialWelfare`
* `bestNashWelfare_le_bestCorrelatedWelfare` — correlation never lowers welfare
* `valueOfCorrelation_nonneg` — the value of correlation is nonnegative
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [Fintype ι] (G : KernelGame ι)

/-- Social welfare of a correlated play `μ`: the sum over players of their
correlated expected utility. Reduces to `socialWelfare` for a pure profile. -/
noncomputable def correlatedSocialWelfare (μ : PMF (Profile G)) : ℝ :=
  ∑ i : ι, G.correlatedEu μ i

/-- For a point-mass recommendation, correlated social welfare is ordinary
social welfare. -/
theorem correlatedSocialWelfare_pure (σ : Profile G) :
    G.correlatedSocialWelfare (PMF.pure σ) = G.socialWelfare σ := by
  simp only [correlatedSocialWelfare, socialWelfare, correlatedEu_pure]

section FiniteOutcome

variable [DecidableEq ι] [Finite G.Outcome]

/-- Correlated social welfare is uniformly bounded above across all profile
distributions (each player's correlated EU is bounded since outcomes are
finite). -/
theorem correlatedSocialWelfare_bddAbove :
    BddAbove (Set.range (fun μ : {μ : PMF (Profile G) // G.IsCorrelatedEq μ} =>
      G.correlatedSocialWelfare μ.1)) := by
  refine ⟨∑ i : ι, Classical.choose
      (Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)), ?_⟩
  rintro x ⟨μ, rfl⟩
  simp only [correlatedSocialWelfare]
  exact Finset.sum_le_sum
    (fun i _ => le_trans (le_abs_self _) (G.correlatedEu_abs_le μ.1 i))

/-- The best social welfare achievable by a correlated equilibrium. -/
noncomputable def bestCorrelatedWelfare : ℝ :=
  ⨆ μ : {μ : PMF (Profile G) // G.IsCorrelatedEq μ}, G.correlatedSocialWelfare μ.1

end FiniteOutcome

section ValueOfCorrelation

variable [DecidableEq ι] [Finite G.Outcome] [Fintype (Profile G)]

/-- **Correlation never lowers welfare.** The best Nash welfare is at most the
best correlated-equilibrium welfare: every Nash equilibrium, as a point-mass
recommendation, is a correlated equilibrium of equal welfare. -/
theorem bestNashWelfare_le_bestCorrelatedWelfare
    (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.bestNashWelfare hN ≤ G.bestCorrelatedWelfare := by
  classical
  simp only [bestNashWelfare]
  apply Finset.sup'_le
  intro σ hσmem
  have hσ : G.IsNash σ := (Finset.mem_filter.mp hσmem).2
  have hce : G.IsCorrelatedEq (PMF.pure σ) := nash_pure_isCorrelatedEq hσ
  have hle : G.correlatedSocialWelfare (PMF.pure σ) ≤ G.bestCorrelatedWelfare :=
    le_ciSup (G.correlatedSocialWelfare_bddAbove)
      (⟨PMF.pure σ, hce⟩ : {μ : PMF (Profile G) // G.IsCorrelatedEq μ})
  rwa [G.correlatedSocialWelfare_pure σ] at hle

/-- The **value of correlation** (Ashlagi–Monderer–Tennenholtz): the welfare
gain obtainable from a correlation device over the best Nash equilibrium. -/
noncomputable def valueOfCorrelation (hN : ∃ σ : Profile G, G.IsNash σ) : ℝ :=
  G.bestCorrelatedWelfare - G.bestNashWelfare hN

/-- The value of correlation is nonnegative: correlation never hurts welfare. -/
theorem valueOfCorrelation_nonneg (hN : ∃ σ : Profile G, G.IsNash σ) :
    0 ≤ G.valueOfCorrelation hN := by
  rw [valueOfCorrelation, sub_nonneg]
  exact G.bestNashWelfare_le_bestCorrelatedWelfare hN

end ValueOfCorrelation

end KernelGame

end GameTheory
