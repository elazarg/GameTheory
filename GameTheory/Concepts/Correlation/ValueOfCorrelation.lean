/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Welfare.PriceOfAnarchy
import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import GameTheory.Concepts.Correlation.CorrelationRegimes
import GameTheory.Concepts.Correlation.CorrelatedEqProperties
import GameTheory.Concepts.Equilibrium.NashCorrelatedEq

/-!
# Welfare gain from correlation

The additive **correlation welfare gap**: how much social welfare the best
correlated equilibrium adds over the best Nash equilibrium. (Ashlagi–Monderer–
Tennenholtz, *On the Value of Correlation*, JAIR 2008, define the *value of
correlation* multiplicatively — the ratio of these welfares, for nonnegative-payoff
games; the additive gap formalized here is the analogous quantity that needs no
positivity assumption.) The Nash benchmark is `bestNashWelfare`, the best welfare
among **pure** Nash equilibria (matching the library's price-of-anarchy
convention), so the comparison requires a pure Nash to exist. Because every pure
Nash equilibrium, viewed as a point-mass recommendation, is a correlated
equilibrium of equal welfare, the gap is always nonnegative: correlation never
hurts. The same comparison against *coarse* correlated equilibria gives an even
larger gap, yielding the welfare ladder best pure Nash ≤ best correlated ≤ best
coarse correlated.

## Main definitions

* `KernelGame.correlatedSocialWelfare` — social welfare of a correlated play `μ`
* `KernelGame.bestCorrelatedWelfare` — best welfare over correlated equilibria
  (a `⨆`, defaulting to `0` when none exists; a supplied pure Nash rules this out)
* `KernelGame.bestCoarseCorrelatedWelfare` — best welfare over coarse correlated equilibria
* `KernelGame.correlationWelfareGap` — `bestCorrelatedWelfare - bestNashWelfare`
* `KernelGame.coarseCorrelationWelfareGap` — `bestCoarseCorrelatedWelfare - bestNashWelfare`

## Main results

* `correlatedSocialWelfare_pure` — for a pure profile it reduces to `socialWelfare`
* `bestNashWelfare_le_bestCorrelatedWelfare` — correlation never lowers welfare
* `bestCorrelatedWelfare_le_bestCoarseCorrelatedWelfare` — coarsening never lowers it further
* `correlationWelfareGap_nonneg`, `coarseCorrelationWelfareGap_nonneg` — both gaps are nonnegative
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

variable [Finite G.Outcome]

/-- Correlated social welfare is bounded above, uniformly over *all* profile
distributions, by the sum of the per-player utility bounds (each player's
correlated EU is bounded since outcomes are finite). -/
theorem correlatedSocialWelfare_le (μ : PMF (Profile G)) :
    G.correlatedSocialWelfare μ ≤ ∑ i : ι, Classical.choose
      (Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)) := by
  simp only [correlatedSocialWelfare]
  exact Finset.sum_le_sum
    (fun i _ => le_trans (le_abs_self _) (G.correlatedEu_abs_le μ i))

variable [DecidableEq ι]

/-- The welfare of correlated equilibria is bounded above. -/
theorem correlatedSocialWelfare_bddAbove :
    BddAbove (Set.range (fun μ : {μ : PMF (Profile G) // G.IsCorrelatedEq μ} =>
      G.correlatedSocialWelfare μ.1)) :=
  ⟨_, by rintro x ⟨μ, rfl⟩; exact G.correlatedSocialWelfare_le μ.1⟩

/-- The welfare of coarse correlated equilibria is bounded above. -/
theorem coarseCorrelatedSocialWelfare_bddAbove :
    BddAbove (Set.range (fun μ : {μ : PMF (Profile G) // G.IsCoarseCorrelatedEq μ} =>
      G.correlatedSocialWelfare μ.1)) :=
  ⟨_, by rintro x ⟨μ, rfl⟩; exact G.correlatedSocialWelfare_le μ.1⟩

/-- The best social welfare achievable by a correlated equilibrium, as a supremum
over the correlated-equilibrium subtype. If no correlated equilibrium exists the
supremum is the `sSup ∅ = 0` default; the welfare-gap results below supply a
pure-Nash witness, so the subtype is nonempty there. -/
noncomputable def bestCorrelatedWelfare : ℝ :=
  ⨆ μ : {μ : PMF (Profile G) // G.IsCorrelatedEq μ}, G.correlatedSocialWelfare μ.1

/-- The best social welfare achievable by a coarse correlated equilibrium, as a
supremum over the coarse-correlated-equilibrium subtype (the `sSup ∅ = 0` default
when none exists; ruled out wherever a pure-Nash witness is supplied). -/
noncomputable def bestCoarseCorrelatedWelfare : ℝ :=
  ⨆ μ : {μ : PMF (Profile G) // G.IsCoarseCorrelatedEq μ}, G.correlatedSocialWelfare μ.1

end FiniteOutcome

section ValueOfCorrelation

variable [DecidableEq ι] [Finite G.Outcome] [Finite (Profile G)]

/-- **Correlation never lowers welfare.** The best Nash welfare is at most the
best correlated-equilibrium welfare: every Nash equilibrium, as a point-mass
recommendation, is a correlated equilibrium of equal welfare. -/
theorem bestNashWelfare_le_bestCorrelatedWelfare
    (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.bestNashWelfare hN ≤ G.bestCorrelatedWelfare := by
  classical
  letI : Nonempty {σ : Profile G // G.IsNash σ} :=
    ⟨⟨hN.choose, hN.choose_spec⟩⟩
  rw [G.bestNashWelfare_eq_iSup hN]
  apply ciSup_le
  intro σ
  have hce : G.IsCorrelatedEq (PMF.pure σ) := nash_pure_isCorrelatedEq σ.property
  have hle : G.correlatedSocialWelfare (PMF.pure σ) ≤ G.bestCorrelatedWelfare :=
    le_ciSup (G.correlatedSocialWelfare_bddAbove)
      (⟨PMF.pure σ, hce⟩ : {μ : PMF (Profile G) // G.IsCorrelatedEq μ})
  rwa [G.correlatedSocialWelfare_pure σ] at hle

omit [Finite (Profile G)] in
/-- **Coarsening never lowers the best welfare.** Every correlated equilibrium
is a coarse correlated equilibrium, so the best coarse-correlated welfare is at
least the best correlated welfare. -/
theorem bestCorrelatedWelfare_le_bestCoarseCorrelatedWelfare
    (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.bestCorrelatedWelfare ≤ G.bestCoarseCorrelatedWelfare := by
  obtain ⟨σ, hσ⟩ := hN
  haveI : Nonempty {μ : PMF (Profile G) // G.IsCorrelatedEq μ} :=
    ⟨⟨PMF.pure σ, nash_pure_isCorrelatedEq hσ⟩⟩
  apply ciSup_le
  intro μ
  exact le_ciSup_of_le (G.coarseCorrelatedSocialWelfare_bddAbove)
    (⟨μ.1, μ.2.toCoarseCorrelatedEq⟩ : {μ : PMF (Profile G) // G.IsCoarseCorrelatedEq μ})
    le_rfl

/-- The best Nash welfare is at most the best coarse-correlated welfare. -/
theorem bestNashWelfare_le_bestCoarseCorrelatedWelfare
    (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.bestNashWelfare hN ≤ G.bestCoarseCorrelatedWelfare :=
  le_trans (G.bestNashWelfare_le_bestCorrelatedWelfare hN)
    (G.bestCorrelatedWelfare_le_bestCoarseCorrelatedWelfare hN)

/-- The **correlation welfare gap**: the welfare gain obtainable from a
correlation device over the best pure Nash equilibrium (the additive analogue of
the Ashlagi–Monderer–Tennenholtz value of correlation). -/
noncomputable def correlationWelfareGap (hN : ∃ σ : Profile G, G.IsNash σ) : ℝ :=
  G.bestCorrelatedWelfare - G.bestNashWelfare hN

/-- The **coarse correlation welfare gap**: the welfare gain obtainable from a
coarse correlation device (e.g. a public signal / no-external-regret play) over
the best pure Nash equilibrium. -/
noncomputable def coarseCorrelationWelfareGap (hN : ∃ σ : Profile G, G.IsNash σ) : ℝ :=
  G.bestCoarseCorrelatedWelfare - G.bestNashWelfare hN

/-- The correlation welfare gap is nonnegative: correlation never hurts welfare. -/
theorem correlationWelfareGap_nonneg (hN : ∃ σ : Profile G, G.IsNash σ) :
    0 ≤ G.correlationWelfareGap hN := by
  rw [correlationWelfareGap, sub_nonneg]
  exact G.bestNashWelfare_le_bestCorrelatedWelfare hN

/-- The coarse correlation welfare gap is nonnegative. -/
theorem coarseCorrelationWelfareGap_nonneg (hN : ∃ σ : Profile G, G.IsNash σ) :
    0 ≤ G.coarseCorrelationWelfareGap hN := by
  rw [coarseCorrelationWelfareGap, sub_nonneg]
  exact G.bestNashWelfare_le_bestCoarseCorrelatedWelfare hN

/-- The correlation welfare gap never exceeds the coarse correlation welfare gap
(the coarse-correlated equilibria form a superset). -/
theorem correlationWelfareGap_le_coarse
    (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.correlationWelfareGap hN ≤ G.coarseCorrelationWelfareGap hN := by
  rw [correlationWelfareGap, coarseCorrelationWelfareGap, sub_le_sub_iff_right]
  exact G.bestCorrelatedWelfare_le_bestCoarseCorrelatedWelfare hN

end ValueOfCorrelation

/-! ### An upper bound: correlation cannot beat the social optimum -/

section OptimalBound

variable [Finite G.Outcome] [Finite (Profile G)]

omit [Finite (Profile G)] in
/-- Social welfare is bounded above across all profiles (each player's expected
utility is bounded since outcomes are finite). -/
theorem socialWelfare_bddAbove :
    BddAbove (Set.range (fun σ : Profile G => G.socialWelfare σ)) := by
  refine ⟨∑ i, Classical.choose
      (Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)), ?_⟩
  rintro x ⟨σ, rfl⟩
  simp only [socialWelfare]
  refine Finset.sum_le_sum (fun i _ => le_trans (le_abs_self _) ?_)
  exact G.eu_abs_le_of_bounded i
    (Classical.choose_spec (Math.Probability.exists_abs_bound_of_finite
      (fun ω => G.utility ω i))) σ

/-- Correlated social welfare is the expected social welfare of the recommended
profile. -/
theorem correlatedSocialWelfare_eq_expect (μ : PMF (Profile G)) :
    G.correlatedSocialWelfare μ = expect μ (fun σ => G.socialWelfare σ) := by
  simp only [correlatedSocialWelfare, socialWelfare]
  rw [← expect_sum_comm μ (fun i σ => G.eu σ i)]
  exact Finset.sum_congr rfl (fun i _ => correlatedEu_eq_expect_eu μ i)

/-- No correlated play beats the social optimum: its expected welfare is at most
the best welfare achievable by any single profile. -/
theorem correlatedSocialWelfare_le_optimalWelfare (μ : PMF (Profile G)) :
    G.correlatedSocialWelfare μ ≤ G.optimalWelfare := by
  rw [correlatedSocialWelfare_eq_expect]
  calc expect μ (fun σ => G.socialWelfare σ)
      ≤ expect μ (fun _ => G.optimalWelfare) :=
        expect_mono μ _ _ (fun σ => welfare_le_optimal G σ G.socialWelfare_bddAbove)
    _ = G.optimalWelfare := expect_const μ _

variable [DecidableEq ι]

/-- The best correlated-equilibrium welfare is at most the social optimum. -/
theorem bestCorrelatedWelfare_le_optimalWelfare (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.bestCorrelatedWelfare ≤ G.optimalWelfare := by
  obtain ⟨σ, hσ⟩ := hN
  haveI : Nonempty {μ : PMF (Profile G) // G.IsCorrelatedEq μ} :=
    ⟨⟨PMF.pure σ, nash_pure_isCorrelatedEq hσ⟩⟩
  exact ciSup_le (fun μ => G.correlatedSocialWelfare_le_optimalWelfare μ.1)

/-- The best coarse-correlated-equilibrium welfare is at most the social optimum. -/
theorem bestCoarseCorrelatedWelfare_le_optimalWelfare
    (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.bestCoarseCorrelatedWelfare ≤ G.optimalWelfare := by
  obtain ⟨σ, hσ⟩ := hN
  haveI : Nonempty {μ : PMF (Profile G) // G.IsCoarseCorrelatedEq μ} :=
    ⟨⟨PMF.pure σ, (nash_pure_isCorrelatedEq hσ).toCoarseCorrelatedEq⟩⟩
  exact ciSup_le (fun μ => G.correlatedSocialWelfare_le_optimalWelfare μ.1)

end OptimalBound

section TeamGameValue

variable [DecidableEq ι] [Finite G.Outcome] [Finite (Profile G)]

/-- **Correlation has no value in team games.** When all players share the same
utility the welfare-optimal profile is itself a Nash equilibrium, and no
correlated equilibrium can beat it, so the correlation welfare gap is zero. -/
theorem IsTeamGame.correlationWelfareGap_eq_zero (hteam : G.IsTeamGame)
    (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.correlationWelfareGap hN = 0 := by
  have hcorr_eq : G.bestCorrelatedWelfare = G.bestNashWelfare hN :=
    le_antisymm
      (by rw [hteam.bestNashWelfare_eq_optimalWelfare hN]
          exact G.bestCorrelatedWelfare_le_optimalWelfare hN)
      (G.bestNashWelfare_le_bestCorrelatedWelfare hN)
  rw [correlationWelfareGap, hcorr_eq, sub_self]

/-- **Coarse correlation has no value in team games either.** Same argument as
`correlationWelfareGap_eq_zero`: the welfare-optimal profile is Nash, and no
coarse correlated equilibrium beats the social optimum. -/
theorem IsTeamGame.coarseCorrelationWelfareGap_eq_zero (hteam : G.IsTeamGame)
    (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.coarseCorrelationWelfareGap hN = 0 := by
  have hcce_eq : G.bestCoarseCorrelatedWelfare = G.bestNashWelfare hN :=
    le_antisymm
      (by rw [hteam.bestNashWelfare_eq_optimalWelfare hN]
          exact G.bestCoarseCorrelatedWelfare_le_optimalWelfare hN)
      (G.bestNashWelfare_le_bestCoarseCorrelatedWelfare hN)
  rw [coarseCorrelationWelfareGap, hcce_eq, sub_self]

end TeamGameValue

end KernelGame

end GameTheory
