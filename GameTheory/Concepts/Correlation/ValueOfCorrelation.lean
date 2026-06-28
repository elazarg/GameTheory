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
# Value of correlation

The *value of correlation* (Ashlagi–Monderer–Tennenholtz, *On the Value of
Correlation*, JAIR 2008) measures how much social welfare a correlation device
can add over the best Nash equilibrium. The benchmark is `bestNashWelfare`, the
best welfare among **pure** Nash equilibria (matching the library's
price-of-anarchy convention), so the comparison requires a pure Nash to exist.
The classical notion compares against the best mixed Nash; since the best
mixed-Nash welfare is at least the best pure-Nash welfare, the pure-Nash *value*
upper-bounds the classical mixed-Nash value. Because every pure Nash
equilibrium, viewed as a
point-mass recommendation, is a correlated equilibrium of equal welfare, the
value of correlation is always nonnegative: correlation never hurts. The same
comparison against *coarse* correlated equilibria gives an even larger value,
yielding the welfare ladder best pure Nash ≤ best correlated ≤ best coarse
correlated.

## Main definitions

* `KernelGame.correlatedSocialWelfare` — social welfare of a correlated play `μ`
* `KernelGame.bestCorrelatedWelfare` — best welfare over all correlated equilibria
* `KernelGame.bestCoarseCorrelatedWelfare` — best welfare over all coarse correlated equilibria
* `KernelGame.valueOfCorrelation` — `bestCorrelatedWelfare - bestNashWelfare`
* `KernelGame.valueOfCoarseCorrelation` — `bestCoarseCorrelatedWelfare - bestNashWelfare`

## Main results

* `correlatedSocialWelfare_pure` — for a pure profile it reduces to `socialWelfare`
* `bestNashWelfare_le_bestCorrelatedWelfare` — correlation never lowers welfare
* `bestCorrelatedWelfare_le_bestCoarseCorrelatedWelfare` — coarsening never lowers it further
* `valueOfCorrelation_nonneg`, `valueOfCoarseCorrelation_nonneg` — both values are nonnegative
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

/-- The best social welfare achievable by a correlated equilibrium. -/
noncomputable def bestCorrelatedWelfare : ℝ :=
  ⨆ μ : {μ : PMF (Profile G) // G.IsCorrelatedEq μ}, G.correlatedSocialWelfare μ.1

/-- The best social welfare achievable by a coarse correlated equilibrium. -/
noncomputable def bestCoarseCorrelatedWelfare : ℝ :=
  ⨆ μ : {μ : PMF (Profile G) // G.IsCoarseCorrelatedEq μ}, G.correlatedSocialWelfare μ.1

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

omit [Fintype (Profile G)] in
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

/-- The **value of correlation** (Ashlagi–Monderer–Tennenholtz): the welfare
gain obtainable from a correlation device over the best pure Nash equilibrium. -/
noncomputable def valueOfCorrelation (hN : ∃ σ : Profile G, G.IsNash σ) : ℝ :=
  G.bestCorrelatedWelfare - G.bestNashWelfare hN

/-- The **value of coarse correlation**: the welfare gain obtainable from a
coarse correlation device (e.g. a public signal / no-external-regret play) over
the best Nash equilibrium. -/
noncomputable def valueOfCoarseCorrelation (hN : ∃ σ : Profile G, G.IsNash σ) : ℝ :=
  G.bestCoarseCorrelatedWelfare - G.bestNashWelfare hN

/-- The value of correlation is nonnegative: correlation never hurts welfare. -/
theorem valueOfCorrelation_nonneg (hN : ∃ σ : Profile G, G.IsNash σ) :
    0 ≤ G.valueOfCorrelation hN := by
  rw [valueOfCorrelation, sub_nonneg]
  exact G.bestNashWelfare_le_bestCorrelatedWelfare hN

/-- The value of coarse correlation is nonnegative, and at least the value of
correlation. -/
theorem valueOfCoarseCorrelation_nonneg (hN : ∃ σ : Profile G, G.IsNash σ) :
    0 ≤ G.valueOfCoarseCorrelation hN := by
  rw [valueOfCoarseCorrelation, sub_nonneg]
  exact G.bestNashWelfare_le_bestCoarseCorrelatedWelfare hN

/-- The value of correlation never exceeds the value of coarse correlation
(the coarse-correlated equilibria form a superset). -/
theorem valueOfCorrelation_le_valueOfCoarseCorrelation
    (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.valueOfCorrelation hN ≤ G.valueOfCoarseCorrelation hN := by
  rw [valueOfCorrelation, valueOfCoarseCorrelation, sub_le_sub_iff_right]
  exact G.bestCorrelatedWelfare_le_bestCoarseCorrelatedWelfare hN

end ValueOfCorrelation

/-! ### An upper bound: correlation cannot beat the social optimum -/

/-- Monotonicity of `expect` over a finite sample space. -/
private theorem expect_mono' {Ω : Type*} [Finite Ω] (μ : PMF Ω) (f g : Ω → ℝ)
    (h : ∀ x, f x ≤ g x) : expect μ f ≤ expect μ g := by
  letI : Fintype Ω := Fintype.ofFinite Ω
  rw [expect_eq_sum, expect_eq_sum]
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) ENNReal.toReal_nonneg)

/-- `expect` commutes with a finite sum of integrands. -/
private theorem expect_finsum' {Ω κ : Type*} [Finite Ω] [Fintype κ]
    (μ : PMF Ω) (f : κ → Ω → ℝ) :
    ∑ i, expect μ (fun x => f i x) = expect μ (fun x => ∑ i, f i x) := by
  letI : Fintype Ω := Fintype.ofFinite Ω
  simp only [expect_eq_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl
    (fun x _ => (Finset.mul_sum Finset.univ (fun i => f i x) ((μ x).toReal)).symm)

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
  rw [← expect_finsum' μ (fun i σ => G.eu σ i)]
  exact Finset.sum_congr rfl (fun i _ => correlatedEu_eq_expect_eu μ i)

/-- No correlated play beats the social optimum: its expected welfare is at most
the best welfare achievable by any single profile. -/
theorem correlatedSocialWelfare_le_optimalWelfare (μ : PMF (Profile G)) :
    G.correlatedSocialWelfare μ ≤ G.optimalWelfare := by
  rw [correlatedSocialWelfare_eq_expect]
  calc expect μ (fun σ => G.socialWelfare σ)
      ≤ expect μ (fun _ => G.optimalWelfare) :=
        expect_mono' μ _ _ (fun σ => welfare_le_optimal G σ G.socialWelfare_bddAbove)
    _ = G.optimalWelfare := expect_const μ _

variable [DecidableEq ι]

/-- The best correlated-equilibrium welfare is at most the social optimum. -/
theorem bestCorrelatedWelfare_le_optimalWelfare (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.bestCorrelatedWelfare ≤ G.optimalWelfare := by
  obtain ⟨σ, hσ⟩ := hN
  haveI : Nonempty {μ : PMF (Profile G) // G.IsCorrelatedEq μ} :=
    ⟨⟨PMF.pure σ, nash_pure_isCorrelatedEq hσ⟩⟩
  exact ciSup_le (fun μ => G.correlatedSocialWelfare_le_optimalWelfare μ.1)

end OptimalBound

section TeamGameValue

variable [DecidableEq ι] [Finite G.Outcome] [Fintype (Profile G)]

/-- **Correlation has no value in team games.** When all players share the same
utility the welfare-optimal profile is itself a Nash equilibrium, and no
correlated equilibrium can beat it, so the value of correlation is zero. -/
theorem IsTeamGame.valueOfCorrelation_eq_zero (hteam : G.IsTeamGame)
    (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.valueOfCorrelation hN = 0 := by
  have hcorr_eq : G.bestCorrelatedWelfare = G.bestNashWelfare hN :=
    le_antisymm
      (by rw [hteam.bestNashWelfare_eq_optimalWelfare hN]
          exact G.bestCorrelatedWelfare_le_optimalWelfare hN)
      (G.bestNashWelfare_le_bestCorrelatedWelfare hN)
  rw [valueOfCorrelation, hcorr_eq, sub_self]

end TeamGameValue

end KernelGame

end GameTheory
