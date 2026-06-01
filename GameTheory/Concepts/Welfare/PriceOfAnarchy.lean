/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import GameTheory.Core.GameProperties
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Welfare.WelfareTheorems

/-!
# Price of Anarchy and Price of Stability

The Price of Anarchy (PoA) measures the worst-case efficiency loss from
selfish behavior: the ratio of optimal social welfare to the worst Nash
equilibrium's social welfare. The Price of Stability (PoS) measures the
ratio to the *best* Nash equilibrium.

## Main definitions

* `KernelGame.optimalWelfare` — maximum social welfare over all profiles
* `KernelGame.worstNashWelfare` — minimum social welfare among Nash equilibria
* `KernelGame.bestNashWelfare` — maximum social welfare among Nash equilibria

## Main results

* `bestNashWelfare_le_optimalWelfare` — best Nash welfare ≤ optimal welfare
* `worstNashWelfare_le_bestNashWelfare` — worst Nash ≤ best Nash
* `teamGame_optimalWelfare_eq_bestNashWelfare` — in team games, the optimal
    profile is Nash so PoS = 1
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [Fintype ι] (G : KernelGame ι)

/-- The optimal social welfare achievable by any profile. -/
noncomputable def optimalWelfare : ℝ :=
  ⨆ σ : Profile G, G.socialWelfare σ

/-- Social welfare of any profile is at most optimal welfare
    (when the supremum is bounded). -/
theorem welfare_le_optimal (σ : Profile G)
    (hbdd : BddAbove (Set.range (fun τ => G.socialWelfare τ))) :
    G.socialWelfare σ ≤ G.optimalWelfare :=
  le_ciSup hbdd σ

variable [DecidableEq ι]

omit [Fintype ι] in
/-- In a team game, every Pareto-efficient profile is Nash. -/
theorem IsTeamGame.pareto_isNash (hteam : G.IsTeamGame)
    {σ : Profile G} (hpareto : G.IsParetoEfficient σ) :
    G.IsNash σ := by
  classical
  by_contra hnn
  simp only [IsNash, not_forall, not_le] at hnn
  obtain ⟨who, s', hdev⟩ := hnn
  apply hpareto
  refine ⟨Function.update σ who s', fun i => ?_, who, hdev⟩
  -- Team-game payoffs are all equal, so any single-player improvement benefits all.
  by_cases hi : i = who
  · subst hi; exact le_of_lt hdev
  · have eu_i_who : ∀ τ : Profile G, G.eu τ i = G.eu τ who := fun τ => by
      simp only [eu]
      congr 1
      ext ω
      exact hteam ω i who
    rw [eu_i_who σ, eu_i_who (Function.update σ who s')]
    exact le_of_lt hdev

section FiniteNash

variable [Fintype (Profile G)]

open Classical in
/-- The best social welfare achievable by any Nash equilibrium. -/
noncomputable def bestNashWelfare (hN : ∃ σ : Profile G, G.IsNash σ) : ℝ :=
  Finset.sup' (Finset.univ.filter (fun σ => G.IsNash σ))
    (by obtain ⟨σ, hσ⟩ := hN
        exact ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩⟩)
    G.socialWelfare

open Classical in
/-- The worst social welfare among all Nash equilibria. -/
noncomputable def worstNashWelfare (hN : ∃ σ : Profile G, G.IsNash σ) : ℝ :=
  Finset.inf' (Finset.univ.filter (fun σ => G.IsNash σ))
    (by obtain ⟨σ, hσ⟩ := hN
        exact ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩⟩)
    G.socialWelfare

open Classical in
/-- Worst Nash welfare ≤ best Nash welfare. -/
theorem worstNashWelfare_le_bestNashWelfare (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.worstNashWelfare hN ≤ G.bestNashWelfare hN := by
  simp only [worstNashWelfare, bestNashWelfare]
  have ⟨σ, hσ⟩ := hN
  have hmem : σ ∈ Finset.univ.filter (fun σ => G.IsNash σ) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩
  exact le_trans (Finset.inf'_le _ hmem) (Finset.le_sup' _ hmem)

open Classical in
/-- The best Nash welfare is at most the optimal welfare (when bounded). -/
theorem bestNashWelfare_le_optimalWelfare (hN : ∃ σ : Profile G, G.IsNash σ)
    (hbdd : BddAbove (Set.range (fun τ => G.socialWelfare τ))) :
    G.bestNashWelfare hN ≤ G.optimalWelfare := by
  apply Finset.sup'_le
  intro σ _
  exact welfare_le_optimal G σ hbdd

open Classical in
/-- **Price of Anarchy** (Koutsoupias–Papadimitriou): the ratio of optimal
welfare to the *worst* Nash welfare. Measures the inefficiency loss from
selfish play in the worst case. -/
noncomputable def priceOfAnarchy (hN : ∃ σ : Profile G, G.IsNash σ) : ℝ :=
  G.optimalWelfare / G.worstNashWelfare hN

open Classical in
/-- **Price of Stability** (Anshelevich et al.): the ratio of optimal welfare
to the *best* Nash welfare. Equals `1` when the social optimum is itself
Nash. -/
noncomputable def priceOfStability (hN : ∃ σ : Profile G, G.IsNash σ) : ℝ :=
  G.optimalWelfare / G.bestNashWelfare hN

open Classical in
/-- The Price of Stability is bounded above by the Price of Anarchy whenever
the worst Nash welfare is positive (so that both ratios are nonnegative). -/
theorem priceOfStability_le_priceOfAnarchy (hN : ∃ σ : Profile G, G.IsNash σ)
    (hopt_nn : 0 ≤ G.optimalWelfare) (hworst : 0 < G.worstNashWelfare hN) :
    G.priceOfStability hN ≤ G.priceOfAnarchy hN := by
  have hbest : 0 < G.bestNashWelfare hN :=
    lt_of_lt_of_le hworst (G.worstNashWelfare_le_bestNashWelfare hN)
  exact div_le_div_of_nonneg_left hopt_nn hworst
    (G.worstNashWelfare_le_bestNashWelfare hN)

open Classical in
/-- The Price of Stability is at least `1` whenever it is well-defined and
the best Nash welfare does not exceed the optimal welfare. -/
theorem one_le_priceOfStability (hN : ∃ σ : Profile G, G.IsNash σ)
    (hbest : 0 < G.bestNashWelfare hN)
    (hbest_le_opt : G.bestNashWelfare hN ≤ G.optimalWelfare) :
    1 ≤ G.priceOfStability hN := by
  rw [priceOfStability, le_div_iff₀ hbest, one_mul]
  exact hbest_le_opt

open Classical in
/-- The Price of Anarchy is at least `1` whenever it is well-defined and
the worst Nash welfare does not exceed the optimal welfare. -/
theorem one_le_priceOfAnarchy (hN : ∃ σ : Profile G, G.IsNash σ)
    (hworst : 0 < G.worstNashWelfare hN)
    (hworst_le_opt : G.worstNashWelfare hN ≤ G.optimalWelfare) :
    1 ≤ G.priceOfAnarchy hN := by
  rw [priceOfAnarchy, le_div_iff₀ hworst, one_mul]
  exact hworst_le_opt

/-- In a team game with finitely many profiles, the best Nash welfare equals
the optimal welfare: the welfare-maximizing profile is itself Nash (by
`IsTeamGame.welfareMax_isNash`). -/
theorem IsTeamGame.bestNashWelfare_eq_optimalWelfare {G : KernelGame ι}
    [Fintype (Profile G)]
    (hteam : G.IsTeamGame) (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.bestNashWelfare hN = G.optimalWelfare := by
  classical
  obtain ⟨σ₀, _⟩ := hN
  haveI : Nonempty (Profile G) := ⟨σ₀⟩
  obtain ⟨σ_max, hmax⟩ := exists_welfareMax G
  have hN_max : G.IsNash σ_max := hteam.welfareMax_isNash hmax
  have h_ge : G.socialWelfare σ_max ≤ G.bestNashWelfare ⟨σ₀, ‹_›⟩ := by
    simp only [bestNashWelfare]
    exact Finset.le_sup' _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN_max⟩)
  have h_opt_le : G.optimalWelfare ≤ G.socialWelfare σ_max := by
    simp only [optimalWelfare]
    exact ciSup_le hmax
  have hbdd : BddAbove (Set.range (fun τ : Profile G => G.socialWelfare τ)) :=
    ⟨G.socialWelfare σ_max, by rintro _ ⟨σ, rfl⟩; exact hmax σ⟩
  linarith [G.bestNashWelfare_le_optimalWelfare ⟨σ₀, ‹_›⟩ hbdd]

/-- In a team game with positive optimal welfare, the Price of Stability is
exactly `1`: selfish play loses no efficiency in the best equilibrium. -/
theorem IsTeamGame.priceOfStability_eq_one {G : KernelGame ι}
    [Fintype (Profile G)]
    (hteam : G.IsTeamGame) (hN : ∃ σ : Profile G, G.IsNash σ)
    (hopt_pos : 0 < G.optimalWelfare) :
    G.priceOfStability hN = 1 := by
  rw [priceOfStability, hteam.bestNashWelfare_eq_optimalWelfare hN,
    div_self hopt_pos.ne']

end FiniteNash

end KernelGame

end GameTheory
