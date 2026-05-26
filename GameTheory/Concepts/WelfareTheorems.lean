/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.SolutionConcepts
import GameTheory.Concepts.NashPareto
import GameTheory.Core.GameProperties
import Math.Probability

/-!
# GameTheory.Concepts.WelfareTheorems

Welfare theorems relating social welfare to individual expected utilities.

## Main results

- `IsTeamGame.socialWelfare_eq` — in a team game with `n` players,
  social welfare equals `n * eu σ i` for any player `i`
- `socialWelfare_nonneg_of_nonneg_eu` — if all players have non-negative EU,
  social welfare is non-negative
- `IsTeamGame.welfareMax_isNash` — in a team game, any welfare-maximizing
  profile is a Nash equilibrium
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- In a team game, social welfare equals `card ι * eu σ i` for any player `i`,
    since all players share the same expected utility. -/
theorem IsTeamGame.socialWelfare_eq [Fintype ι] [Inhabited ι]
    {G : KernelGame ι} (hteam : G.IsTeamGame) (σ : Profile G) (i : ι) :
    G.socialWelfare σ = Fintype.card ι * G.eu σ i := by
  simp only [KernelGame.socialWelfare]
  have heu : ∀ j : ι, G.eu σ j = G.eu σ i := by
    intro j
    rw [KernelGame.eu, KernelGame.eu]
    congr with ω
    exact hteam ω j i
  calc
    ∑ j : ι, G.eu σ j = ∑ _j : ι, G.eu σ i := by
      apply Finset.sum_congr rfl
      intro j _
      exact heu j
    _ = Fintype.card ι * G.eu σ i := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- If all players have non-negative expected utility, social welfare is non-negative. -/
theorem socialWelfare_nonneg_of_nonneg_eu [Fintype ι]
    {G : KernelGame ι} {σ : Profile G}
    (h : ∀ i, G.eu σ i ≥ 0) : G.socialWelfare σ ≥ 0 :=
  Finset.sum_nonneg (fun i _ => h i)

/-- In a team game with finite players, any social-welfare-maximizing profile
is a Nash equilibrium. Since every player shares the social welfare equally
(via `IsTeamGame.socialWelfare_eq`), no unilateral deviation can improve a
single player's payoff without raising total welfare. -/
theorem IsTeamGame.welfareMax_isNash [Fintype ι] [Inhabited ι] [DecidableEq ι]
    {G : KernelGame ι} (hteam : G.IsTeamGame) {σ : Profile G}
    (hmax : ∀ τ : Profile G, G.socialWelfare τ ≤ G.socialWelfare σ) :
    G.IsNash σ := by
  intro who s'
  have hσ := hteam.socialWelfare_eq σ who
  have hσ' := hteam.socialWelfare_eq (Function.update σ who s') who
  have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hle := hmax (Function.update σ who s')
  rw [hσ, hσ'] at hle
  exact le_of_mul_le_mul_left hle hcard_pos

/-- **Welfare maximizers are Pareto-efficient**: if `σ` maximizes social
welfare over all profiles, then `σ` is Pareto-efficient. A Pareto-dominating
profile would strictly raise total welfare, contradicting maximality. -/
theorem welfareMax_isParetoEfficient [Fintype ι]
    {G : KernelGame ι} {σ : Profile G}
    (hmax : ∀ τ : Profile G, G.socialWelfare τ ≤ G.socialWelfare σ) :
    G.IsParetoEfficient σ := by
  rintro ⟨τ, hpd⟩
  have hlt : G.socialWelfare σ < G.socialWelfare τ :=
    KernelGame.ParetoDominates.socialWelfare_lt hpd
  have hle := hmax τ
  linarith

/-- **Existence of welfare maximizers**: any finite game admits a profile
that maximizes social welfare. Follows from `Finset.exists_max_image` on
the finite profile space. -/
theorem exists_welfareMax [Fintype ι]
    (G : KernelGame ι) [Finite (Profile G)] [Nonempty (Profile G)] :
    ∃ σ : Profile G, ∀ τ : Profile G, G.socialWelfare τ ≤ G.socialWelfare σ := by
  haveI := Fintype.ofFinite (Profile G)
  obtain ⟨σ, _, hσ⟩ :=
    Finset.exists_max_image Finset.univ G.socialWelfare
      (Finset.univ_nonempty (α := Profile G))
  exact ⟨σ, fun τ => hσ τ (Finset.mem_univ τ)⟩

/-- **Existence of a Pareto-efficient profile** in finite games. Follows
from `exists_welfareMax` + `welfareMax_isParetoEfficient`. -/
theorem exists_paretoEfficient [Finite ι]
    (G : KernelGame ι) [Finite (Profile G)] [Nonempty (Profile G)] :
    ∃ σ : Profile G, G.IsParetoEfficient σ := by
  haveI := Fintype.ofFinite ι
  obtain ⟨σ, hmax⟩ := exists_welfareMax G
  exact ⟨σ, welfareMax_isParetoEfficient hmax⟩

end KernelGame

end GameTheory
