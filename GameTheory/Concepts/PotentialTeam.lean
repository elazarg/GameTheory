import Mathlib.Algebra.BigOperators.Ring.Finset
import Math.Probability
import GameTheory.Concepts.TeamGame
import GameTheory.Core.GameProperties
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Concepts.ZeroSum

/-!
# Team games as potential games

Every team game (identical-interest game) is an exact potential game, with the
potential function being any player's expected utility.

## Main results

- `IsTeamGame.isExactPotential` — a team game is an exact potential game with
  potential `Φ(σ) = eu σ i₀` for any fixed player `i₀`
- `IsTeamGame.nash_iff_local_potential_max` — Nash equilibrium in a team game
  is equivalent to no unilateral deviation improving the potential
- `IsZeroSum.teamGame_utility_zero` — a game that is both zero-sum and team
  must have all utilities identically zero
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability
namespace KernelGame

variable {ι : Type}

set_option linter.unusedFintypeInType false in
open Classical in
/-- A team game is an exact potential game, with potential function
    `Φ(σ) = eu σ i₀` for any fixed player `i₀`. -/
theorem IsTeamGame.isExactPotential [Fintype ι]
    {G : KernelGame ι} (hteam : G.IsTeamGame) (i₀ : ι) :
    G.IsExactPotential (fun σ => G.eu σ i₀) := by
  intro who σ s'
  have h1 := hteam.eu_eq (Function.update σ who s') who i₀
  have h2 := hteam.eu_eq σ who i₀
  linarith

set_option linter.unusedFintypeInType false in
open Classical in
/-- In a team game, a profile is Nash if and only if no unilateral deviation
    improves the potential function `Φ(σ) = eu σ i₀`. -/
theorem IsTeamGame.nash_iff_local_potential_max [Fintype ι]
    {G : KernelGame ι} (hteam : G.IsTeamGame) (i₀ : ι) (σ : Profile G) :
    G.IsNash σ ↔ ∀ (who : ι) (s' : G.Strategy who),
      G.eu σ i₀ ≥ G.eu (Function.update σ who s') i₀ := by
  constructor
  · intro hN who s'
    have := hN who s'
    have h1 := hteam.eu_eq σ who i₀
    have h2 := hteam.eu_eq (Function.update σ who s') who i₀
    linarith
  · intro h who s'
    have := h who s'
    have h1 := hteam.eu_eq σ i₀ who
    have h2 := hteam.eu_eq (Function.update σ who s') i₀ who
    linarith

set_option linter.unusedFintypeInType false in
/-- A game that is both zero-sum and a team game must have all utilities
    identically zero. -/
theorem IsZeroSum.teamGame_utility_zero [Fintype ι] [Nonempty ι]
    {G : KernelGame ι} (hzs : G.IsZeroSum) (hteam : G.IsTeamGame)
    (ω : G.Outcome) (i : ι) : G.utility ω i = 0 := by
  have hzero : (∑ j : ι, G.utility ω j) = 0 := hzs ω
  have hconst : ∀ j, G.utility ω j = G.utility ω i := fun j => hteam ω j i
  simp_rw [hconst] at hzero
  rw [Finset.sum_const, nsmul_eq_mul] at hzero
  have hpos : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  exact (mul_eq_zero.mp hzero).resolve_left hpos

end KernelGame
end GameTheory
