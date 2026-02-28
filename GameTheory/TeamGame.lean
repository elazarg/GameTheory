import GameTheory.GameProperties
import GameTheory.SolutionConcepts

/-!
# GameTheory.TeamGame

Properties of team games (identical-interest games).

In a team game, all players share the same utility function over outcomes.
This implies that expected utilities are equal across all players under any
strategy profile, and that Nash equilibria have strong non-improvability
properties.

## Main results

- `IsTeamGame.eu_eq` — all players have identical EU under any profile
- `IsTeamGame.eu_eq_update` — EU equality is preserved after unilateral deviations
- `IsTeamGame.nash_deviation_nonimproving` — in a Nash equilibrium of a team game,
  no unilateral deviation improves *any* player's EU (not just the deviator's)
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type} [DecidableEq ι] [Fintype ι]

omit [DecidableEq ι] [Fintype ι] in
/-- In a team game, all players have the same expected utility under any profile. -/
theorem IsTeamGame.eu_eq {G : KernelGame ι} (hteam : G.IsTeamGame)
    (σ : Profile G) (i j : ι) : G.eu σ i = G.eu σ j := by
  unfold eu
  congr 1
  ext ω
  exact hteam ω i j

omit [Fintype ι] in
/-- In a team game, after a unilateral deviation, all players still have equal EU. -/
theorem IsTeamGame.eu_eq_update {G : KernelGame ι} (hteam : G.IsTeamGame)
    (σ : Profile G) (who : ι) (s' : G.Strategy who) (i j : ι) :
    G.eu (Function.update σ who s') i = G.eu (Function.update σ who s') j := by
  exact hteam.eu_eq (Function.update σ who s') i j

omit [Fintype ι] in
/-- In a team game, if σ is a Nash equilibrium, then for every player `who`,
    every alternative strategy `s'`, and every player `i`,
    the EU at σ is at least as large as after the deviation.

    This is stronger than the Nash condition itself, which only guarantees
    non-improvement for the deviating player. In a team game, because all
    players share utilities, no unilateral deviation can improve *any* player. -/
theorem IsTeamGame.nash_deviation_nonimproving {G : KernelGame ι} (hteam : G.IsTeamGame)
    {σ : Profile G} (hnash : G.IsNash σ)
    (who : ι) (s' : G.Strategy who) (i : ι) :
    G.eu σ i ≥ G.eu (Function.update σ who s') i := by
  have h_nash_who : G.eu σ who ≥ G.eu (Function.update σ who s') who := hnash who s'
  have h_eq_orig : G.eu σ i = G.eu σ who := hteam.eu_eq σ i who
  have h_eq_dev : G.eu (Function.update σ who s') i =
      G.eu (Function.update σ who s') who := hteam.eu_eq_update σ who s' i who
  linarith

end KernelGame

end GameTheory
