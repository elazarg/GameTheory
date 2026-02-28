import GameTheory.TeamGame
import GameTheory.GameProperties

/-!
# GameTheory.TeamGameNash

Nash equilibrium properties specific to team games (identical-interest games).

In a team game all players share the same utility function, so expected utilities
coincide.  This simplifies Pareto dominance and strengthens the guarantees of
Nash equilibria.

## Main results

- `IsTeamGame.pareto_dominates_iff` — Pareto dominance reduces to a strict EU
  comparison at a single (arbitrary) player: σ Pareto-dominates τ iff the common
  EU under σ strictly exceeds the common EU under τ.
- `IsTeamGame.nash_no_unilateral_pareto_improvement` — no unilateral deviation
  from a Nash equilibrium can Pareto-dominate the equilibrium profile.
- `IsTeamGame.nash_common_eu_ge` — the Nash equilibrium EU (at any player) is at
  least as large as the EU after any unilateral deviation (at any player).
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type}

set_option linter.unusedFintypeInType false in
/-- In a team game, Pareto dominance is equivalent to a strict EU improvement
    at any single player (all players share the same EU, so one strict
    improvement implies all are weakly better and at least one is strict). -/
theorem IsTeamGame.pareto_dominates_iff [Fintype ι] [Inhabited ι]
    {G : KernelGame ι} (hteam : G.IsTeamGame) (σ τ : Profile G) :
    G.ParetoDominates σ τ ↔ G.eu σ default > G.eu τ default := by
  constructor
  · intro ⟨hge, ⟨i, hi⟩⟩
    have h1 : G.eu σ i = G.eu σ default := hteam.eu_eq σ i default
    have h2 : G.eu τ i = G.eu τ default := hteam.eu_eq τ i default
    linarith
  · intro h
    exact ⟨fun i => by linarith [hteam.eu_eq σ default i, hteam.eu_eq τ default i],
           ⟨default, h⟩⟩

set_option linter.unusedFintypeInType false in
open Classical in
/-- In a team game, no unilateral deviation from a Nash equilibrium can
    Pareto-dominate the equilibrium profile. -/
theorem IsTeamGame.nash_no_unilateral_pareto_improvement [Fintype ι]
    {G : KernelGame ι} (hteam : G.IsTeamGame)
    {σ : Profile G} (hnash : G.IsNash σ) (who : ι) (s' : G.Strategy who) :
    ¬ G.ParetoDominates (Function.update σ who s') σ := by
  intro ⟨_, ⟨i, hi⟩⟩
  have h := hteam.nash_deviation_nonimproving hnash who s' i
  linarith

set_option linter.unusedFintypeInType false in
open Classical in
/-- In a team game Nash equilibrium, the EU at any player `i` is at least
    as large as the EU after any unilateral deviation, measured at any
    player `j`.  This combines the Nash condition with the team-game
    EU-equality property. -/
theorem IsTeamGame.nash_common_eu_ge [Fintype ι]
    {G : KernelGame ι} (hteam : G.IsTeamGame)
    {σ : Profile G} (hnash : G.IsNash σ) (who : ι) (s' : G.Strategy who)
    (i j : ι) :
    G.eu σ i ≥ G.eu (Function.update σ who s') j := by
  have h1 := hteam.nash_deviation_nonimproving hnash who s' j
  have h2 := hteam.eu_eq σ i j
  linarith

end KernelGame

end GameTheory
