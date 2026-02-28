import GameTheory.SolutionConcepts

/-!
# GameTheory.DominanceNash

Connections between dominance concepts and Nash equilibria for kernel-based games.

Provides:
- `not_in_nash_of_not_best_response` — a strategy that is never a best response
  is not played in any Nash equilibrium
- `StrictlyDominates.not_nash` — if some strategy strictly dominates a player's
  current choice, the profile is not Nash
- `IsStrictDominant.unique_best_response` — a strictly dominant strategy is the
  unique best response at every profile
-/

namespace GameTheory
namespace KernelGame

variable {ι : Type} [DecidableEq ι] {G : KernelGame ι}

/-- If strategy `s` is never a best response (against any profile), then no
    Nash equilibrium plays `s`. -/
theorem not_in_nash_of_not_best_response {who : ι} (s : G.Strategy who)
    (hnbr : ∀ σ : Profile G, ¬ G.IsBestResponse who σ s) {σ : Profile G}
    (hN : G.IsNash σ) : σ who ≠ s := by
  intro heq
  apply hnbr σ
  rw [← heq]
  intro s'
  have := hN who s'
  rwa [Function.update_eq_self]

/-- If some strategy `s` strictly dominates what player `who` is currently
    playing, then the profile is not a Nash equilibrium. -/
theorem StrictlyDominates.not_nash {who : ι} {s : G.Strategy who}
    {σ : Profile G} (hsd : G.StrictlyDominates who s (σ who)) :
    ¬ G.IsNash σ := by
  intro hN
  have hge := hN who s
  have hlt := hsd σ
  simp only [Function.update_eq_self] at hlt
  linarith

/-- A strictly dominant strategy is the unique best response at every profile:
    if `s` is strictly dominant and `t` is a best response, then `t = s`. -/
theorem IsStrictDominant.unique_best_response {who : ι}
    {s : G.Strategy who} (hsd : G.IsStrictDominant who s)
    (σ : Profile G) {t : G.Strategy who} (hbr : G.IsBestResponse who σ t) :
    t = s := by
  by_contra hne
  have hlt := hsd σ t hne
  have hge := hbr s
  linarith

end KernelGame
end GameTheory
