import GameTheory.SolutionConcepts

/-!
# GameTheory.DominanceSolvable

Relationships between dominance and best-response / Nash equilibrium concepts
for kernel-based games.

Provides:
- `StrictlyDominates.not_best_response` — a strictly dominated strategy is never a best response
- `WeaklyDominates.best_response_of_best_response` — weak dominance preserves best-response status
- `nash_never_strictly_dominated` — Nash equilibrium strategies are never strictly dominated
- `IsDominant.isBestResponse` — a dominant strategy is a best response against every profile
-/

namespace GameTheory

variable {ι : Type} [DecidableEq ι]

namespace KernelGame

/-- A strictly dominated strategy is never a best response.
    If `s` strictly dominates `t` for player `who`, then for every opponent
    profile `σ`, `t` cannot be a best response. -/
theorem StrictlyDominates.not_best_response {G : KernelGame ι} {who : ι}
    {s t : G.Strategy who} (hsd : G.StrictlyDominates who s t) :
    ∀ σ : Profile G, ¬ G.IsBestResponse who σ t := by
  intro σ hbr
  have hbr_s := hbr s
  have hsd_σ := hsd σ
  linarith

/-- If `s` weakly dominates `t` and `t` is a best response against `σ`,
    then `s` is also a best response against `σ`. -/
theorem WeaklyDominates.best_response_of_best_response {G : KernelGame ι} {who : ι}
    {s t : G.Strategy who} (hwd : G.WeaklyDominates who s t) (σ : Profile G)
    (hbr : G.IsBestResponse who σ t) : G.IsBestResponse who σ s := by
  intro s'
  have h1 := hbr s'
  have h2 := hwd σ
  linarith

/-- In a Nash equilibrium, no player's strategy is strictly dominated.
    That is, if `σ` is Nash then for every player `who` and strategy `s`,
    `s` does not strictly dominate `σ who`. -/
theorem nash_never_strictly_dominated {G : KernelGame ι} {σ : Profile G}
    (hN : G.IsNash σ) (who : ι) (s : G.Strategy who) :
    ¬ G.StrictlyDominates who s (σ who) := by
  intro hsd
  have hsd_σ := hsd σ
  simp only [Function.update_eq_self] at hsd_σ
  have hN_who := hN who s
  linarith

/-- A dominant strategy is a best response against every profile. -/
theorem IsDominant.isBestResponse {G : KernelGame ι} {who : ι} {s : G.Strategy who}
    (hdom : G.IsDominant who s) (σ : Profile G) : G.IsBestResponse who σ s := by
  intro s'
  exact hdom σ s'

end KernelGame

end GameTheory
