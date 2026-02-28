import GameTheory.SolutionConcepts

/-!
# GameTheory.StrictNashProperties

Properties of strict Nash equilibria for kernel-based games.

Provides:
- `strictNash_of_strictDominant` — a profile of strictly dominant strategies is strict Nash
- `IsStrictNash.isBestResponse_unique` — under strict Nash, best responses are unique
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type} [DecidableEq ι] {G : KernelGame ι}

/-- If every player has a strictly dominant strategy and plays it, the resulting
    profile is a strict Nash equilibrium. -/
theorem strictNash_of_strictDominant (σ : Profile G)
    (hdom : ∀ i, G.IsStrictDominant i (σ i)) : G.IsStrictNash σ := by
  intro who s' hne
  have h := hdom who σ s' hne
  simp only [Function.update_eq_self] at h
  exact h

/-- In a strict Nash equilibrium, the equilibrium strategy is the unique best response:
    any best response must equal the equilibrium strategy. -/
theorem IsStrictNash.isBestResponse_unique {σ : Profile G}
    (hstrict : G.IsStrictNash σ) {who : ι} {s' : G.Strategy who}
    (hbr : G.IsBestResponse who σ s') : s' = σ who := by
  by_contra hne
  have hbr_ge := hbr (σ who)
  simp only [Function.update_eq_self] at hbr_ge
  have hstrict_gt := hstrict who s' hne
  linarith

end KernelGame

end GameTheory
