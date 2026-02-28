import GameTheory.SolutionConcepts

/-!
# GameTheory.StrictDominance

Theorems connecting strict dominance with Nash equilibria.

Provides:
- `IsStrictDominant.toDominant` -- strict dominance implies (weak) dominance
- `strictly_dominant_is_nash` -- a profile of strictly dominant strategies is Nash
- `strictly_dominant_unique_nash` -- such a profile is the unique Nash equilibrium
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type}
variable {G : KernelGame ι}

/-- A strictly dominant strategy is also (weakly) dominant. -/
theorem IsStrictDominant.toDominant {who : ι} {s : G.Strategy who}
    (h : G.IsStrictDominant who s) : G.IsDominant who s := by
  intro σ s'
  by_cases hne : s' = s
  · subst hne; exact le_refl _
  · exact le_of_lt (h σ s' hne)

/-- If every player has a strictly dominant strategy, the profile of those
    strategies is a Nash equilibrium. -/
theorem strictly_dominant_is_nash (σ : Profile G)
    (hdom : ∀ i, G.IsStrictDominant i (σ i)) : G.IsNash σ :=
  dominant_is_nash G σ (fun i => (hdom i).toDominant)

/-- If every player has a strictly dominant strategy, there is a unique Nash
    equilibrium: any Nash profile must equal the dominant-strategy profile. -/
theorem strictly_dominant_unique_nash (σ : Profile G)
    (hdom : ∀ i, G.IsStrictDominant i (σ i))
    (τ : Profile G) (hτ : G.IsNash τ) : τ = σ := by
  classical
  funext i
  by_contra hne
  have hstrict := hdom i τ (τ i) hne
  have hge := hτ i (σ i)
  simp only [Function.update_eq_self] at hstrict
  linarith

end KernelGame

end GameTheory
