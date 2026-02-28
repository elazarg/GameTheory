import GameTheory.SolutionConcepts

/-!
# GameTheory.BestResponse

Theorems linking best responses to Nash equilibria for kernel-based games.

Provides:
- `isNash_iff_bestResponse` — a profile is Nash iff every player plays a best response
- `isNashFor_iff_bestResponseFor` — preference-parameterized version
- `dominant_isBestResponse` — a dominant strategy is a best response against any profile
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- A profile is Nash iff every player plays a best response to the others' strategies. -/
theorem isNash_iff_bestResponse (G : KernelGame ι) (σ : Profile G) :
    G.IsNash σ ↔ ∀ who, G.IsBestResponse who σ (σ who) := by
  constructor
  · intro hNash who s'
    have := hNash who s'
    rwa [Function.update_eq_self]
  · intro hBR who s'
    have := hBR who s'
    rwa [Function.update_eq_self] at this

/-- Preference-parameterized version: a profile is Nash for `pref` iff every player
    plays a best response for `pref`. -/
theorem isNashFor_iff_bestResponseFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop) (σ : Profile G) :
    G.IsNashFor pref σ ↔ ∀ who, G.IsBestResponseFor pref who σ (σ who) := by
  constructor
  · intro hNash who s'
    have := hNash who s'
    rwa [Function.update_eq_self]
  · intro hBR who s'
    have := hBR who s'
    rwa [Function.update_eq_self] at this

/-- A dominant strategy is a best response against any profile. -/
theorem dominant_isBestResponse (G : KernelGame ι) (who : ι)
    (s : G.Strategy who) (σ : Profile G)
    (hdom : G.IsDominant who s) : G.IsBestResponse who σ s := by
  intro s'
  exact hdom σ s'

end KernelGame

end GameTheory
