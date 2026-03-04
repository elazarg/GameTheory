import GameTheory.Concepts.SolutionConcepts
import GameTheory.Concepts.Deviation
import Math.Probability

/-!
# GameTheory.Concepts.BestResponse

Theorems linking best responses to Nash equilibria for kernel-based games.

Provides:
- `isNash_iff_bestResponse` -- a profile is Nash iff every player plays a best response
- `isNashFor_iff_bestResponseFor` -- preference-parameterized version (delegates to GameForm)
- `dominant_isBestResponse` -- a dominant strategy is a best response against any profile
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- A profile is Nash iff every player plays a best response to the others' strategies. -/
theorem isNash_iff_bestResponse (G : KernelGame ι) (σ : Profile G) :
    G.IsNash σ ↔ ∀ who, G.IsBestResponse who σ (σ who) := by
  classical
  constructor
  · intro hNash who s'
    have := hNash who s'
    rwa [Function.update_eq_self]
  · intro hBR who s'
    have := hBR who s'
    rwa [Function.update_eq_self] at this

/-- Preference-parameterized version: a profile is Nash for `pref` iff every player
    plays a best response for `pref`. Delegates to `GameForm.isNashFor_iff_bestResponseFor`. -/
theorem isNashFor_iff_bestResponseFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop) (σ : Profile G) :
    G.IsNashFor pref σ ↔ ∀ who, G.IsBestResponseFor pref who σ (σ who) :=
  G.toGameForm.isNashFor_iff_bestResponseFor pref σ

/-- A dominant strategy is a best response against any profile. -/
theorem dominant_isBestResponse (G : KernelGame ι) (who : ι)
    (s : G.Strategy who) (σ : Profile G)
    (hdom : G.IsDominant who s) : G.IsBestResponse who σ s := by
  intro s'
  exact hdom σ s'

open Classical in
/-- Best response rewritten through the first-class constant deviation operator. -/
theorem isBestResponse_iff_noConstantDeviationGain (G : KernelGame ι)
    (who : ι) (σ : Profile G) (s : G.Strategy who) :
    G.IsBestResponse who σ s ↔
      ∀ s' : G.Strategy who,
        G.euAfterDeviation who (G.constantDeviation who s) σ ≥
        G.euAfterDeviation who (G.constantDeviation who s') σ := by
  constructor <;> intro h s' <;>
    simpa [KernelGame.IsBestResponse, KernelGame.euAfterDeviation, KernelGame.constantDeviation]
      using h s'

end KernelGame

end GameTheory
