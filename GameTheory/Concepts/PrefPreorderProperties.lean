import GameTheory.Concepts.SolutionConcepts
import Math.Probability

/-!
# GameTheory.Concepts.PrefPreorderProperties

Properties of preference preorders for kernel-based games.

Provides:
- `euPref_isPrefPreorder` -- the EU preference is a `PrefPreorder`
- `IsDominantFor.isBestResponseFor` -- delegates to `GameForm.IsDominantFor.isBestResponseFor`
- `IsNashFor.mono` -- delegates to `GameForm.IsNashFor.mono`
- `IsDominantFor.mono` -- delegates to `GameForm.IsDominantFor.mono`
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- The EU preference is a `PrefPreorder`: reflexive and transitive. -/
instance euPref_isPrefPreorder (G : KernelGame ι) : PrefPreorder (G.euPref) where
  refl := fun _i _x => le_refl _
  trans := fun _i _x _y _z hxy hyz => ge_trans hxy hyz

/-- A dominant-for strategy is a best-response-for against any profile.
    Delegates to `GameForm.IsDominantFor.isBestResponseFor`. -/
theorem IsDominantFor.isBestResponseFor {G : KernelGame ι}
    {pref : ι → PMF G.Outcome → PMF G.Outcome → Prop}
    {who : ι} {s : G.Strategy who}
    (hdom : G.IsDominantFor pref who s) (σ : Profile G) :
    G.IsBestResponseFor pref who σ s :=
  (show G.toGameForm.IsDominantFor pref who s from hdom).isBestResponseFor σ

/-- Monotonicity of Nash-for: if `pref₂` implies `pref₁` pointwise, then
    Nash-for `pref₂` implies Nash-for `pref₁`.
    Delegates to `GameForm.IsNashFor.mono`. -/
theorem IsNashFor.mono {G : KernelGame ι}
    {pref₁ pref₂ : ι → PMF G.Outcome → PMF G.Outcome → Prop}
    (h : ∀ i d₁ d₂, pref₂ i d₁ d₂ → pref₁ i d₁ d₂)
    {σ : Profile G} (hN : G.IsNashFor pref₂ σ) : G.IsNashFor pref₁ σ :=
  GameForm.IsNashFor.mono h hN

/-- Monotonicity of dominant-for: if `pref₂` implies `pref₁` pointwise, then
    dominant-for `pref₂` implies dominant-for `pref₁`.
    Delegates to `GameForm.IsDominantFor.mono`. -/
theorem IsDominantFor.mono {G : KernelGame ι}
    {pref₁ pref₂ : ι → PMF G.Outcome → PMF G.Outcome → Prop}
    (h : ∀ i d₁ d₂, pref₂ i d₁ d₂ → pref₁ i d₁ d₂)
    {who : ι} {s : G.Strategy who}
    (hdom : G.IsDominantFor pref₂ who s) : G.IsDominantFor pref₁ who s :=
  GameForm.IsDominantFor.mono h hdom

end KernelGame

end GameTheory
