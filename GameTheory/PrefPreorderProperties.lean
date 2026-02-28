import GameTheory.SolutionConcepts

/-!
# GameTheory.PrefPreorderProperties

Properties of preference preorders for kernel-based games.

Provides:
- `euPref_isPrefPreorder` — the EU preference is a `PrefPreorder`
- `IsDominantFor.isBestResponseFor` — a dominant-for strategy is a best-response-for
  against any profile
- `IsNashFor.mono` — monotonicity of Nash-for w.r.t. preference weakening
- `IsDominantFor.mono` — monotonicity of dominant-for w.r.t. preference weakening
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- The EU preference is a `PrefPreorder`: reflexive and transitive. -/
instance euPref_isPrefPreorder (G : KernelGame ι) : PrefPreorder (G.euPref) where
  refl := fun _i _x => le_refl _
  trans := fun _i _x _y _z hxy hyz => ge_trans hxy hyz

/-- A dominant-for strategy is a best-response-for against any profile. -/
theorem IsDominantFor.isBestResponseFor {G : KernelGame ι}
    {pref : ι → PMF G.Outcome → PMF G.Outcome → Prop}
    {who : ι} {s : G.Strategy who}
    (hdom : G.IsDominantFor pref who s) (σ : Profile G) :
    G.IsBestResponseFor pref who σ s := by
  intro s'
  exact hdom σ s'

/-- Monotonicity of Nash-for: if `pref₂` implies `pref₁` pointwise, then
    Nash-for `pref₂` implies Nash-for `pref₁`. -/
theorem IsNashFor.mono {G : KernelGame ι}
    {pref₁ pref₂ : ι → PMF G.Outcome → PMF G.Outcome → Prop}
    (h : ∀ i d₁ d₂, pref₂ i d₁ d₂ → pref₁ i d₁ d₂)
    {σ : Profile G} (hN : G.IsNashFor pref₂ σ) : G.IsNashFor pref₁ σ := by
  intro who s'
  exact h who _ _ (hN who s')

/-- Monotonicity of dominant-for: if `pref₂` implies `pref₁` pointwise, then
    dominant-for `pref₂` implies dominant-for `pref₁`. -/
theorem IsDominantFor.mono {G : KernelGame ι}
    {pref₁ pref₂ : ι → PMF G.Outcome → PMF G.Outcome → Prop}
    (h : ∀ i d₁ d₂, pref₂ i d₁ d₂ → pref₁ i d₁ d₂)
    {who : ι} {s : G.Strategy who}
    (hdom : G.IsDominantFor pref₂ who s) : G.IsDominantFor pref₁ who s := by
  intro σ s'
  exact h who _ _ (hdom σ s')

end KernelGame

end GameTheory
