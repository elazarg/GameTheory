import GameTheory.Core.GameProperties
import Math.Probability

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- No profile Pareto-dominates itself (preference-parametric version). -/
theorem ParetoDominatesFor.irrefl (G : KernelGame ι)
    {pref spref : ι → PMF G.Outcome → PMF G.Outcome → Prop}
    (hirr : ∀ i x, ¬ spref i x x) (σ : Profile G) :
    ¬ G.ParetoDominatesFor pref spref σ σ := by
  simpa [KernelGame.ParetoDominatesFor] using
    (GameForm.ParetoDominatesFor.irrefl (F := G.toGameForm) (pref := pref) (spref := spref) hirr σ)

/-- Preference-parametric Pareto dominance is asymmetric under strict-vs-weak
    incompatibility. -/
theorem ParetoDominatesFor.asymm (G : KernelGame ι)
    {pref spref : ι → PMF G.Outcome → PMF G.Outcome → Prop}
    (hanti : ∀ i x y, spref i x y → ¬ pref i y x) (σ τ : Profile G) :
    G.ParetoDominatesFor pref spref σ τ → ¬ G.ParetoDominatesFor pref spref τ σ := by
  simpa [KernelGame.ParetoDominatesFor] using
    (GameForm.ParetoDominatesFor.asymm
      (F := G.toGameForm) (pref := pref) (spref := spref) hanti σ τ)

/-- No profile Pareto-dominates itself. -/
theorem ParetoDominates.irrefl (G : KernelGame ι) (σ : Profile G) :
    ¬ G.ParetoDominates σ σ := by
  intro h
  have heu : G.ParetoDominatesFor
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) ≥ expect d₂ (fun ω => G.utility ω who))
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) > expect d₂ (fun ω => G.utility ω who))
      σ σ := (G.ParetoDominates_iff_ParetoDominatesFor_eu σ σ).mp h
  have hirr : ∀ i x, ¬ (expect x (fun ω => G.utility ω i) > expect x (fun ω => G.utility ω i)) := by
    intro i x hx
    exact lt_irrefl _ hx
  exact (KernelGame.ParetoDominatesFor.irrefl (G := G) (pref := fun who d₁ d₂ =>
      expect d₁ (fun ω => G.utility ω who) ≥ expect d₂ (fun ω => G.utility ω who))
      (spref := fun who d₁ d₂ =>
      expect d₁ (fun ω => G.utility ω who) > expect d₂ (fun ω => G.utility ω who))
      hirr σ) heu

/-- Pareto dominance is asymmetric: if `σ` Pareto-dominates `τ`, then `τ` cannot
    Pareto-dominate `σ`. -/
theorem ParetoDominates.asymm (G : KernelGame ι) (σ τ : Profile G) :
    G.ParetoDominates σ τ → ¬ G.ParetoDominates τ σ := by
  intro hστ hτσ
  have hστ' : G.ParetoDominatesFor
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) ≥ expect d₂ (fun ω => G.utility ω who))
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) > expect d₂ (fun ω => G.utility ω who))
      σ τ := (G.ParetoDominates_iff_ParetoDominatesFor_eu σ τ).mp hστ
  have hτσ' : G.ParetoDominatesFor
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) ≥ expect d₂ (fun ω => G.utility ω who))
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) > expect d₂ (fun ω => G.utility ω who))
      τ σ := (G.ParetoDominates_iff_ParetoDominatesFor_eu τ σ).mp hτσ
  have hanti :
      ∀ i x y, (expect x (fun ω => G.utility ω i) > expect y (fun ω => G.utility ω i)) →
        ¬ (expect y (fun ω => G.utility ω i) ≥ expect x (fun ω => G.utility ω i)) := by
    intro i x y hlt hge
    linarith
  exact (KernelGame.ParetoDominatesFor.asymm (G := G)
    (pref := fun who d₁ d₂ =>
      expect d₁ (fun ω => G.utility ω who) ≥ expect d₂ (fun ω => G.utility ω who))
    (spref := fun who d₁ d₂ =>
      expect d₁ (fun ω => G.utility ω who) > expect d₂ (fun ω => G.utility ω who))
    hanti σ τ hστ') hτσ'

end KernelGame

end GameTheory
