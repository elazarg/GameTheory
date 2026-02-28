import GameTheory.GameProperties

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- No profile Pareto-dominates itself. -/
theorem ParetoDominates.irrefl (G : KernelGame ι) (σ : Profile G) :
    ¬ G.ParetoDominates σ σ := by
  intro ⟨_, ⟨i, hi⟩⟩
  exact lt_irrefl _ hi

/-- Pareto dominance is asymmetric: if `σ` Pareto-dominates `τ`, then `τ` cannot
    Pareto-dominate `σ`. -/
theorem ParetoDominates.asymm (G : KernelGame ι) (σ τ : Profile G) :
    G.ParetoDominates σ τ → ¬ G.ParetoDominates τ σ := by
  intro ⟨_, ⟨i, hi⟩⟩ ⟨hge, _⟩
  have := hge i
  linarith

end KernelGame

end GameTheory
