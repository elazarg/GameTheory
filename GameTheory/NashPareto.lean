import GameTheory.GameProperties
import GameTheory.SolutionConcepts

/-!
# GameTheory.NashPareto

Relationships between Nash equilibrium concepts and Pareto efficiency.

Provides:
- `IsStrictNash.isNash` — a strict Nash equilibrium is a Nash equilibrium
- `ParetoDominates.not_paretoEfficient` — Pareto-dominated profiles are not efficient
- `ParetoDominates.trans` — Pareto dominance is transitive
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type} {G : KernelGame ι}

/-- A strict Nash equilibrium is a Nash equilibrium. -/
theorem IsStrictNash.isNash {σ : Profile G} (hstrict : G.IsStrictNash σ) :
    G.IsNash σ := by
  classical
  intro who s'
  by_cases h : s' = σ who
  · subst h; simp [Function.update_eq_self]
  · exact le_of_lt (hstrict who s' h)

/-- If `τ` Pareto-dominates `σ`, then `σ` is not Pareto-efficient. -/
theorem ParetoDominates.not_paretoEfficient {σ τ : Profile G}
    (hpd : G.ParetoDominates τ σ) : ¬ G.IsParetoEfficient σ :=
  fun hpe => hpe ⟨τ, hpd⟩

/-- Pareto dominance is transitive. -/
theorem ParetoDominates.trans {σ τ υ : Profile G}
    (h1 : G.ParetoDominates σ τ) (h2 : G.ParetoDominates τ υ) :
    G.ParetoDominates σ υ := by
  constructor
  · intro i; have := h1.1 i; have := h2.1 i; linarith
  · obtain ⟨i, hi⟩ := h1.2; exact ⟨i, by have := h2.1 i; linarith⟩

end KernelGame

end GameTheory
