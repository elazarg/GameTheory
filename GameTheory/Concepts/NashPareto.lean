import GameTheory.Core.GameProperties
import Math.Probability
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Concepts.StrictNashProperties

/-!
# GameTheory.Concepts.NashPareto

Relationships between Nash equilibrium concepts and Pareto efficiency.

Provides:
- `ParetoDominates.not_paretoEfficient` -- Pareto-dominated profiles are not efficient
- `ParetoDominates.trans` -- Pareto dominance is transitive
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} {G : KernelGame ι}

/-- If `τ` Pareto-dominates `σ`, then `σ` is not Pareto-efficient. -/
theorem ParetoDominates.not_paretoEfficient {σ τ : Profile G}
    (hpd : G.ParetoDominates τ σ) : ¬ G.IsParetoEfficient σ :=
  fun hpe => hpe ⟨τ, hpd⟩

/-- Preference-parametric analogue: if `τ` Pareto-dominates `σ` w.r.t.
    `pref`/`spref`, then `σ` is not Pareto-efficient w.r.t. these preferences. -/
theorem ParetoDominatesFor.not_paretoEfficientFor
    {pref spref : ι → PMF G.Outcome → PMF G.Outcome → Prop}
    {σ τ : Profile G}
    (hpd : G.ParetoDominatesFor pref spref τ σ) :
    ¬ G.IsParetoEfficientFor pref spref σ :=
  fun hpe => hpe ⟨τ, hpd⟩

/-- Preference-parametric Pareto dominance is transitive when:
    weak preference is transitive, and strict preference composes on the left
    with weak preference. -/
theorem ParetoDominatesFor.trans
    {pref spref : ι → PMF G.Outcome → PMF G.Outcome → Prop}
    {σ τ υ : Profile G}
    (htrans : ∀ i x y z, pref i x y → pref i y z → pref i x z)
    (hstrict_left : ∀ i x y z, spref i x y → pref i y z → spref i x z)
    (h1 : G.ParetoDominatesFor pref spref σ τ)
    (h2 : G.ParetoDominatesFor pref spref τ υ) :
    G.ParetoDominatesFor pref spref σ υ := by
  constructor
  · intro i
    exact htrans i _ _ _ (h1.1 i) (h2.1 i)
  · obtain ⟨i, hi⟩ := h1.2
    exact ⟨i, hstrict_left i _ _ _ hi (h2.1 i)⟩

/-- Pareto dominance is transitive. -/
theorem ParetoDominates.trans {σ τ υ : Profile G}
    (h1 : G.ParetoDominates σ τ) (h2 : G.ParetoDominates τ υ) :
    G.ParetoDominates σ υ := by
  obtain ⟨hweak1, i, hi⟩ := h1
  obtain ⟨hweak2, _⟩ := h2
  refine ⟨fun j => le_trans (hweak2 j) (hweak1 j), i, ?_⟩
  exact lt_of_le_of_lt (hweak2 i) hi

end KernelGame

end GameTheory
