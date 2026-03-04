import GameTheory.Core.GameProperties
import GameTheory.Concepts.SolutionConcepts
import Math.Probability

/-!
# GameTheory.Concepts.NashPareto

Relationships between Nash equilibrium concepts and Pareto efficiency.

Provides:
- `IsStrictNash.isNash` -- a strict Nash equilibrium is a Nash equilibrium
- `ParetoDominates.not_paretoEfficient` -- Pareto-dominated profiles are not efficient
- `ParetoDominates.trans` -- Pareto dominance is transitive
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι] {G : KernelGame ι}

/-- A strict Nash equilibrium is a Nash equilibrium. -/
theorem IsStrictNash.isNash {σ : Profile G} (hstrict : G.IsStrictNash σ) :
    G.IsNash σ := by
  classical
  intro who s'
  by_cases h : s' = σ who
  · subst h; simp [Function.update_eq_self]
  · exact le_of_lt (hstrict who s' h)

omit [DecidableEq ι] in
/-- If `τ` Pareto-dominates `σ`, then `σ` is not Pareto-efficient. -/
theorem ParetoDominates.not_paretoEfficient {σ τ : Profile G}
    (hpd : G.ParetoDominates τ σ) : ¬ G.IsParetoEfficient σ :=
  fun hpe => hpe ⟨τ, hpd⟩

omit [DecidableEq ι] in
/-- Preference-parametric analogue: if `τ` Pareto-dominates `σ` w.r.t.
    `pref`/`spref`, then `σ` is not Pareto-efficient w.r.t. these preferences. -/
theorem ParetoDominatesFor.not_paretoEfficientFor
    {pref spref : ι → PMF G.Outcome → PMF G.Outcome → Prop}
    {σ τ : Profile G}
    (hpd : G.ParetoDominatesFor pref spref τ σ) :
    ¬ G.IsParetoEfficientFor pref spref σ :=
  fun hpe => hpe ⟨τ, hpd⟩

omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
/-- Pareto dominance is transitive. -/
theorem ParetoDominates.trans {σ τ υ : Profile G}
    (h1 : G.ParetoDominates σ τ) (h2 : G.ParetoDominates τ υ) :
    G.ParetoDominates σ υ := by
  have h1' : G.ParetoDominatesFor
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) ≥ expect d₂ (fun ω => G.utility ω who))
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) > expect d₂ (fun ω => G.utility ω who))
      σ τ := (G.ParetoDominates_iff_ParetoDominatesFor_eu σ τ).mp h1
  have h2' : G.ParetoDominatesFor
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) ≥ expect d₂ (fun ω => G.utility ω who))
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) > expect d₂ (fun ω => G.utility ω who))
      τ υ := (G.ParetoDominates_iff_ParetoDominatesFor_eu τ υ).mp h2
  have htrans :
      ∀ i x y z,
        (expect x (fun ω => G.utility ω i) ≥ expect y (fun ω => G.utility ω i)) →
        (expect y (fun ω => G.utility ω i) ≥ expect z (fun ω => G.utility ω i)) →
        (expect x (fun ω => G.utility ω i) ≥ expect z (fun ω => G.utility ω i)) := by
    intro i x y z hxy hyz
    linarith
  have hstrict_left :
      ∀ i x y z,
        (expect x (fun ω => G.utility ω i) > expect y (fun ω => G.utility ω i)) →
        (expect y (fun ω => G.utility ω i) ≥ expect z (fun ω => G.utility ω i)) →
        (expect x (fun ω => G.utility ω i) > expect z (fun ω => G.utility ω i)) := by
    intro i x y z hxy hyz
    linarith
  exact (G.ParetoDominates_iff_ParetoDominatesFor_eu σ υ).mpr
    (KernelGame.ParetoDominatesFor.trans (G := G) htrans hstrict_left h1' h2')

end KernelGame

end GameTheory
