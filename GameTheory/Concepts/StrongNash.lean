import GameTheory.Concepts.SolutionConcepts
import GameTheory.Core.GameProperties

/-!
# GameTheory.Concepts.StrongNash

Strong Nash Equilibrium (Aumann 1959): a profile from which no coalition can
collectively deviate so as to weakly improve every member with at least one
strict gain.

This is strictly stronger than ordinary Nash. Ordinary Nash rules out only
*unilateral* profitable deviations; Strong Nash also rules out profitable
deviations by any subset of players.

## Main definitions

- `KernelGame.coalitionDeviation` — coalitional profile transformer
- `KernelGame.IsStrongNash` — Strong Nash equilibrium

## Main results

- `KernelGame.IsStrongNash.isNash` — Strong Nash ⇒ Nash (singleton coalition)
- `KernelGame.IsStrongNash.isParetoEfficient` — Strong Nash ⇒ Pareto efficient
  (grand coalition)
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type}

section CoalitionDeviation
variable [DecidableEq ι]

/-- Coalitional deviation: the profile that uses `τ i` on players `i ∈ C` and
keeps `σ i` for everyone else. -/
def coalitionDeviation (G : KernelGame ι) (C : Finset ι) (σ τ : Profile G) :
    Profile G :=
  fun i => if i ∈ C then τ i else σ i

@[simp] theorem coalitionDeviation_of_mem (G : KernelGame ι)
    {C : Finset ι} {σ τ : Profile G} {i : ι} (h : i ∈ C) :
    G.coalitionDeviation C σ τ i = τ i := by
  simp [coalitionDeviation, h]

@[simp] theorem coalitionDeviation_of_not_mem (G : KernelGame ι)
    {C : Finset ι} {σ τ : Profile G} {i : ι} (h : i ∉ C) :
    G.coalitionDeviation C σ τ i = σ i := by
  simp [coalitionDeviation, h]

@[simp] theorem coalitionDeviation_empty (G : KernelGame ι) (σ τ : Profile G) :
    G.coalitionDeviation ∅ σ τ = σ := by
  ext i; simp [coalitionDeviation]

@[simp] theorem coalitionDeviation_univ (G : KernelGame ι) [Fintype ι]
    (σ τ : Profile G) :
    G.coalitionDeviation Finset.univ σ τ = τ := by
  ext i; simp [coalitionDeviation]

/-- The singleton coalition deviation is the standard unilateral update. -/
theorem coalitionDeviation_singleton (G : KernelGame ι) (who : ι)
    (σ τ : Profile G) :
    G.coalitionDeviation {who} σ τ = Function.update σ who (τ who) := by
  ext i
  by_cases hi : i = who
  · subst hi; simp [coalitionDeviation]
  · simp [coalitionDeviation, hi]

end CoalitionDeviation

/-- A profile `σ` is a **Strong Nash equilibrium** if for every coalition `C`
and every joint deviation `τ`, if every member of `C` weakly improves under the
coalitional deviation, then every member is in fact exactly indifferent. This
forbids any *Pareto-improving* joint deviation (weakly better for all, strictly
better for some). -/
def IsStrongNash [DecidableEq ι] (G : KernelGame ι) (σ : Profile G) : Prop :=
  ∀ (C : Finset ι) (τ : Profile G),
    (∀ i ∈ C, G.eu (G.coalitionDeviation C σ τ) i ≥ G.eu σ i) →
    ∀ i ∈ C, G.eu (G.coalitionDeviation C σ τ) i = G.eu σ i

/-- Textbook formulation: Strong Nash forbids any joint deviation that weakly
improves every coalition member while strictly improving at least one. -/
theorem isStrongNash_iff_no_profitableCoalitionDeviation [DecidableEq ι]
    (G : KernelGame ι) (σ : Profile G) :
    G.IsStrongNash σ ↔
    ∀ (C : Finset ι) (τ : Profile G),
      ¬ ((∀ i ∈ C, G.eu (G.coalitionDeviation C σ τ) i ≥ G.eu σ i) ∧
         (∃ i ∈ C, G.eu (G.coalitionDeviation C σ τ) i > G.eu σ i)) := by
  refine ⟨fun h C τ ⟨hweak, i, hi, hstrict⟩ => ?_, fun h C τ hweak i hi => ?_⟩
  · have := h C τ hweak i hi
    linarith
  · by_contra hne
    refine h C τ ⟨hweak, i, hi, ?_⟩
    exact lt_of_le_of_ne (hweak i hi) (Ne.symm hne)

namespace IsStrongNash

variable [DecidableEq ι]

/-- Strong Nash implies Nash: apply the definition to the singleton coalition
`{who}`. -/
theorem isNash {G : KernelGame ι} {σ : Profile G} (h : G.IsStrongNash σ) :
    G.IsNash σ := by
  intro who s'
  by_contra hlt
  rw [not_le] at hlt
  -- hlt : G.eu σ who < G.eu (Function.update σ who s') who
  let τ : Profile G := Function.update σ who s'
  have h_dev : G.coalitionDeviation {who} σ τ = Function.update σ who s' := by
    rw [G.coalitionDeviation_singleton]; simp [τ]
  have hweak : ∀ i ∈ ({who} : Finset ι),
      G.eu (G.coalitionDeviation {who} σ τ) i ≥ G.eu σ i := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    rw [h_dev]
    linarith
  have heq := h {who} τ hweak who (Finset.mem_singleton_self _)
  rw [h_dev] at heq
  linarith

/-- Strong Nash implies Pareto efficient: apply the definition to the grand
coalition `Finset.univ`. -/
theorem isParetoEfficient {G : KernelGame ι} [Finite ι] {σ : Profile G}
    (h : G.IsStrongNash σ) : G.IsParetoEfficient σ := by
  haveI : Fintype ι := Fintype.ofFinite ι
  rintro ⟨τ, hweak_all, i, hi_strict⟩
  -- ParetoDominates τ σ unfolds to (∀ i, eu τ i ≥ eu σ i) ∧ (∃ i, eu τ i > eu σ i).
  have hweak : ∀ j ∈ (Finset.univ : Finset ι),
      G.eu (G.coalitionDeviation Finset.univ σ τ) j ≥ G.eu σ j := by
    intro j _; rw [G.coalitionDeviation_univ]; exact hweak_all j
  have heq_i := h Finset.univ τ hweak i (Finset.mem_univ i)
  rw [G.coalitionDeviation_univ] at heq_i
  linarith

end IsStrongNash

end KernelGame

end GameTheory
