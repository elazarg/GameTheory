import Mathlib.Algebra.BigOperators.Ring.Finset
import GameTheory.KernelGame

open scoped BigOperators

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- Profile `σ` Pareto-dominates profile `τ`. -/
def ParetoDominates (G : KernelGame ι) (σ τ : Profile G) : Prop :=
  (∀ i : ι, G.eu σ i ≥ G.eu τ i) ∧ ∃ i : ι, G.eu σ i > G.eu τ i

/-- Profile `σ` is Pareto-efficient (no Pareto improvement exists). -/
def IsParetoEfficient (G : KernelGame ι) (σ : Profile G) : Prop :=
  ¬ ∃ τ : Profile G, G.ParetoDominates τ σ

/-- Individual rationality w.r.t. reservation utility `r`. -/
def IsIndividuallyRational (G : KernelGame ι)
    (r : ι → ℝ) (σ : Profile G) : Prop :=
  ∀ i : ι, G.eu σ i ≥ r i

open Classical in
/-- Exact potential game (in expected-utility form). -/
def IsExactPotential (G : KernelGame ι) (Φ : Profile G → ℝ) : Prop :=
  ∀ (who : ι) (σ : Profile G) (s' : G.Strategy who),
    G.eu (Function.update σ who s') who - G.eu σ who =
      (Φ (Function.update σ who s') - Φ σ)

open Classical in
/-- Ordinal potential game (in expected-utility form). -/
def IsOrdinalPotential (G : KernelGame ι) (Φ : Profile G → ℝ) : Prop :=
  ∀ (who : ι) (σ : Profile G) (s' : G.Strategy who),
    (G.eu (Function.update σ who s') who > G.eu σ who) ↔
      (Φ (Function.update σ who s') > Φ σ)

section FinitePlayers

variable [Fintype ι]

/-- Social welfare at profile `σ` as sum of expected utilities. -/
noncomputable def socialWelfare (G : KernelGame ι) (σ : Profile G) : ℝ :=
  ∑ i : ι, G.eu σ i

/-- Constant-sum game property at the outcome-utility level. -/
def IsConstantSum (G : KernelGame ι) (c : ℝ) : Prop :=
  ∀ ω : G.Outcome, (∑ i : ι, G.utility ω i) = c

/-- Zero-sum game property at the outcome-utility level. -/
def IsZeroSum (G : KernelGame ι) : Prop :=
  G.IsConstantSum 0

/-- Team game / identical-interest property at the outcome-utility level. -/
def IsTeamGame (G : KernelGame ι) : Prop :=
  ∀ (ω : G.Outcome) (i j : ι), G.utility ω i = G.utility ω j

end FinitePlayers

end KernelGame

end GameTheory
