import GameTheory.SolutionConcepts
import GameTheory.GameProperties

open scoped BigOperators

/-!
# GameTheory.OfEUProperties

Simplification theorems for games constructed via `KernelGame.ofEU`.

Since `ofEU` builds a kernel game whose outcome kernel is a point mass,
expected utility reduces to direct function evaluation.  The theorems here
push `simp` through the solution-concept definitions so that Nash equilibrium,
dominance, best response, strict Nash, and social welfare all reduce to
plain inequalities (or sums) on the underlying utility function.
-/

namespace GameTheory

variable {ι : Type}

open Classical in
/-- Nash equilibrium for an `ofEU` game reduces to a direct inequality
    on the utility function: no player can improve by unilateral deviation. -/
theorem ofEU_isNash_iff (S : ι → Type) (u : (∀ i, S i) → Payoff ι) (σ : ∀ i, S i) :
    (KernelGame.ofEU S u).IsNash σ ↔
      ∀ (who : ι) (s' : S who), u σ who ≥ u (Function.update σ who s') who := by
  unfold KernelGame.IsNash
  simp only [KernelGame.eu_ofEU]
  rfl

open Classical in
/-- Dominant strategy for an `ofEU` game reduces to a direct inequality
    on the utility function for all opponent profiles. -/
theorem ofEU_isDominant_iff (S : ι → Type) (u : (∀ i, S i) → Payoff ι) (who : ι) (s : S who) :
    (KernelGame.ofEU S u).IsDominant who s ↔
      ∀ (σ : ∀ i, S i) (s' : S who),
        u (Function.update σ who s) who ≥ u (Function.update σ who s') who := by
  unfold KernelGame.IsDominant
  simp only [KernelGame.eu_ofEU]
  rfl

open Classical in
/-- Best response for an `ofEU` game reduces to a direct inequality
    on the utility function against all alternative strategies. -/
theorem ofEU_isBestResponse_iff (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (who : ι) (σ : ∀ i, S i) (s : S who) :
    (KernelGame.ofEU S u).IsBestResponse who σ s ↔
      ∀ (s' : S who),
        u (Function.update σ who s) who ≥ u (Function.update σ who s') who := by
  unfold KernelGame.IsBestResponse
  simp only [KernelGame.eu_ofEU]
  rfl

open Classical in
/-- Strict Nash equilibrium for an `ofEU` game reduces to a strict inequality
    on the utility function for every non-trivial unilateral deviation. -/
theorem ofEU_isStrictNash_iff (S : ι → Type) (u : (∀ i, S i) → Payoff ι) (σ : ∀ i, S i) :
    (KernelGame.ofEU S u).IsStrictNash σ ↔
      ∀ (who : ι) (s' : S who), s' ≠ σ who →
        u σ who > u (Function.update σ who s') who := by
  unfold KernelGame.IsStrictNash
  simp only [KernelGame.eu_ofEU]
  rfl

/-- Social welfare for an `ofEU` game equals the sum of utility values. -/
theorem ofEU_socialWelfare_eq [Fintype ι] (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (σ : ∀ i, S i) :
    (KernelGame.ofEU S u).socialWelfare σ = ∑ i, u σ i := by
  unfold KernelGame.socialWelfare
  simp only [KernelGame.eu_ofEU]

end GameTheory
