import GameTheory.SolutionConcepts

open scoped BigOperators

/-!
# GameTheory.EUProperties

Basic properties of expected utility (`KernelGame.eu`).

Provides:
- `eu_eq_expect` — EU restated as `expect` (definitional, for external use)
- `eu_eq_sum` — EU as a finite sum when the outcome type is finite
- `eu_pure_outcome` — EU under a deterministic outcome kernel
- `eu_nonneg_of_utility_nonneg` — non-negative utilities imply non-negative EU
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

omit [DecidableEq ι] in
/-- EU is the expected value of utility under the outcome distribution. -/
theorem eu_eq_expect {G : KernelGame ι} (σ : Profile G) (who : ι) :
    G.eu σ who = expect (G.outcomeKernel σ) (fun ω => G.utility ω who) := rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- For finite outcome types, EU equals a finite sum over outcomes. -/
theorem eu_eq_sum {G : KernelGame ι} [Fintype G.Outcome] (σ : Profile G) (who : ι) :
    G.eu σ who = ∑ ω : G.Outcome, (G.outcomeKernel σ ω).toReal * G.utility ω who := by
  simp [eu, expect_eq_sum]

omit [DecidableEq ι] in
/-- If the outcome kernel yields a pure (deterministic) outcome, EU equals
    the utility at that outcome. -/
theorem eu_pure_outcome {G : KernelGame ι} (σ : Profile G) (who : ι)
    (ω : G.Outcome) (h : G.outcomeKernel σ = PMF.pure ω) :
    G.eu σ who = G.utility ω who := by
  simp [eu, h, expect_pure]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- If all utilities for a player are non-negative, EU is non-negative. -/
theorem eu_nonneg_of_utility_nonneg {G : KernelGame ι} [Fintype G.Outcome]
    (σ : Profile G) (who : ι)
    (h : ∀ ω : G.Outcome, G.utility ω who ≥ 0) :
    G.eu σ who ≥ 0 := by
  rw [eu_eq_sum]
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg
  · exact ENNReal.toReal_nonneg
  · exact h ω

end KernelGame

end GameTheory
