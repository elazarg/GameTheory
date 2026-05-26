/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import GameTheory.Concepts.SolutionConcepts

/-!
# GameTheory.Concepts.EUProperties

Basic properties of expected utility (`KernelGame.eu`).

Provides:
- `eu_eq_expect` — EU restated as `expect` (definitional, for external use)
- `eu_eq_sum` — EU as a finite sum when the outcome type is finite
- `eu_pure_outcome` — EU under a deterministic outcome kernel
- `eu_nonneg_of_utility_nonneg` — non-negative utilities imply non-negative EU
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- EU is the expected value of utility under the outcome distribution. -/
theorem eu_eq_expect {G : KernelGame ι} (σ : Profile G) (who : ι) :
    G.eu σ who = expect (G.outcomeKernel σ) (fun ω => G.utility ω who) := rfl

/-- For finite outcome types, EU equals a finite sum over outcomes. -/
theorem eu_eq_sum {G : KernelGame ι} [Fintype G.Outcome] (σ : Profile G) (who : ι) :
    G.eu σ who = ∑ ω : G.Outcome, (G.outcomeKernel σ ω).toReal * G.utility ω who := by
  simp [eu, expect_eq_sum]

/-- If the outcome kernel yields a pure (deterministic) outcome, EU equals
    the utility at that outcome. -/
theorem eu_pure_outcome {G : KernelGame ι} (σ : Profile G) (who : ι)
    (ω : G.Outcome) (h : G.outcomeKernel σ = PMF.pure ω) :
    G.eu σ who = G.utility ω who := by
  simp [eu, h, expect_pure]

/-- If all utilities for a player are non-negative, EU is non-negative. -/
theorem eu_nonneg_of_utility_nonneg {G : KernelGame ι}
    (σ : Profile G) (who : ι)
    (h : ∀ ω : G.Outcome, G.utility ω who ≥ 0) :
    G.eu σ who ≥ 0 := by
  unfold eu expect
  exact tsum_nonneg (fun ω => mul_nonneg ENNReal.toReal_nonneg (h ω))

end KernelGame

end GameTheory
