/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Correlation.ApproximateCorrelatedEq
import GameTheory.Concepts.ZeroSum.ConstantSumCorrelated

/-!
# No-regret learning converges to coarse correlated equilibrium

The keystone reduction of learning dynamics: the **time-average** of a play sequence is a
coarse correlated equilibrium up to its **average external regret**. Combined with any
no-regret learning rule (sublinear cumulative regret), the empirical distribution of play
converges to the set of coarse correlated equilibria.

The argument is pure averaging on top of the static characterization
`isCoarseCorrelatedEq_iff_noExternalRegret`: external regret is linear in the recommendation
distribution, so the regret of an average of distributions is the average of their regrets.

All statements assume `[Finite (Profile G)] [Finite G.Outcome]` (the regret-as-expectation
identity needs a finite outcome space, and `expect` linearity needs a finite profile space).

## Main definitions

* `KernelGame.timeAverage` — the uniform average of a finite family of profile distributions

## Main results

* `KernelGame.externalRegret_eq_expect` — external regret as the expected pointwise deviation gain
* `KernelGame.externalRegret_timeAverage` — regret of the time-average is the average of regrets
* `KernelGame.timeAverage_isεCCE_of_regret_le` — a cumulative regret bound `R` over horizon `T`
  makes the time-average an `(R/T)`-coarse correlated equilibrium
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- Expectation under the uniform distribution on `Fin n` is the average. -/
theorem expect_uniformOfFintype_fin {n : ℕ} [NeZero n] (g : Fin n → ℝ) :
    expect (PMF.uniformOfFintype (Fin n)) g = (∑ t, g t) / n := by
  rw [expect_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, inv_mul_eq_div]
  rw [← Finset.sum_div]

variable (G : KernelGame ι) [Finite (Profile G)] [Finite G.Outcome]

/-- External regret is the expected gain from the constant deviation, pointwise over the
    recommendation distribution. This linearity in `μ` is what drives the time-average reduction. -/
theorem externalRegret_eq_expect (μ : PMF (Profile G)) (who : ι) (s' : G.Strategy who) :
    G.externalRegret μ who s'
      = expect μ (fun σ => G.eu (Function.update σ who s') who - G.eu σ who) := by
  unfold externalRegret
  rw [correlatedEu_constantDeviationDistribution_eq_expect_update, correlatedEu_eq_expect_eu,
    ← expect_sub]

/-- The time-average (uniform mixture) of a finite family of profile distributions. -/
noncomputable def timeAverage {T : ℕ} [NeZero T] (q : Fin T → PMF (Profile G)) : PMF (Profile G) :=
  (PMF.uniformOfFintype (Fin T)).bind q

/-- The external regret of a time-average is the average of the per-round external regrets. -/
theorem externalRegret_timeAverage {T : ℕ} [NeZero T] (q : Fin T → PMF (Profile G))
    (who : ι) (s' : G.Strategy who) :
    G.externalRegret (G.timeAverage q) who s'
      = (∑ t, G.externalRegret (q t) who s') / T := by
  rw [externalRegret_eq_expect]
  unfold timeAverage
  rw [expect_bind, expect_uniformOfFintype_fin]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← externalRegret_eq_expect]

/-- **No-regret ⇒ coarse correlated equilibrium.** If the cumulative external regret of every
    player against every fixed deviation is at most `R` over horizon `T`, then the time-average
    of play is an `(R/T)`-coarse correlated equilibrium. As `R/T → 0` (sublinear regret), the
    empirical distribution of play approaches the set of coarse correlated equilibria. -/
theorem timeAverage_isεCCE_of_regret_le {T : ℕ} [NeZero T] {q : Fin T → PMF (Profile G)}
    {R : ℝ} (h : ∀ who s', (∑ t, G.externalRegret (q t) who s') ≤ R) :
    G.IsεCoarseCorrelatedEq (R / T) (G.timeAverage q) := by
  rw [isεCoarseCorrelatedEq_iff_externalRegret_le]
  intro who s'
  rw [externalRegret_timeAverage]
  have hT : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  exact (div_le_div_iff_of_pos_right hT).2 (h who s')

end KernelGame

end GameTheory
