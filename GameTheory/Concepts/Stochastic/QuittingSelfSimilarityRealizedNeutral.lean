/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityRealizedBounds

/-!
# Neutral faces of realized finite quitting holonomy

The weighted realized-block bounds force the prescribed intercept and the
unilateral tail intercept to vanish when their survival slope is one.  Thus the
only realized neutral maps are the identity and a threshold closure.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- On the neutral prescribed face, weighted realizability forces zero
intercept. -/
theorem quittingFiniteBoundaryHolonomy_prescribed_intercept_eq_zero_of_survival_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι)
    (hsurvival :
      (QuittingBoundaryHolonomy.prescribed
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).survival = 1) :
    (QuittingBoundaryHolonomy.prescribed
      (quittingFiniteBoundaryHolonomy reward roots start extra) who).intercept = 0 := by
  let summary := QuittingBoundaryHolonomy.prescribed
    (quittingFiniteBoundaryHolonomy reward roots start extra) who
  have hweighted :=
    abs_quittingFiniteBoundaryHolonomy_prescribed_intercept_le
      reward roots start extra who
  apply QuittingAffineSummary.intercept_eq_zero_of_abs_intercept_le_mul_absorptionMass
    summary (quittingRewardBound reward)
  · simpa [summary] using hweighted
  · simpa [summary] using hsurvival

/-- A realized prescribed block with survival one is literally the identity
continuation map. -/
theorem quittingFiniteBoundaryHolonomy_prescribed_eval_eq_of_survival_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι)
    (hsurvival :
      (QuittingBoundaryHolonomy.prescribed
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).survival = 1)
    (w : ℝ) :
    (QuittingBoundaryHolonomy.prescribed
      (quittingFiniteBoundaryHolonomy reward roots start extra) who).eval w = w := by
  have hintercept :=
    quittingFiniteBoundaryHolonomy_prescribed_intercept_eq_zero_of_survival_eq_one
      reward roots start extra who hsurvival
  simp [QuittingAffineSummary.eval, hsurvival, hintercept]

/-- On the neutral unilateral tail face, weighted realizability forces zero
tail intercept. -/
theorem quittingFiniteBoundaryHolonomy_bestResponse_tail_eq_zero_of_survival_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι)
    (hsurvival :
      (QuittingBoundaryHolonomy.bestResponse
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).survival = 1) :
    (QuittingBoundaryHolonomy.bestResponse
      (quittingFiniteBoundaryHolonomy reward roots start extra) who).tail = 0 := by
  let summary := QuittingBoundaryHolonomy.bestResponse
    (quittingFiniteBoundaryHolonomy reward roots start extra) who
  have hweighted :=
    abs_quittingFiniteBoundaryHolonomy_bestResponse_tail_le
      reward roots start extra who
  apply QuittingMaxAffineSummary.tail_eq_zero_of_abs_tail_le_mul_absorptionMass
    summary (quittingRewardBound reward)
  · simpa [summary] using hweighted
  · simpa [summary] using hsurvival

/-- A realized unilateral tail map with survival one is literally a threshold
closure `w ↦ max early w`. -/
theorem quittingFiniteBoundaryHolonomy_bestResponse_eval_eq_max_of_survival_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι)
    (hsurvival :
      (QuittingBoundaryHolonomy.bestResponse
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).survival = 1)
    (w : ℝ) :
    (QuittingBoundaryHolonomy.bestResponse
      (quittingFiniteBoundaryHolonomy reward roots start extra) who).eval w =
      max
        (QuittingBoundaryHolonomy.bestResponse
          (quittingFiniteBoundaryHolonomy reward roots start extra) who).early
        w := by
  have htail :=
    quittingFiniteBoundaryHolonomy_bestResponse_tail_eq_zero_of_survival_eq_one
      reward roots start extra who hsurvival
  simp [QuittingMaxAffineSummary.eval, hsurvival, htail]

/-- If every prescribed and unilateral tail slope of an actual block is
neutral, strategic self-similarity reduces exactly to the early stopping floors
lying below the target. -/
theorem quittingFiniteBoundaryHolonomy_isSelfSimilarAt_iff_of_survival_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ)
    (target : Payoff ι)
    (hprescribed : ∀ who,
      (QuittingBoundaryHolonomy.prescribed
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).survival = 1)
    (hbestResponse : ∀ who,
      (QuittingBoundaryHolonomy.bestResponse
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).survival = 1) :
    (quittingFiniteBoundaryHolonomy reward roots start extra).IsSelfSimilarAt
        target ↔
      ∀ who,
        (QuittingBoundaryHolonomy.bestResponse
          (quittingFiniteBoundaryHolonomy reward roots start extra) who).early ≤
            target who := by
  constructor
  · intro hself who
    have hsafe := hself.bestResponse_safe who
    rw [quittingFiniteBoundaryHolonomy_bestResponse_eval_eq_max_of_survival_eq_one
      reward roots start extra who (hbestResponse who)] at hsafe
    exact (max_le_iff.mp hsafe).1
  · intro hearly
    constructor
    · intro who
      unfold QuittingAffineSummary.IsFixedAt
      exact quittingFiniteBoundaryHolonomy_prescribed_eval_eq_of_survival_eq_one
        reward roots start extra who (hprescribed who) (target who)
    · intro who
      rw [quittingFiniteBoundaryHolonomy_bestResponse_eval_eq_max_of_survival_eq_one
        reward roots start extra who (hbestResponse who)]
      exact max_le (hearly who) le_rfl

end GameTheory
