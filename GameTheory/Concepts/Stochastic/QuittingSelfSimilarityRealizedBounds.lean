/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityAffineTangent
import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityMaxAffineTangent
import GameTheory.Concepts.Stochastic.QuittingBoundaryHolonomyWeightedBounds

/-!
# Absorbed-mass bounds for realized finite quitting holonomy

Weighted intercept estimates for actual blocks imply compact conditional
anchors and residuals which are uniformly first-order in absorbed mass.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The normalized prescribed anchor of every nonneutral realized block stays
inside the terminal reward bound. -/
theorem abs_quittingFiniteBoundaryHolonomy_prescribed_fixedPoint_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι)
    (hsurvival :
      (QuittingBoundaryHolonomy.prescribed
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).survival ≠ 1) :
    |(QuittingBoundaryHolonomy.prescribed
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).fixedPoint| ≤
      quittingRewardBound reward := by
  let summary := QuittingBoundaryHolonomy.prescribed
    (quittingFiniteBoundaryHolonomy reward roots start extra) who
  obtain ⟨_, hsurvival_le, _, _, _⟩ :=
    quittingFiniteBoundaryHolonomy_coordinates_bounded
      reward roots start extra who
  have hweighted :=
    abs_quittingFiniteBoundaryHolonomy_prescribed_intercept_le
      reward roots start extra who
  apply QuittingAffineSummary.abs_fixedPoint_le_of_abs_intercept_le_mul_absorptionMass
    summary (quittingRewardBound reward)
  · simpa [summary] using hsurvival_le
  · simpa [summary] using hsurvival
  · simpa [summary] using hweighted

/-- The normalized unilateral tail anchor of every nonneutral realized block
stays inside the terminal reward bound. -/
theorem abs_quittingFiniteBoundaryHolonomy_bestResponse_tailAnchor_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι)
    (hsurvival :
      (QuittingBoundaryHolonomy.bestResponse
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).survival ≠ 1) :
    |(QuittingBoundaryHolonomy.bestResponse
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).tailAnchor| ≤
      quittingRewardBound reward := by
  let summary := QuittingBoundaryHolonomy.bestResponse
    (quittingFiniteBoundaryHolonomy reward roots start extra) who
  obtain ⟨_, _, _, _, hsurvival_le⟩ :=
    quittingFiniteBoundaryHolonomy_coordinates_bounded
      reward roots start extra who
  have hweighted :=
    abs_quittingFiniteBoundaryHolonomy_bestResponse_tail_le
      reward roots start extra who
  apply QuittingMaxAffineSummary.abs_tailAnchor_le_of_abs_tail_le_mul_absorptionMass
    summary (quittingRewardBound reward)
  · simpa [summary] using hsurvival_le
  · simpa [summary] using hsurvival
  · simpa [summary] using hweighted

/-- Every realized prescribed target residual is first-order in the block's
own absorbed mass. -/
theorem abs_quittingFiniteBoundaryHolonomy_prescribed_targetResidual_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι)
    (target : ℝ) :
    |(QuittingBoundaryHolonomy.prescribed
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).targetResidual target| ≤
      (quittingRewardBound reward + |target|) *
        (QuittingBoundaryHolonomy.prescribed
          (quittingFiniteBoundaryHolonomy reward roots start extra) who).absorptionMass := by
  let summary := QuittingBoundaryHolonomy.prescribed
    (quittingFiniteBoundaryHolonomy reward roots start extra) who
  change |summary.targetResidual target| ≤
    (quittingRewardBound reward + |target|) * summary.absorptionMass
  obtain ⟨_, hsurvival_le, _, _, _⟩ :=
    quittingFiniteBoundaryHolonomy_coordinates_bounded
      reward roots start extra who
  have hmass : 0 ≤ summary.absorptionMass :=
    sub_nonneg.mpr hsurvival_le
  have hweighted :=
    abs_quittingFiniteBoundaryHolonomy_prescribed_intercept_le
      reward roots start extra who
  rw [QuittingAffineSummary.targetResidual_eq]
  calc
    |summary.intercept - summary.absorptionMass * target|
        ≤ |summary.intercept| + |summary.absorptionMass * target| :=
      abs_sub _ _
    _ = |summary.intercept| + summary.absorptionMass * |target| := by
      rw [abs_mul, abs_of_nonneg hmass]
    _ ≤ quittingRewardBound reward * summary.absorptionMass +
          summary.absorptionMass * |target| :=
      add_le_add hweighted le_rfl
    _ = (quittingRewardBound reward + |target|) *
          summary.absorptionMass := by ring

/-- Every realized unilateral tail residual is first-order in opponent-only
absorbed mass. -/
theorem abs_quittingFiniteBoundaryHolonomy_bestResponse_tailResidual_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι)
    (target : ℝ) :
    |(QuittingBoundaryHolonomy.bestResponse
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).tailResidual target| ≤
      (quittingRewardBound reward + |target|) *
        (QuittingBoundaryHolonomy.bestResponse
          (quittingFiniteBoundaryHolonomy reward roots start extra) who).absorptionMass := by
  let summary := QuittingBoundaryHolonomy.bestResponse
    (quittingFiniteBoundaryHolonomy reward roots start extra) who
  change |summary.tailResidual target| ≤
    (quittingRewardBound reward + |target|) * summary.absorptionMass
  obtain ⟨_, _, _, _, hsurvival_le⟩ :=
    quittingFiniteBoundaryHolonomy_coordinates_bounded
      reward roots start extra who
  have hmass : 0 ≤ summary.absorptionMass :=
    sub_nonneg.mpr hsurvival_le
  have hweighted :=
    abs_quittingFiniteBoundaryHolonomy_bestResponse_tail_le
      reward roots start extra who
  unfold QuittingMaxAffineSummary.tailResidual
  calc
    |summary.tail - summary.absorptionMass * target|
        ≤ |summary.tail| + |summary.absorptionMass * target| :=
      abs_sub _ _
    _ = |summary.tail| + summary.absorptionMass * |target| := by
      rw [abs_mul, abs_of_nonneg hmass]
    _ ≤ quittingRewardBound reward * summary.absorptionMass +
          summary.absorptionMass * |target| :=
      add_le_add hweighted le_rfl
    _ = (quittingRewardBound reward + |target|) *
          summary.absorptionMass := by ring

/-- The normalized prescribed residual is uniformly bounded by reward scale
plus the absolute target. -/
theorem abs_quittingFiniteBoundaryHolonomy_prescribed_normalizedTargetResidual_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι)
    (target : ℝ)
    (hsurvival :
      (QuittingBoundaryHolonomy.prescribed
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).survival ≠ 1) :
    |(QuittingBoundaryHolonomy.prescribed
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).normalizedTargetResidual target| ≤
      quittingRewardBound reward + |target| := by
  let summary := QuittingBoundaryHolonomy.prescribed
    (quittingFiniteBoundaryHolonomy reward roots start extra) who
  rw [QuittingAffineSummary.normalizedTargetResidual_eq_fixedPoint_sub
    summary target hsurvival]
  have hfixed :=
    abs_quittingFiniteBoundaryHolonomy_prescribed_fixedPoint_le
      reward roots start extra who hsurvival
  exact (abs_sub _ _).trans (add_le_add hfixed le_rfl)

/-- The normalized unilateral tail residual obeys the same compact bound. -/
theorem abs_quittingFiniteBoundaryHolonomy_bestResponse_normalizedTailResidual_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι)
    (target : ℝ)
    (hsurvival :
      (QuittingBoundaryHolonomy.bestResponse
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).survival ≠ 1) :
    |(QuittingBoundaryHolonomy.bestResponse
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).normalizedTailResidual target| ≤
      quittingRewardBound reward + |target| := by
  let summary := QuittingBoundaryHolonomy.bestResponse
    (quittingFiniteBoundaryHolonomy reward roots start extra) who
  rw [QuittingMaxAffineSummary.normalizedTailResidual_eq_tailAnchor_sub
    summary target hsurvival]
  have hanchor :=
    abs_quittingFiniteBoundaryHolonomy_bestResponse_tailAnchor_le
      reward roots start extra who hsurvival
  exact (abs_sub _ _).trans (add_le_add hanchor le_rfl)

end GameTheory
