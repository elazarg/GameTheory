/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Holonomy.SelfSimilarity
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Holonomy.Tangent
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Holonomy.WeightedBounds
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Order.Real

/-!
# Realized tangent bounds and projected compactness for quitting holonomy

Weighted intercept estimates for actual blocks imply compact conditional
anchors and residuals which are uniformly first-order in absorbed mass. The
compactness results retain coordinate projections only; they do not decode a
strategically repeatable limiting block.
-/

noncomputable section

open Filter

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
  · simpa [summary, QuittingAffineSummary.absorptionMass] using hweighted

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
  · simpa [summary, QuittingMaxAffineSummary.absorptionMass] using hweighted

/-- The prescribed conditional anchor is bounded for every realized block.
At the neutral face Lean's totalized division makes the anchor zero; away from
that face the weighted-intercept theorem gives the substantive bound. -/
theorem abs_quittingFiniteBoundaryHolonomy_prescribed_fixedPoint_le_all
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι) :
    |(QuittingBoundaryHolonomy.prescribed
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).fixedPoint| ≤
      quittingRewardBound reward := by
  by_cases hsurvival :
      (QuittingBoundaryHolonomy.prescribed
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).survival = 1
  · simpa [QuittingAffineSummary.fixedPoint, hsurvival] using
      quittingRewardBound_nonneg reward
  · exact abs_quittingFiniteBoundaryHolonomy_prescribed_fixedPoint_le
      reward roots start extra who hsurvival

/-- The unilateral conditional tail anchor is likewise bounded on every
realized block, with the neutral value canonically zero. -/
theorem abs_quittingFiniteBoundaryHolonomy_bestResponse_tailAnchor_le_all
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι) :
    |(QuittingBoundaryHolonomy.bestResponse
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).tailAnchor| ≤
      quittingRewardBound reward := by
  by_cases hsurvival :
      (QuittingBoundaryHolonomy.bestResponse
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).survival = 1
  · simpa [QuittingMaxAffineSummary.tailAnchor,
      QuittingMaxAffineSummary.absorptionMass, hsurvival] using
        quittingRewardBound_nonneg reward
  · exact abs_quittingFiniteBoundaryHolonomy_bestResponse_tailAnchor_le
      reward roots start extra who hsurvival

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
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).normalizedTargetResidual
      target| ≤
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
        (quittingFiniteBoundaryHolonomy reward roots start extra) who).normalizedTailResidual
      target| ≤
      quittingRewardBound reward + |target| := by
  let summary := QuittingBoundaryHolonomy.bestResponse
    (quittingFiniteBoundaryHolonomy reward roots start extra) who
  rw [QuittingMaxAffineSummary.normalizedTailResidual_eq_tailAnchor_sub
    summary target hsurvival]
  have hanchor :=
    abs_quittingFiniteBoundaryHolonomy_bestResponse_tailAnchor_le
      reward roots start extra who hsurvival
  exact (abs_sub _ _).trans (add_le_add hanchor le_rfl)



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
  · simpa [summary, QuittingAffineSummary.absorptionMass] using hweighted
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
  · simpa [summary, QuittingMaxAffineSummary.absorptionMass] using hweighted
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



open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Playerwise tangent-core coordinates:

* prescribed absorption mass and conditional anchor;
* unilateral early floor, tail absorption mass, and conditional tail anchor.
-/
abbrev QuittingBoundaryTangentCoreCoordinates (ι : Type) :=
  (ι → ℝ × ℝ) × (ι → ℝ × (ℝ × ℝ))

/-- Forget a complete holonomy to its bounded tangent core. -/
def QuittingBoundaryHolonomy.tangentCoreCoordinates
    (holonomy : QuittingBoundaryHolonomy ι) :
    QuittingBoundaryTangentCoreCoordinates ι :=
  (fun who =>
    ((holonomy.prescribed who).absorptionMass,
      (holonomy.prescribed who).fixedPoint),
   fun who =>
    ((holonomy.bestResponse who).early,
      ((holonomy.bestResponse who).absorptionMass,
        (holonomy.bestResponse who).tailAnchor)))

/-- Compact box for the tangent core at terminal reward bound `M`. -/
def quittingBoundaryTangentCoreBox (ι : Type) (M : ℝ) :
    Set (QuittingBoundaryTangentCoreCoordinates ι) :=
  (Set.univ.pi (fun _ => Set.Icc 0 1 ×ˢ Set.Icc (-M) M)) ×ˢ
    (Set.univ.pi (fun _ =>
      Set.Icc (-M) M ×ˢ (Set.Icc 0 1 ×ˢ Set.Icc (-M) M)))

/-- The tangent-core box is compact. -/
theorem isCompact_quittingBoundaryTangentCoreBox
    (ι : Type) (M : ℝ) :
    IsCompact (quittingBoundaryTangentCoreBox ι M) := by
  simpa [quittingBoundaryTangentCoreBox] using
    (isCompact_Icc : IsCompact
      (Set.Icc
        ((fun _ : ι => ((0 : ℝ), -M)),
          fun _ : ι => (-M, ((0 : ℝ), -M)))
        ((fun _ : ι => ((1 : ℝ), M)),
          fun _ : ι => (M, ((1 : ℝ), M)))))

/-- Every actual finite block belongs to the common tangent-core box. -/
theorem quittingFiniteBoundaryHolonomy_tangentCoreCoordinates_mem_box
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) :
    (quittingFiniteBoundaryHolonomy reward roots start extra).tangentCoreCoordinates ∈
      quittingBoundaryTangentCoreBox ι (quittingRewardBound reward) := by
  refine ⟨?_, ?_⟩
  · intro who _
    let summary := QuittingBoundaryHolonomy.prescribed
      (quittingFiniteBoundaryHolonomy reward roots start extra) who
    obtain ⟨_, hsurvival_le, _, _, _⟩ :=
      quittingFiniteBoundaryHolonomy_coordinates_bounded
        reward roots start extra who
    have hmass : summary.absorptionMass ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact sub_nonneg.mpr hsurvival_le
      · unfold QuittingAffineSummary.absorptionMass
        linarith [summary.survival_nonneg]
    have hanchor :=
      abs_quittingFiniteBoundaryHolonomy_prescribed_fixedPoint_le_all
        reward roots start extra who
    exact ⟨hmass, abs_le.mp hanchor⟩
  · intro who _
    let summary := QuittingBoundaryHolonomy.bestResponse
      (quittingFiniteBoundaryHolonomy reward roots start extra) who
    obtain ⟨_, _, hearly, _, hsurvival_le⟩ :=
      quittingFiniteBoundaryHolonomy_coordinates_bounded
        reward roots start extra who
    have hmass : summary.absorptionMass ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact sub_nonneg.mpr hsurvival_le
      · unfold QuittingMaxAffineSummary.absorptionMass
        linarith [summary.survival_nonneg]
    have hanchor :=
      abs_quittingFiniteBoundaryHolonomy_bestResponse_tailAnchor_le_all
        reward roots start extra who
    exact ⟨abs_le.mp hearly, ⟨hmass, abs_le.mp hanchor⟩⟩

/-- Every sequence of actual finite blocks admits a subsequence whose bounded
tangent-core coordinates converge. No source-path, obstacle, mark, debt, or
splice closedness is asserted. -/
theorem exists_tendsto_subseq_quittingFiniteBoundaryTangentCoreCoordinates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ℕ → ι → PMF Bool)
    (start extra : ℕ → ℕ) :
    ∃ limit ∈ quittingBoundaryTangentCoreBox ι (quittingRewardBound reward),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto
          (fun n =>
            (quittingFiniteBoundaryHolonomy reward (roots (φ n))
              (start (φ n)) (extra (φ n))).tangentCoreCoordinates)
          atTop (nhds limit) := by
  let K := quittingBoundaryTangentCoreBox ι (quittingRewardBound reward)
  let sequence : ℕ → QuittingBoundaryTangentCoreCoordinates ι := fun n =>
    (quittingFiniteBoundaryHolonomy reward (roots n)
      (start n) (extra n)).tangentCoreCoordinates
  have hcompact : IsCompact K :=
    isCompact_quittingBoundaryTangentCoreBox ι (quittingRewardBound reward)
  have hmem : ∀ n, sequence n ∈ K := by
    intro n
    exact quittingFiniteBoundaryHolonomy_tangentCoreCoordinates_mem_box
      reward (roots n) (start n) (extra n)
  obtain ⟨limit, hlimit, φ, hφ, htendsto⟩ :=
    hcompact.tendsto_subseq hmem
  exact ⟨limit, hlimit, φ, hφ, htendsto⟩


namespace QuittingMaxAffineSummary

/-- Positive part of the early stopping excess over a target. -/
def positiveEarlyExcess
    (summary : QuittingMaxAffineSummary) (target : ℝ) : ℝ :=
  max 0 (summary.early - target)

/-- Positive early excess measured per unit tail absorption mass, with infinity
allowed. -/
def scaledPositiveEarlyExcess
    (summary : QuittingMaxAffineSummary) (target : ℝ) : ENNReal :=
  ENNReal.ofReal (summary.positiveEarlyExcess target) /
    ENNReal.ofReal summary.absorptionMass

@[simp] theorem positiveEarlyExcess_nonneg
    (summary : QuittingMaxAffineSummary) (target : ℝ) :
    0 ≤ summary.positiveEarlyExcess target := by
  exact le_max_left _ _

/-- Positive early excess vanishes exactly when the early stopping floor is
safe at the target. -/
@[simp] theorem positiveEarlyExcess_eq_zero_iff
    (summary : QuittingMaxAffineSummary) (target : ℝ) :
    summary.positiveEarlyExcess target = 0 ↔ summary.early ≤ target := by
  simp [positiveEarlyExcess]

/-- Positive early excess is strictly positive exactly when the early floor
strictly exceeds the target. -/
theorem positiveEarlyExcess_pos_iff
    (summary : QuittingMaxAffineSummary) (target : ℝ) :
    0 < summary.positiveEarlyExcess target ↔ target < summary.early := by
  constructor
  · intro h
    by_contra hnot
    have hle : summary.early - target ≤ 0 := by linarith
    rw [positiveEarlyExcess, max_eq_left hle] at h
    exact lt_irrefl 0 h
  · intro h
    have hdiff : 0 < summary.early - target := by linarith
    exact hdiff.trans_le (le_max_right _ _)

/-- The extended scaled coordinate is zero exactly when the early obstacle is
safe.  This remains true at zero absorption mass. -/
@[simp] theorem scaledPositiveEarlyExcess_eq_zero_iff
    (summary : QuittingMaxAffineSummary) (target : ℝ) :
    summary.scaledPositiveEarlyExcess target = 0 ↔
      summary.early ≤ target := by
  unfold scaledPositiveEarlyExcess
  rw [ENNReal.div_eq_zero_iff]
  simp only [ENNReal.ofReal_ne_top, or_false, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have hzero : summary.positiveEarlyExcess target = 0 :=
      le_antisymm h (summary.positiveEarlyExcess_nonneg target)
    exact (summary.positiveEarlyExcess_eq_zero_iff target).mp hzero
  · intro h
    have hzero := (summary.positiveEarlyExcess_eq_zero_iff target).mpr h
    rw [hzero]

/-- At nonnegative absorption mass, infinity occurs exactly for an unsafe
neutral obstacle. -/
theorem scaledPositiveEarlyExcess_eq_top_iff
    (summary : QuittingMaxAffineSummary) (target : ℝ)
    (hmass : 0 ≤ summary.absorptionMass) :
    summary.scaledPositiveEarlyExcess target = ⊤ ↔
      summary.absorptionMass = 0 ∧ target < summary.early := by
  unfold scaledPositiveEarlyExcess
  rw [ENNReal.div_eq_top]
  simp only [ENNReal.ofReal_ne_top, false_and, or_false,
    ENNReal.ofReal_ne_zero_iff, ENNReal.ofReal_eq_zero]
  constructor
  · rintro ⟨hearly, hmass_nonpos⟩
    exact ⟨le_antisymm hmass_nonpos hmass,
      (summary.positiveEarlyExcess_pos_iff target).mp hearly⟩
  · rintro ⟨hmass_zero, hearly⟩
    exact ⟨(summary.positiveEarlyExcess_pos_iff target).mpr hearly,
      by simp [hmass_zero]⟩

/-- Positive absorption mass makes the scaled early excess finite. -/
theorem scaledPositiveEarlyExcess_ne_top_of_absorptionMass_pos
    (summary : QuittingMaxAffineSummary) (target : ℝ)
    (hmass : 0 < summary.absorptionMass) :
    summary.scaledPositiveEarlyExcess target ≠ ⊤ := by
  unfold scaledPositiveEarlyExcess
  exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
    (by simpa [ENNReal.ofReal_ne_zero_iff] using hmass)

end QuittingMaxAffineSummary

/-- Tangent core augmented by the complete extended positive early-obstacle
scale. -/
abbrev QuittingBoundaryExtendedTangentCoordinates (ι : Type) :=
  QuittingBoundaryTangentCoreCoordinates ι × (ι → ENNReal)

/-- Target-dependent extended tangent coordinates of a complete holonomy. -/
def QuittingBoundaryHolonomy.extendedTangentCoordinates
    (holonomy : QuittingBoundaryHolonomy ι) (target : Payoff ι) :
    QuittingBoundaryExtendedTangentCoordinates ι :=
  (holonomy.tangentCoreCoordinates,
    fun who =>
      (holonomy.bestResponse who).scaledPositiveEarlyExcess (target who))

/-- Compact target-dependent extended tangent box.  The early-obstacle
coordinate is unrestricted in `ℝ≥0∞`; infinity is an intended boundary point. -/
def quittingBoundaryExtendedTangentBox
    (ι : Type) (M : ℝ) :
    Set (QuittingBoundaryExtendedTangentCoordinates ι) :=
  quittingBoundaryTangentCoreBox ι M ×ˢ Set.univ

/-- The extended tangent box is compact. -/
theorem isCompact_quittingBoundaryExtendedTangentBox
    (ι : Type) (M : ℝ) :
    IsCompact (quittingBoundaryExtendedTangentBox ι M) := by
  exact (isCompact_quittingBoundaryTangentCoreBox ι M).prod isCompact_univ

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every actual finite block belongs to the extended tangent box for every
supplied target. -/
theorem quittingFiniteBoundaryHolonomy_extendedTangentCoordinates_mem_box
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ)
    (target : Payoff ι) :
    (quittingFiniteBoundaryHolonomy reward roots start extra).extendedTangentCoordinates
        target ∈
      quittingBoundaryExtendedTangentBox ι (quittingRewardBound reward) := by
  exact ⟨quittingFiniteBoundaryHolonomy_tangentCoreCoordinates_mem_box
    reward roots start extra, Set.mem_univ _⟩

/-- Every sequence of actual blocks has a subsequence whose extended tangent
coordinates converge.  Diverging scaled early obstacles converge to infinity
rather than destroying compactness. -/
theorem exists_tendsto_subseq_quittingFiniteBoundaryExtendedTangentCoordinates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ℕ → ι → PMF Bool)
    (start extra : ℕ → ℕ) (target : Payoff ι) :
    ∃ limit ∈
        quittingBoundaryExtendedTangentBox ι (quittingRewardBound reward),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto
          (fun n =>
            (quittingFiniteBoundaryHolonomy reward (roots (φ n))
              (start (φ n)) (extra (φ n))).extendedTangentCoordinates target)
          atTop (nhds limit) := by
  let K := quittingBoundaryExtendedTangentBox ι (quittingRewardBound reward)
  let sequence : ℕ → QuittingBoundaryExtendedTangentCoordinates ι := fun n =>
    (quittingFiniteBoundaryHolonomy reward (roots n)
      (start n) (extra n)).extendedTangentCoordinates target
  have hcompact : IsCompact K :=
    isCompact_quittingBoundaryExtendedTangentBox ι (quittingRewardBound reward)
  have hmem : ∀ n, sequence n ∈ K := by
    intro n
    exact quittingFiniteBoundaryHolonomy_extendedTangentCoordinates_mem_box
      reward (roots n) (start n) (extra n) target
  obtain ⟨limit, hlimit, φ, hφ, htendsto⟩ :=
    hcompact.tendsto_subseq hmem
  exact ⟨limit, hlimit, φ, hφ, htendsto⟩


end GameTheory
