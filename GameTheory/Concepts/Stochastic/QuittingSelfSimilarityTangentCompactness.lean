/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityRealizedBounds

/-!
# Compact tangent core of realized quitting holonomy

Raw coefficients approaching the identity forget their first-order direction.
This module retains prescribed and unilateral absorption masses, their bounded
conditional anchors, and the unscaled early stopping floor.  Every actual
finite block lies in one compact finite-dimensional box, so every sequence has
a convergent tangent-core subsequence.

The scaled early obstacle is deliberately absent: existing weighted bounds do
not control it at an absorption scale.  Compactness of that missing coordinate
is a separate producer theorem.
-/

noncomputable section

open Filter

namespace GameTheory

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
tangent-core coordinates converge.  No source-path, obstacle, mark, debt, or
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

end GameTheory
