/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityTangentCompactness
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Order.Real

/-!
# Extended scaled early-obstacle excess

The early stopping floor need not differ from the target at the same finite
scale as tail absorption.  Dividing its positive excess by absorption mass in
`ℝ≥0∞` records all regimes without an unjustified boundedness assumption:

* zero is exactly target safety;
* a finite positive value is a scaled violation; and
* infinity records a positive obstacle on the neutral face.

Because `ℝ≥0∞` is compact, adjoining this coordinate preserves subsequential
compactness.  This is an obstruction compactification; it deliberately forgets
negative early drift, which is irrelevant to the safety inequality.
-/

noncomputable section

open Filter

namespace GameTheory
namespace QuittingMaxAffineSummary

/-- Positive part of the early stopping excess over a target. -/
def positiveEarlyExcess
    (summary : QuittingMaxAffineSummary) (target : ℝ) : ℝ :=
  max 0 (summary.early - target)

/-- Positive early excess measured per unit tail absorption mass, with infinity
allowed. -/
def scaledPositiveEarlyExcess
    (summary : QuittingMaxAffineSummary) (target : ℝ) : ℝ≥0∞ :=
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
  unfold positiveEarlyExcess
  rw [max_eq_left_iff]
  linarith

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
      by simpa [hmass_zero]⟩

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
  QuittingBoundaryTangentCoreCoordinates ι × (ι → ℝ≥0∞)

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
