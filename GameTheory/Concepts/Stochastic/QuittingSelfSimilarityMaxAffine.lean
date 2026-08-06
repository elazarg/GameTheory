/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityAffineIteration

/-!
# Max-affine self-similarity algebra for unilateral stopping

A player's unilateral stopping value over a finite quitting block is
max-affine. This module identifies the two target-safety halfspaces, the
absorbed-mass-normalized tail anchor, the max-plus composition law for total
excess, monotonicity, and all coefficient idempotents.
-/

noncomputable section

namespace GameTheory

namespace QuittingMaxAffineSummary

/-- Defect of the tail survival slope. -/
def absorptionMass (summary : QuittingMaxAffineSummary) : ℝ :=
  1 - summary.survival

/-- Tail branch residual at a supplied target. -/
def tailResidual
    (summary : QuittingMaxAffineSummary) (target : ℝ) : ℝ :=
  summary.tail - summary.absorptionMass * target

/-- Total best-response excess at a supplied target. -/
def targetExcess
    (summary : QuittingMaxAffineSummary) (target : ℝ) : ℝ :=
  summary.eval target - target

/-- Tail fixed point away from the neutral face. -/
def tailAnchor (summary : QuittingMaxAffineSummary) : ℝ :=
  summary.tail / summary.absorptionMass

/-- Tail residual per unit tail absorption mass. -/
def normalizedTailResidual
    (summary : QuittingMaxAffineSummary) (target : ℝ) : ℝ :=
  summary.tailResidual target / summary.absorptionMass

/-- Tail absorption mass obeys the same survival-weighted composition law as
prescribed absorption mass. -/
@[simp] theorem absorptionMass_mul
    (outer inner : QuittingMaxAffineSummary) :
    (outer * inner).absorptionMass =
      outer.absorptionMass + outer.survival * inner.absorptionMass := by
  change 1 - outer.survival * inner.survival =
    (1 - outer.survival) + outer.survival * (1 - inner.survival)
  ring

/-- Tail residuals form an exact cocycle under chronological composition. -/
theorem tailResidual_mul
    (outer inner : QuittingMaxAffineSummary) (target : ℝ) :
    (outer * inner).tailResidual target =
      outer.tailResidual target +
        outer.survival * inner.tailResidual target := by
  unfold tailResidual absorptionMass
  change
    (outer.tail + outer.survival * inner.tail) -
        (1 - outer.survival * inner.survival) * target = _
  ring

/-- The normalized tail residual of a composite is the transported
absorption-mass-weighted average of the two normalized tail residuals. -/
theorem normalizedTailResidual_mul
    (outer inner : QuittingMaxAffineSummary) (target : ℝ)
    (houter : outer.absorptionMass ≠ 0)
    (hinner : inner.absorptionMass ≠ 0)
    (hcompose : (outer * inner).absorptionMass ≠ 0) :
    (outer * inner).normalizedTailResidual target =
      (outer.absorptionMass * outer.normalizedTailResidual target +
        outer.survival * inner.absorptionMass *
          inner.normalizedTailResidual target) /
        (outer.absorptionMass + outer.survival * inner.absorptionMass) := by
  have hcompose' :
      outer.absorptionMass + outer.survival * inner.absorptionMass ≠ 0 := by
    simpa only [absorptionMass_mul] using hcompose
  unfold normalizedTailResidual
  rw [tailResidual_mul, absorptionMass_mul]
  field_simp [houter, hinner, hcompose']
  ring

/-- Target excess is the maximum of early and tail residuals. -/
theorem targetExcess_eq_max
    (summary : QuittingMaxAffineSummary) (target : ℝ) :
    summary.targetExcess target =
      max (summary.early - target) (summary.tailResidual target) := by
  unfold targetExcess eval tailResidual absorptionMass
  by_cases h : summary.early ≤ summary.tail + summary.survival * target
  · rw [max_eq_right h]
    have h' : summary.early - target ≤
        summary.tail - (1 - summary.survival) * target := by
      linarith
    rw [max_eq_right h']
    ring
  · have hle : summary.tail + summary.survival * target ≤ summary.early :=
      le_of_not_ge h
    rw [max_eq_left hle]
    have h' : summary.tail - (1 - summary.survival) * target ≤
        summary.early - target := by
      linarith
    rw [max_eq_left h']

/-- Total excess composes by a max-plus Bellman recurrence: the outer early
obstacle competes with its tail residual plus the inner excess transported by
outer survival. -/
theorem targetExcess_mul
    (outer inner : QuittingMaxAffineSummary) (target : ℝ) :
    (outer * inner).targetExcess target =
      max (outer.early - target)
        (outer.tailResidual target +
          outer.survival * inner.targetExcess target) := by
  unfold targetExcess
  rw [eval_mul]
  unfold eval tailResidual absorptionMass
  by_cases h :
      outer.early ≤ outer.tail + outer.survival * inner.eval target
  · rw [max_eq_right h]
    have h' : outer.early - target ≤
        (outer.tail - (1 - outer.survival) * target) +
          outer.survival * (inner.eval target - target) := by
      calc
        outer.early - target ≤
            (outer.tail + outer.survival * inner.eval target) - target :=
          sub_le_sub_right h target
        _ = (outer.tail - (1 - outer.survival) * target) +
              outer.survival * (inner.eval target - target) := by ring
    rw [max_eq_right h']
    ring
  · have hle :
        outer.tail + outer.survival * inner.eval target ≤ outer.early :=
      le_of_not_ge h
    rw [max_eq_left hle]
    have h' :
        (outer.tail - (1 - outer.survival) * target) +
            outer.survival * (inner.eval target - target) ≤
          outer.early - target := by
      calc
        (outer.tail - (1 - outer.survival) * target) +
              outer.survival * (inner.eval target - target) =
            (outer.tail + outer.survival * inner.eval target) - target := by
          ring
        _ ≤ outer.early - target := sub_le_sub_right hle target
    rw [max_eq_left h']

/-- Strategic safety at one target is exactly two scalar halfspaces. -/
theorem eval_le_target_iff
    (summary : QuittingMaxAffineSummary) (target : ℝ) :
    summary.eval target ≤ target ↔
      summary.early ≤ target ∧
        summary.tail ≤ summary.absorptionMass * target := by
  unfold eval absorptionMass
  rw [max_le_iff]
  constructor
  · rintro ⟨hearly, htail⟩
    exact ⟨hearly, by linarith⟩
  · rintro ⟨hearly, htail⟩
    exact ⟨hearly, by linarith⟩

/-- A max-affine summary is monotone because its survival slope is
nonnegative. -/
theorem eval_mono (summary : QuittingMaxAffineSummary) :
    Monotone summary.eval := by
  intro x y hxy
  unfold eval
  apply max_le_max le_rfl
  exact add_le_add_left
    (mul_le_mul_of_nonneg_left hxy summary.survival_nonneg)
    summary.tail

/-- Tail residual is tail absorption mass times tail-anchor error. -/
theorem tailResidual_eq_absorptionMass_mul_tailAnchor_sub
    (summary : QuittingMaxAffineSummary) (target : ℝ)
    (hsurvival : summary.survival ≠ 1) :
    summary.tailResidual target =
      summary.absorptionMass * (summary.tailAnchor - target) := by
  have hmass : 1 - summary.survival ≠ 0 :=
    sub_ne_zero.mpr hsurvival.symm
  unfold tailResidual absorptionMass tailAnchor
  field_simp [hmass]
  ring

/-- Normalized tail residual is exactly tail-anchor displacement. -/
theorem normalizedTailResidual_eq_tailAnchor_sub
    (summary : QuittingMaxAffineSummary) (target : ℝ)
    (hsurvival : summary.survival ≠ 1) :
    summary.normalizedTailResidual target =
      summary.tailAnchor - target := by
  have hmass : summary.absorptionMass ≠ 0 := by
    unfold absorptionMass
    exact sub_ne_zero.mpr hsurvival.symm
  unfold normalizedTailResidual
  rw [div_eq_iff hmass]
  simpa [mul_comm] using
    summary.tailResidual_eq_absorptionMass_mul_tailAnchor_sub
      target hsurvival

/-- Coefficient-semigroup idempotents are exactly canonical constant summaries
or threshold-closure summaries. -/
theorem mul_self_eq_self_iff (summary : QuittingMaxAffineSummary) :
    summary * summary = summary ↔
      (summary.survival = 0 ∧ summary.tail ≤ summary.early) ∨
        (summary.survival = 1 ∧ summary.tail = 0) := by
  constructor
  · intro h
    have hs : summary.survival * summary.survival = summary.survival := by
      simpa [mul_eq_compose, compose] using
        congrArg QuittingMaxAffineSummary.survival h
    have ht : summary.tail + summary.survival * summary.tail =
        summary.tail := by
      simpa [mul_eq_compose, compose] using
        congrArg QuittingMaxAffineSummary.tail h
    have he : max summary.early
          (summary.tail + summary.survival * summary.early) =
        summary.early := by
      simpa [mul_eq_compose, compose] using
        congrArg QuittingMaxAffineSummary.early h
    have hfactor : summary.survival * (summary.survival - 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hzero | hone
    · left
      refine ⟨hzero, ?_⟩
      rw [hzero, zero_mul, add_zero] at he
      exact (max_eq_left_iff.mp he)
    · right
      have hsone : summary.survival = 1 := by linarith
      refine ⟨hsone, ?_⟩
      rw [hsone] at ht
      linarith
  · rintro (⟨hzero, htail⟩ | ⟨hone, htail⟩)
    · ext <;> simp [mul_eq_compose, compose, hzero, htail]
    · ext <;> simp [mul_eq_compose, compose, hone, htail]

/-- Functional normal form of a coefficient-semigroup idempotent. -/
theorem eval_normalForm_of_mul_self_eq_self
    (summary : QuittingMaxAffineSummary)
    (hidempotent : summary * summary = summary) :
    (summary.survival = 0 ∧ summary.tail ≤ summary.early ∧
        ∀ w, summary.eval w = summary.early) ∨
      (summary.survival = 1 ∧ summary.tail = 0 ∧
        ∀ w, summary.eval w = max summary.early w) := by
  rcases (mul_self_eq_self_iff summary).mp hidempotent with
    ⟨hzero, htail⟩ | ⟨hone, htail⟩
  · left
    refine ⟨hzero, htail, ?_⟩
    intro w
    simp [eval, hzero, htail]
  · right
    refine ⟨hone, htail, ?_⟩
    intro w
    simp [eval, hone, htail]

end QuittingMaxAffineSummary

end GameTheory
