/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Holonomy.AffineResidual

/-!
# Max-affine residual algebra for unilateral stopping

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
  unfold tailResidual absorptionMass
  by_cases h :
      outer.early ≤ outer.tail + outer.survival * inner.eval target
  · change max outer.early (outer.tail + outer.survival * inner.eval target) - target = _
    rw [max_eq_right h]
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
    change max outer.early (outer.tail + outer.survival * inner.eval target) - target = _
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
  simpa [add_comm] using
    add_le_add_left
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
  change summary.tail - (1 - summary.survival) * target =
    (1 - summary.survival) * (summary.tail / (1 - summary.survival) - target)
  field_simp [hmass]

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


namespace QuittingMaxAffineSummary

/-- `extra + 1` chronological copies of one max-affine summary. -/
def selfComposeNonempty
    (summary : QuittingMaxAffineSummary) : ℕ → QuittingMaxAffineSummary
  | 0 => summary
  | extra + 1 => summary * summary.selfComposeNonempty extra

@[simp] theorem selfComposeNonempty_zero
    (summary : QuittingMaxAffineSummary) :
    summary.selfComposeNonempty 0 = summary := rfl

@[simp] theorem selfComposeNonempty_succ
    (summary : QuittingMaxAffineSummary) (extra : ℕ) :
    summary.selfComposeNonempty (extra + 1) =
      summary * summary.selfComposeNonempty extra := rfl

/-- Total target excess under repetition obeys the same max-plus recurrence as
one Bellman step: the one-block early residual competes with one-block tail
residual plus the surviving repeated excess. -/
theorem targetExcess_selfComposeNonempty_succ
    (summary : QuittingMaxAffineSummary) (target : ℝ) (extra : ℕ) :
    (summary.selfComposeNonempty (extra + 1)).targetExcess target =
      max (summary.early - target)
        (summary.tailResidual target + summary.survival *
          (summary.selfComposeNonempty extra).targetExcess target) := by
  rw [selfComposeNonempty_succ, targetExcess_mul]

/-- Tail residual after `extra + 1` copies is the geometric amplifier times
the one-block tail residual. -/
theorem tailResidual_selfComposeNonempty
    (summary : QuittingMaxAffineSummary) (target : ℝ) (extra : ℕ) :
    (summary.selfComposeNonempty extra).tailResidual target =
      QuittingAffineSummary.geometricAmplifier summary.survival (extra + 1) *
        summary.tailResidual target := by
  induction extra with
  | zero =>
      simp [QuittingAffineSummary.geometricAmplifier]
  | succ extra ih =>
      rw [selfComposeNonempty_succ, tailResidual_mul, ih,
        QuittingAffineSummary.geometricAmplifier_succ]
      have hgeom :
          QuittingAffineSummary.geometricAmplifier summary.survival (2 + extra) =
            1 + summary.survival *
              (1 + summary.survival *
                QuittingAffineSummary.geometricAmplifier summary.survival extra) := by
        rw [show 2 + extra = (extra + 1) + 1 by omega,
          QuittingAffineSummary.geometricAmplifier_succ,
          QuittingAffineSummary.geometricAmplifier_succ]
      rw [show extra + 1 + 1 = 2 + extra by omega, hgeom]
      ring

/-- On the neutral tail face, tail residual grows linearly with the number of
copies. -/
theorem tailResidual_selfComposeNonempty_of_survival_eq_one
    (summary : QuittingMaxAffineSummary) (target : ℝ) (extra : ℕ)
    (hsurvival : summary.survival = 1) :
    (summary.selfComposeNonempty extra).tailResidual target =
      ((extra + 1 : ℕ) : ℝ) * summary.tailResidual target := by
  rw [tailResidual_selfComposeNonempty, hsurvival,
    QuittingAffineSummary.geometricAmplifier_one]

/-- A positive neutral tail residual defeats every finite tail-residual budget
under sufficiently many nonempty repetitions. -/
theorem exists_tailResidual_selfComposeNonempty_gt_of_survival_eq_one
    (summary : QuittingMaxAffineSummary) (target budget : ℝ)
    (hsurvival : summary.survival = 1)
    (hpositive : 0 < summary.tailResidual target) :
    ∃ extra : ℕ,
      budget < (summary.selfComposeNonempty extra).tailResidual target := by
  obtain ⟨copies, hcopies⟩ := exists_nat_gt
    (budget / summary.tailResidual target)
  refine ⟨copies, ?_⟩
  rw [tailResidual_selfComposeNonempty_of_survival_eq_one
    summary target copies hsurvival]
  have hcopy_le : (copies : ℝ) ≤ ((copies + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ copies
  have hbudget : budget < (copies : ℝ) * summary.tailResidual target :=
    (div_lt_iff₀ hpositive).mp hcopies
  exact hbudget.trans_le
    (mul_le_mul_of_nonneg_right hcopy_le hpositive.le)

/-- Target safety is preserved under every finite nonempty repetition. -/
theorem eval_selfComposeNonempty_le_target
    (summary : QuittingMaxAffineSummary) (target : ℝ)
    (hsafe : summary.eval target ≤ target) :
    ∀ extra,
      (summary.selfComposeNonempty extra).eval target ≤ target := by
  intro extra
  induction extra with
  | zero => exact hsafe
  | succ extra ih =>
      rw [selfComposeNonempty_succ, eval_mul]
      exact (summary.eval_mono ih).trans hsafe

/-- An idempotent summary has the same target-safety test after every nonempty
repetition. -/
theorem eval_selfComposeNonempty_le_target_iff_of_idempotent
    (summary : QuittingMaxAffineSummary) (target : ℝ)
    (hidempotent : summary * summary = summary) (extra : ℕ) :
    (summary.selfComposeNonempty extra).eval target ≤ target ↔
      summary.eval target ≤ target := by
  have hpower : summary.selfComposeNonempty extra = summary := by
    induction extra with
    | zero => rfl
    | succ extra ih =>
        rw [selfComposeNonempty_succ, ih, hidempotent]
  rw [hpower]

end QuittingMaxAffineSummary

end GameTheory
