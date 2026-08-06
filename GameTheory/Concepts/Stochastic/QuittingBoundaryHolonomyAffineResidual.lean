/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingBoundaryHolonomy

/-!
# Affine residual algebra for quitting boundary holonomy

The prescribed continuation map of a finite quitting block is affine.  This
module defines its absorbed-mass scale, target residual, and normalized
fixed-point displacement, and proves the exact residual cocycle under
chronological composition. It is coefficient algebra only.
-/

noncomputable section

namespace GameTheory

namespace QuittingAffineSummary

/-- Probability defect of the continuation slope.  For an actual quitting
block this is the total prescribed absorption mass through the block. -/
def absorptionMass (summary : QuittingAffineSummary) : ℝ :=
  1 - summary.survival

/-- Failure of `target` to be fixed by the prescribed affine map. -/
def targetResidual (summary : QuittingAffineSummary) (target : ℝ) : ℝ :=
  summary.eval target - target

/-- Residual measured per unit continuation defect.  It is meaningful away
from the neutral face `survival = 1`. -/
def normalizedTargetResidual
    (summary : QuittingAffineSummary) (target : ℝ) : ℝ :=
  summary.targetResidual target / summary.absorptionMass

/-- `target` is reproduced exactly by the prescribed affine map. -/
def IsFixedAt (summary : QuittingAffineSummary) (target : ℝ) : Prop :=
  summary.eval target = target

/-- Absorption mass composes by the usual survival-weighted sum. -/
@[simp] theorem absorptionMass_mul
    (outer inner : QuittingAffineSummary) :
    (outer * inner).absorptionMass =
      outer.absorptionMass + outer.survival * inner.absorptionMass := by
  change 1 - outer.survival * inner.survival =
    (1 - outer.survival) + outer.survival * (1 - inner.survival)
  ring

/-- The target residual is the intercept minus absorbed mass times target. -/
theorem targetResidual_eq
    (summary : QuittingAffineSummary) (target : ℝ) :
    summary.targetResidual target =
      summary.intercept - summary.absorptionMass * target := by
  unfold targetResidual absorptionMass eval
  ring

/-- Affine residuals form an exact cocycle under chronological composition. -/
theorem targetResidual_mul
    (outer inner : QuittingAffineSummary) (target : ℝ) :
    (outer * inner).targetResidual target =
      outer.targetResidual target +
        outer.survival * inner.targetResidual target := by
  simp only [targetResidual, mul_eq_compose, compose, eval]
  ring

/-- Fixedness is the vanishing of the target residual. -/
theorem isFixedAt_iff_targetResidual_eq_zero
    (summary : QuittingAffineSummary) (target : ℝ) :
    summary.IsFixedAt target ↔ summary.targetResidual target = 0 := by
  unfold IsFixedAt targetResidual
  constructor <;> intro h <;> linarith

/-- Fixedness is one scalar affine equation. -/
theorem isFixedAt_iff_intercept_eq
    (summary : QuittingAffineSummary) (target : ℝ) :
    summary.IsFixedAt target ↔
      summary.intercept = summary.absorptionMass * target := by
  unfold IsFixedAt absorptionMass eval
  constructor <;> intro h <;> linarith

/-- Away from the neutral face, residual equals absorption mass times the
fixed-point error.  This is the exact blow-up identity behind the normalization
by `1 - survival`. -/
theorem targetResidual_eq_absorptionMass_mul_fixedPoint_sub
    (summary : QuittingAffineSummary) (target : ℝ)
    (hsurvival : summary.survival ≠ 1) :
    summary.targetResidual target =
      summary.absorptionMass * (summary.fixedPoint - target) := by
  have hmass : 1 - summary.survival ≠ 0 :=
    sub_ne_zero.mpr hsurvival.symm
  rw [targetResidual_eq]
  unfold absorptionMass fixedPoint
  field_simp [hmass]

/-- The normalized residual is exactly fixed-point displacement. -/
theorem normalizedTargetResidual_eq_fixedPoint_sub
    (summary : QuittingAffineSummary) (target : ℝ)
    (hsurvival : summary.survival ≠ 1) :
    summary.normalizedTargetResidual target =
      summary.fixedPoint - target := by
  have hmass : summary.absorptionMass ≠ 0 := by
    unfold absorptionMass
    exact sub_ne_zero.mpr hsurvival.symm
  unfold normalizedTargetResidual
  rw [div_eq_iff hmass]
  simpa [mul_comm] using
    summary.targetResidual_eq_absorptionMass_mul_fixedPoint_sub
      target hsurvival

/-- Away from the neutral face, fixing a target is equivalent to the unique
contracting fixed point being that target. -/
theorem isFixedAt_iff_fixedPoint_eq
    (summary : QuittingAffineSummary) (target : ℝ)
    (hsurvival : summary.survival ≠ 1) :
    summary.IsFixedAt target ↔ summary.fixedPoint = target := by
  rw [isFixedAt_iff_targetResidual_eq_zero,
    targetResidual_eq_absorptionMass_mul_fixedPoint_sub summary target hsurvival]
  have hmass : summary.absorptionMass ≠ 0 := by
    unfold absorptionMass
    exact sub_ne_zero.mpr hsurvival.symm
  rw [mul_eq_zero]
  simp [hmass, sub_eq_zero]

end QuittingAffineSummary

namespace QuittingAffineSummary

/-- Identity affine summary, used only for finite self-composition. -/
def identitySummary : QuittingAffineSummary where
  intercept := 0
  survival := 1
  survival_nonneg := zero_le_one

@[simp] theorem eval_identitySummary (w : ℝ) :
    identitySummary.eval w = w := by
  simp [identitySummary, eval]

@[simp] theorem identitySummary_mul (summary : QuittingAffineSummary) :
    identitySummary * summary = summary := by
  ext <;> simp [identitySummary, mul_eq_compose, compose]

@[simp] theorem mul_identitySummary (summary : QuittingAffineSummary) :
    summary * identitySummary = summary := by
  ext <;> simp [identitySummary, mul_eq_compose, compose]

/-- `n` chronological copies of one affine summary. -/
def selfCompose (summary : QuittingAffineSummary) : ℕ → QuittingAffineSummary
  | 0 => identitySummary
  | n + 1 => summary * summary.selfCompose n

@[simp] theorem selfCompose_zero (summary : QuittingAffineSummary) :
    summary.selfCompose 0 = identitySummary := rfl

@[simp] theorem selfCompose_succ
    (summary : QuittingAffineSummary) (n : ℕ) :
    summary.selfCompose (n + 1) = summary * summary.selfCompose n := rfl

/-- Recursive geometric amplification factor
`1 + s + ⋯ + s^(n-1)`, written without division so it is valid at `s = 1`. -/
def geometricAmplifier (s : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 + s * geometricAmplifier s n

@[simp] theorem geometricAmplifier_zero (s : ℝ) :
    geometricAmplifier s 0 = 0 := rfl

@[simp] theorem geometricAmplifier_succ (s : ℝ) (n : ℕ) :
    geometricAmplifier s (n + 1) =
      1 + s * geometricAmplifier s n := rfl

@[simp] theorem geometricAmplifier_one (n : ℕ) :
    geometricAmplifier 1 n = (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [geometricAmplifier, ih, Nat.cast_succ, add_comm]

/-- Closed geometric identity, still valid at the neutral face. -/
theorem absorptionMass_mul_geometricAmplifier
    (s : ℝ) (n : ℕ) :
    (1 - s) * geometricAmplifier s n = 1 - s ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [geometricAmplifier_succ, pow_succ]
      calc
        (1 - s) * (1 + s * geometricAmplifier s n) =
            (1 - s) + s * ((1 - s) * geometricAmplifier s n) := by ring
        _ = (1 - s) + s * (1 - s ^ n) := by rw [ih]
        _ = 1 - s ^ n * s := by ring

/-- Away from the neutral face, the recursive amplifier is the usual
geometric quotient. -/
theorem geometricAmplifier_eq_div
    (s : ℝ) (n : ℕ) (hs : s ≠ 1) :
    geometricAmplifier s n = (1 - s ^ n) / (1 - s) := by
  have hmass : 1 - s ≠ 0 := sub_ne_zero.mpr hs.symm
  rw [eq_div_iff hmass]
  simpa [mul_comm] using absorptionMass_mul_geometricAmplifier s n

/-- Repeating a block amplifies its target residual by the geometric factor. -/
theorem targetResidual_selfCompose
    (summary : QuittingAffineSummary) (target : ℝ) (n : ℕ) :
    (summary.selfCompose n).targetResidual target =
      geometricAmplifier summary.survival n *
        summary.targetResidual target := by
  induction n with
  | zero =>
      simp [selfCompose, targetResidual, identitySummary, eval,
        geometricAmplifier]
  | succ n ih =>
      rw [selfCompose_succ, targetResidual_mul, ih,
        geometricAmplifier_succ]
      ring

/-- The normalized residual of a composite is the absorption-mass-weighted
average of the normalized residuals of its two factors.  The outer survival
transports the inner mass back to the entry of the outer block. -/
theorem normalizedTargetResidual_mul
    (outer inner : QuittingAffineSummary) (target : ℝ)
    (houter : outer.absorptionMass ≠ 0)
    (hinner : inner.absorptionMass ≠ 0)
    (hcompose : (outer * inner).absorptionMass ≠ 0) :
    (outer * inner).normalizedTargetResidual target =
      (outer.absorptionMass * outer.normalizedTargetResidual target +
        outer.survival * inner.absorptionMass *
          inner.normalizedTargetResidual target) /
        (outer.absorptionMass + outer.survival * inner.absorptionMass) := by
  have hcompose' :
      outer.absorptionMass + outer.survival * inner.absorptionMass ≠ 0 := by
    simpa only [absorptionMass_mul] using hcompose
  unfold normalizedTargetResidual
  rw [targetResidual_mul, absorptionMass_mul]
  field_simp [houter, hinner, hcompose']

/-- At a neutral self-return, any nonzero residual pumps linearly. -/
theorem targetResidual_selfCompose_of_survival_eq_one
    (summary : QuittingAffineSummary) (target : ℝ) (n : ℕ)
    (hsurvival : summary.survival = 1) :
    (summary.selfCompose n).targetResidual target =
      (n : ℝ) * summary.targetResidual target := by
  rw [targetResidual_selfCompose, hsurvival, geometricAmplifier_one]

/-- A positive residual on a neutral self-return defeats every finite residual
budget after sufficiently many repetitions. -/
theorem exists_targetResidual_selfCompose_gt_of_survival_eq_one
    (summary : QuittingAffineSummary) (target budget : ℝ)
    (hsurvival : summary.survival = 1)
    (hpositive : 0 < summary.targetResidual target) :
    ∃ n : ℕ, budget < (summary.selfCompose n).targetResidual target := by
  obtain ⟨n, hn⟩ := exists_nat_gt
    (budget / summary.targetResidual target)
  refine ⟨n, ?_⟩
  rw [targetResidual_selfCompose_of_survival_eq_one
    summary target n hsurvival]
  exact (div_lt_iff₀ hpositive).mp hn

/-- Exact fixedness survives arbitrary finite repetition. -/
theorem IsFixedAt.selfCompose
    {summary : QuittingAffineSummary} {target : ℝ}
    (hfixed : summary.IsFixedAt target) (n : ℕ) :
    (summary.selfCompose n).IsFixedAt target := by
  rw [isFixedAt_iff_targetResidual_eq_zero]
  rw [targetResidual_selfCompose]
  have hzero := (isFixedAt_iff_targetResidual_eq_zero summary target).mp hfixed
  rw [hzero, mul_zero]

/-- Coefficient-semigroup idempotents are exactly constant projectors or the
identity summary. -/
theorem mul_self_eq_self_iff (summary : QuittingAffineSummary) :
    summary * summary = summary ↔
      summary.survival = 0 ∨
        (summary.survival = 1 ∧ summary.intercept = 0) := by
  constructor
  · intro h
    have hs : summary.survival * summary.survival = summary.survival := by
      simpa [mul_eq_compose, compose] using
        congrArg QuittingAffineSummary.survival h
    have hi : summary.intercept + summary.survival * summary.intercept =
        summary.intercept := by
      simpa [mul_eq_compose, compose] using
        congrArg QuittingAffineSummary.intercept h
    have hfactor : summary.survival * (summary.survival - 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hzero | hone
    · exact Or.inl hzero
    · right
      have hsone : summary.survival = 1 := by linarith
      refine ⟨hsone, ?_⟩
      rw [hsone] at hi
      linarith
  · rintro (hzero | ⟨hone, hintercept⟩)
    · ext <;> simp [mul_eq_compose, compose, hzero]
    · ext <;> simp [mul_eq_compose, compose, hone, hintercept]

/-- Functional normal form of a coefficient-semigroup idempotent. -/
theorem eval_normalForm_of_mul_self_eq_self
    (summary : QuittingAffineSummary)
    (hidempotent : summary * summary = summary) :
    (summary.survival = 0 ∧
        ∀ w, summary.eval w = summary.intercept) ∨
      (summary.survival = 1 ∧ summary.intercept = 0 ∧
        ∀ w, summary.eval w = w) := by
  rcases (mul_self_eq_self_iff summary).mp hidempotent with
    hzero | ⟨hone, hintercept⟩
  · left
    refine ⟨hzero, ?_⟩
    intro w
    simp [eval, hzero]
  · right
    refine ⟨hone, hintercept, ?_⟩
    intro w
    simp [eval, hone, hintercept]

end QuittingAffineSummary

end GameTheory
