/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityAffine

/-!
# Iteration and idempotents of affine quitting holonomy

Finite repetition amplifies affine residuals geometrically.  On the neutral
face the amplification is linear, yielding a precise pumping obstruction.
The coefficient-semigroup idempotents are classified completely.
-/

noncomputable section

namespace GameTheory
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
      simp [geometricAmplifier, ih, Nat.cast_succ]

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
  ring

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
