/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityMaxAffine

/-!
# Nonempty repetition of max-affine stopping holonomy

A max-affine identity would require an infinite early floor, so finite stopping
summaries do not form a monoid.  This file therefore iterates one or more
copies.  Tail residuals amplify geometrically, while target safety is preserved
under every finite nonempty repetition.
-/

noncomputable section

namespace GameTheory
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
