/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingBoundaryHolonomy

/-!
# Affine self-similarity residuals for quitting holonomy

The prescribed continuation map of a finite quitting block is affine.  This
module defines its absorbed-mass scale, target residual, and normalized
fixed-point displacement, and proves the exact residual cocycle under
chronological composition.
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
  simp only [targetResidual, eval_mul, eval]
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
  ring

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
  simp [hmass]

end QuittingAffineSummary
end GameTheory
