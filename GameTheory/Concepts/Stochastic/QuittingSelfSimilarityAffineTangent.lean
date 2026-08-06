/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityAffineIteration

/-!
# Absorbed-mass tangent coordinates for affine quitting holonomy

Near survival one, raw affine coefficients collapse to the identity.  Writing
an affine block by absorbed mass and conditional payoff anchor retains the
first-order direction exactly and gives the chronological renormalization law.
-/

noncomputable section

namespace GameTheory

namespace QuittingAffineSummary

/-- Affine block parameterized by absorbed mass and its conditional payoff
anchor.  The condition `mass ≤ 1` ensures nonnegative survival. -/
def ofAbsorptionMass
    (mass anchor : ℝ) (hmass_le_one : mass ≤ 1) :
    QuittingAffineSummary where
  intercept := mass * anchor
  survival := 1 - mass
  survival_nonneg := sub_nonneg.mpr hmass_le_one

@[simp] theorem ofAbsorptionMass_intercept
    (mass anchor : ℝ) (hmass_le_one : mass ≤ 1) :
    (ofAbsorptionMass mass anchor hmass_le_one).intercept = mass * anchor := rfl

@[simp] theorem ofAbsorptionMass_survival
    (mass anchor : ℝ) (hmass_le_one : mass ≤ 1) :
    (ofAbsorptionMass mass anchor hmass_le_one).survival = 1 - mass := rfl

@[simp] theorem absorptionMass_ofAbsorptionMass
    (mass anchor : ℝ) (hmass_le_one : mass ≤ 1) :
    (ofAbsorptionMass mass anchor hmass_le_one).absorptionMass = mass := by
  simp [ofAbsorptionMass, absorptionMass]

/-- Exact finite-scale affine blow-up formula. -/
theorem eval_ofAbsorptionMass
    (mass anchor : ℝ) (hmass_le_one : mass ≤ 1) (w : ℝ) :
    (ofAbsorptionMass mass anchor hmass_le_one).eval w =
      w + mass * (anchor - w) := by
  simp [ofAbsorptionMass, eval]
  ring

/-- Exact target residual at absorbed-mass scale. -/
theorem targetResidual_ofAbsorptionMass
    (mass anchor : ℝ) (hmass_le_one : mass ≤ 1) (target : ℝ) :
    (ofAbsorptionMass mass anchor hmass_le_one).targetResidual target =
      mass * (anchor - target) := by
  rw [targetResidual_eq]
  simp [ofAbsorptionMass, absorptionMass]
  ring

/-- Such a block fixes `target` exactly iff it is neutral (`mass = 0`) or its
conditional anchor equals the target. -/
theorem isFixedAt_ofAbsorptionMass_iff
    (mass anchor : ℝ) (hmass_le_one : mass ≤ 1) (target : ℝ) :
    (ofAbsorptionMass mass anchor hmass_le_one).IsFixedAt target ↔
      mass = 0 ∨ anchor = target := by
  rw [isFixedAt_iff_targetResidual_eq_zero,
    targetResidual_ofAbsorptionMass]
  rw [mul_eq_zero, sub_eq_zero]

/-- Chronological composition adds absorbed masses with the inner mass
discounted by outer survival. -/
theorem absorptionMass_mul_ofAbsorptionMass
    (outerMass outerAnchor innerMass innerAnchor : ℝ)
    (houter : outerMass ≤ 1) (hinner : innerMass ≤ 1) :
    ((ofAbsorptionMass outerMass outerAnchor houter) *
      (ofAbsorptionMass innerMass innerAnchor hinner)).absorptionMass =
        outerMass + (1 - outerMass) * innerMass := by
  rw [absorptionMass_mul]
  simp [ofAbsorptionMass, absorptionMass]

/-- The intercept of a composite is the transported sum of its two absorbed
payoff moments. -/
theorem intercept_mul_ofAbsorptionMass
    (outerMass outerAnchor innerMass innerAnchor : ℝ)
    (houter : outerMass ≤ 1) (hinner : innerMass ≤ 1) :
    (((ofAbsorptionMass outerMass outerAnchor houter) *
      (ofAbsorptionMass innerMass innerAnchor hinner)).intercept) =
        outerMass * outerAnchor +
          (1 - outerMass) * innerMass * innerAnchor := by
  change outerMass * outerAnchor +
      (1 - outerMass) * (innerMass * innerAnchor) = _
  ring

/-- Exact target-residual renormalization under composition of two mass-anchor
blocks. -/
theorem targetResidual_mul_ofAbsorptionMass
    (outerMass outerAnchor innerMass innerAnchor target : ℝ)
    (houter : outerMass ≤ 1) (hinner : innerMass ≤ 1) :
    ((ofAbsorptionMass outerMass outerAnchor houter) *
      (ofAbsorptionMass innerMass innerAnchor hinner)).targetResidual target =
        outerMass * (outerAnchor - target) +
          (1 - outerMass) * innerMass * (innerAnchor - target) := by
  rw [targetResidual_mul, targetResidual_ofAbsorptionMass,
    targetResidual_ofAbsorptionMass]
  simp [ofAbsorptionMass]
  ring

/-- Division by nonzero absorbed mass recovers the anchor displacement
exactly. -/
theorem normalizedTargetResidual_ofAbsorptionMass
    (mass anchor : ℝ) (hmass_le_one : mass ≤ 1) (target : ℝ)
    (hmass : mass ≠ 0) :
    (ofAbsorptionMass mass anchor hmass_le_one).normalizedTargetResidual target =
      anchor - target := by
  unfold normalizedTargetResidual
  rw [targetResidual_ofAbsorptionMass,
    absorptionMass_ofAbsorptionMass]
  field_simp [hmass]
  ring

/-- Generic weighted intercept bound implies a uniform bound on the conditional
anchor whenever the block has positive absorbed mass. -/
theorem abs_fixedPoint_le_of_abs_intercept_le_mul_absorptionMass
    (summary : QuittingAffineSummary) (M : ℝ)
    (hsurvival_le_one : summary.survival ≤ 1)
    (hsurvival_ne_one : summary.survival ≠ 1)
    (hweighted : |summary.intercept| ≤ M * summary.absorptionMass) :
    |summary.fixedPoint| ≤ M := by
  have hsurvival_lt_one : summary.survival < 1 :=
    lt_of_le_of_ne hsurvival_le_one hsurvival_ne_one
  have hmass : 0 < summary.absorptionMass := by
    exact sub_pos.mpr hsurvival_lt_one
  rw [fixedPoint, abs_div, abs_of_pos hmass]
  rw [div_le_iff₀ hmass]
  simpa [absorptionMass] using hweighted

/-- A weighted intercept must vanish on the neutral face. -/
theorem intercept_eq_zero_of_abs_intercept_le_mul_absorptionMass
    (summary : QuittingAffineSummary) (M : ℝ)
    (hweighted : |summary.intercept| ≤ M * summary.absorptionMass)
    (hsurvival : summary.survival = 1) :
    summary.intercept = 0 := by
  have hle : |summary.intercept| ≤ 0 := by
    simpa [absorptionMass, hsurvival] using hweighted
  have hzero : |summary.intercept| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact abs_eq_zero.mp hzero

end QuittingAffineSummary

end GameTheory
