/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityMaxAffine

/-!
# Max-plus tangent coordinates for unilateral stopping holonomy

Early stopping and tail continuation produce a max-plus tangent at absorbed
mass scale.  The formulas here are exact at finite scale, including the
quadratic probe correction that vanishes in a first-order limit.
-/

noncomputable section

namespace GameTheory

/-- Pull a common nonnegative scale through a maximum after a common affine
translation. -/
theorem max_add_mul_eq_add_mul_max
    (base scale x y : ℝ) (hscale : 0 ≤ scale) :
    max (base + scale * x) (base + scale * y) =
      base + scale * max x y := by
  rcases le_total x y with hxy | hyx
  · have hscaled : scale * x ≤ scale * y :=
      mul_le_mul_of_nonneg_left hxy hscale
    rw [max_eq_right hxy, max_eq_right (add_le_add_left hscaled base)]
  · have hscaled : scale * y ≤ scale * x :=
      mul_le_mul_of_nonneg_left hyx hscale
    rw [max_eq_left hyx, max_eq_left (add_le_add_left hscaled base)]

namespace QuittingMaxAffineSummary

/-- Max-affine block resolved at target and absorbed-mass scale.

`earlyDrift` is the early obstacle measured per unit mass, while `tailAnchor`
is the conditional continuation value of the tail branch. -/
def ofScaledObstacles
    (target mass earlyDrift tailAnchor : ℝ)
    (hmass_le_one : mass ≤ 1) : QuittingMaxAffineSummary where
  early := target + mass * earlyDrift
  tail := mass * tailAnchor
  survival := 1 - mass
  survival_nonneg := sub_nonneg.mpr hmass_le_one

@[simp] theorem ofScaledObstacles_early
    (target mass earlyDrift tailAnchor : ℝ)
    (hmass_le_one : mass ≤ 1) :
    (ofScaledObstacles target mass earlyDrift tailAnchor
      hmass_le_one).early = target + mass * earlyDrift := rfl

@[simp] theorem ofScaledObstacles_tail
    (target mass earlyDrift tailAnchor : ℝ)
    (hmass_le_one : mass ≤ 1) :
    (ofScaledObstacles target mass earlyDrift tailAnchor
      hmass_le_one).tail = mass * tailAnchor := rfl

@[simp] theorem ofScaledObstacles_survival
    (target mass earlyDrift tailAnchor : ℝ)
    (hmass_le_one : mass ≤ 1) :
    (ofScaledObstacles target mass earlyDrift tailAnchor
      hmass_le_one).survival = 1 - mass := rfl

@[simp] theorem absorptionMass_ofScaledObstacles
    (target mass earlyDrift tailAnchor : ℝ)
    (hmass_le_one : mass ≤ 1) :
    (ofScaledObstacles target mass earlyDrift tailAnchor
      hmass_le_one).absorptionMass = mass := by
  simp [ofScaledObstacles, absorptionMass]

/-- Exact normalized obstacle at the base target. -/
theorem eval_target_ofScaledObstacles
    (target mass earlyDrift tailAnchor : ℝ)
    (hmass_le_one : mass ≤ 1) (hmass_nonneg : 0 ≤ mass) :
    (ofScaledObstacles target mass earlyDrift tailAnchor
      hmass_le_one).eval target =
      target + mass * max earlyDrift (tailAnchor - target) := by
  change max (target + mass * earlyDrift)
      (mass * tailAnchor + (1 - mass) * target) = _
  have htail :
      mass * tailAnchor + (1 - mass) * target =
        target + mass * (tailAnchor - target) := by ring
  rw [htail, max_add_mul_eq_add_mul_max _ _ _ _ hmass_nonneg]

/-- The target excess is absorbed mass times the max-plus tangent obstacle. -/
theorem targetExcess_ofScaledObstacles
    (target mass earlyDrift tailAnchor : ℝ)
    (hmass_le_one : mass ≤ 1) (hmass_nonneg : 0 ≤ mass) :
    (ofScaledObstacles target mass earlyDrift tailAnchor
      hmass_le_one).targetExcess target =
      mass * max earlyDrift (tailAnchor - target) := by
  unfold targetExcess
  rw [eval_target_ofScaledObstacles _ _ _ _ hmass_le_one hmass_nonneg]
  ring

/-- At positive scale, strategic safety is exactly nonpositive early drift and
a tail anchor below the target. -/
theorem eval_target_ofScaledObstacles_le_iff
    (target mass earlyDrift tailAnchor : ℝ)
    (hmass_le_one : mass ≤ 1) (hmass_pos : 0 < mass) :
    (ofScaledObstacles target mass earlyDrift tailAnchor
      hmass_le_one).eval target ≤ target ↔
      earlyDrift ≤ 0 ∧ tailAnchor ≤ target := by
  rw [eval_le_target_iff]
  constructor
  · rintro ⟨hearly, htail⟩
    change target + mass * earlyDrift ≤ target at hearly
    change mass * tailAnchor ≤ mass * target at htail
    have hearly' : mass * earlyDrift ≤ 0 := by linarith
    exact ⟨by nlinarith, (mul_le_mul_left hmass_pos).mp htail⟩
  · rintro ⟨hearly, htail⟩
    constructor
    · change target + mass * earlyDrift ≤ target
      nlinarith
    · change mass * tailAnchor ≤ mass * target
      exact (mul_le_mul_left hmass_pos).mpr htail

/-- Exact finite-scale probe formula.  After normalizing by `mass`, the only
correction to the limiting tangent map is `-mass * x`. -/
theorem eval_probe_ofScaledObstacles
    (target mass earlyDrift tailAnchor x : ℝ)
    (hmass_le_one : mass ≤ 1) (hmass_nonneg : 0 ≤ mass) :
    (ofScaledObstacles target mass earlyDrift tailAnchor
      hmass_le_one).eval (target + mass * x) =
      target + mass *
        max earlyDrift (tailAnchor - target + x - mass * x) := by
  change max (target + mass * earlyDrift)
      (mass * tailAnchor + (1 - mass) * (target + mass * x)) = _
  have htail :
      mass * tailAnchor + (1 - mass) * (target + mass * x) =
        target + mass * (tailAnchor - target + x - mass * x) := by ring
  rw [htail, max_add_mul_eq_add_mul_max _ _ _ _ hmass_nonneg]

/-- Dividing the probe displacement by positive mass yields the exact
finite-scale max-plus tangent expression. -/
theorem normalized_eval_probe_ofScaledObstacles
    (target mass earlyDrift tailAnchor x : ℝ)
    (hmass_le_one : mass ≤ 1) (hmass_pos : 0 < mass) :
    ((ofScaledObstacles target mass earlyDrift tailAnchor
      hmass_le_one).eval (target + mass * x) - target) / mass =
      max earlyDrift (tailAnchor - target + x - mass * x) := by
  rw [eval_probe_ofScaledObstacles _ _ _ _ _ hmass_le_one hmass_pos.le]
  field_simp [hmass_pos.ne']
  ring

/-- Generic weighted tail bound implies a uniform bound on the conditional
tail anchor whenever tail absorption mass is positive. -/
theorem abs_tailAnchor_le_of_abs_tail_le_mul_absorptionMass
    (summary : QuittingMaxAffineSummary) (M : ℝ)
    (hsurvival_le_one : summary.survival ≤ 1)
    (hsurvival_ne_one : summary.survival ≠ 1)
    (hweighted : |summary.tail| ≤ M * summary.absorptionMass) :
    |summary.tailAnchor| ≤ M := by
  have hsurvival_lt_one : summary.survival < 1 :=
    lt_of_le_of_ne hsurvival_le_one hsurvival_ne_one
  have hmass : 0 < summary.absorptionMass := by
    exact sub_pos.mpr hsurvival_lt_one
  rw [tailAnchor, abs_div, abs_of_pos hmass]
  rw [div_le_iff₀ hmass]
  simpa [absorptionMass] using hweighted

/-- A weighted tail intercept must vanish on the neutral face. -/
theorem tail_eq_zero_of_abs_tail_le_mul_absorptionMass
    (summary : QuittingMaxAffineSummary) (M : ℝ)
    (hweighted : |summary.tail| ≤ M * summary.absorptionMass)
    (hsurvival : summary.survival = 1) :
    summary.tail = 0 := by
  have hle : |summary.tail| ≤ 0 := by
    simpa [absorptionMass, hsurvival] using hweighted
  have hzero : |summary.tail| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact abs_eq_zero.mp hzero

end QuittingMaxAffineSummary

end GameTheory
