/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingBoundaryHolonomyMaxAffineResidual

/-!
# Absorbed-mass tangent and max-plus dynamics for quitting holonomy

Near survival one, raw affine coefficients collapse to the identity.  Writing
an affine block by absorbed mass and conditional payoff anchor retains the
first-order direction exactly and gives the chronological renormalization law.
The same module supplies the max-affine tangent and its scalar max-plus
dynamics; none of these coefficient laws is a strategic decoder.
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
  rw [fixedPoint, abs_div, abs_of_pos (sub_pos.mpr hsurvival_lt_one)]
  rw [div_le_iff₀ (sub_pos.mpr hsurvival_lt_one)]
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



/-- Pull a common nonnegative scale through a maximum after a common affine
translation. -/
theorem max_add_mul_eq_add_mul_max
    (base scale x y : ℝ) (hscale : 0 ≤ scale) :
    max (base + scale * x) (base + scale * y) =
      base + scale * max x y := by
  rcases le_total x y with hxy | hyx
  · have hscaled : scale * x ≤ scale * y :=
      mul_le_mul_of_nonneg_left hxy hscale
    calc
      max (base + scale * x) (base + scale * y) = base + scale * y :=
        max_eq_right (by simpa [add_comm] using add_le_add_left hscaled base)
      _ = base + scale * max x y := by rw [max_eq_right hxy]
  · have hscaled : scale * y ≤ scale * x :=
      mul_le_mul_of_nonneg_left hyx hscale
    calc
      max (base + scale * x) (base + scale * y) = base + scale * x :=
        max_eq_left (by simpa [add_comm] using add_le_add_left hscaled base)
      _ = base + scale * max x y := by rw [max_eq_left hyx]

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
  simp only [ofScaledObstacles_early, ofScaledObstacles_tail,
    absorptionMass_ofScaledObstacles]
  constructor
  · rintro ⟨hearly, htail⟩
    change target + mass * earlyDrift ≤ target at hearly
    change mass * tailAnchor ≤ mass * target at htail
    have hearly' : mass * earlyDrift ≤ 0 := by linarith
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨hearly, htail⟩
    constructor
    · nlinarith
    · nlinarith

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


namespace QuittingMaxPlusTangent

/-- Max-plus tangent operator with early floor and tail drift. -/
def eval (early tail x : ℝ) : ℝ :=
  max early (tail + x)

/-- `extra + 1` iterates of the tangent operator. -/
def iterateNonempty (early tail : ℝ) : ℕ → ℝ → ℝ
  | 0, x => eval early tail x
  | extra + 1, x => eval early tail (iterateNonempty early tail extra x)

@[simp] theorem iterateNonempty_zero (early tail x : ℝ) :
    iterateNonempty early tail 0 x = eval early tail x := rfl

@[simp] theorem iterateNonempty_succ
    (early tail : ℝ) (extra : ℕ) (x : ℝ) :
    iterateNonempty early tail (extra + 1) x =
      eval early tail (iterateNonempty early tail extra x) := rfl

/-- Safety at the tangent origin is exactly nonpositive early and tail drift. -/
theorem eval_zero_le_zero_iff (early tail : ℝ) :
    eval early tail 0 ≤ 0 ↔ early ≤ 0 ∧ tail ≤ 0 := by
  unfold eval
  simp only [add_zero, max_le_iff]

/-- Every iterate dominates the pure tail branch. -/
theorem linear_tail_le_iterateNonempty
    (early tail x : ℝ) (extra : ℕ) :
    (((extra + 1 : ℕ) : ℝ) * tail + x) ≤
      iterateNonempty early tail extra x := by
  induction extra with
  | zero =>
      simp [iterateNonempty, eval]
  | succ extra ih =>
      rw [iterateNonempty_succ]
      unfold eval
      calc
        (((extra + 2 : ℕ) : ℝ) * tail + x)
            = tail + ((((extra + 1 : ℕ) : ℝ) * tail) + x) := by
              push_cast
              ring
        _ ≤ tail + iterateNonempty early tail extra x :=
          by simpa [add_comm] using add_le_add_left ih tail
        _ ≤ max early (tail + iterateNonempty early tail extra x) :=
          le_max_right _ _

/-- Under nonpositive tail drift, the only surviving branches are the outer
floor and the tail translated through every copy. -/
theorem iterateNonempty_eq_max_of_tail_nonpos
    (early tail x : ℝ) (htail : tail ≤ 0) (extra : ℕ) :
    iterateNonempty early tail extra x =
      max early ((((extra + 1 : ℕ) : ℝ) * tail) + x) := by
  induction extra with
  | zero =>
      simp [iterateNonempty, eval]
  | succ extra ih =>
      rw [iterateNonempty_succ, ih]
      unfold eval
      let y : ℝ := (((extra + 1 : ℕ) : ℝ) * tail) + x
      have hy : tail + y = (((extra + 2 : ℕ) : ℝ) * tail) + x := by
        dsimp [y]
        push_cast
        ring
      by_cases h : early ≤ y
      · rw [max_eq_right h, hy]
      · have h' : y ≤ early := le_of_not_ge h
        rw [max_eq_left h']
        have htailEarly : tail + early ≤ early := by linarith
        rw [max_eq_left htailEarly]
        rw [max_eq_left]
        calc
          (((extra + 2 : ℕ) : ℝ) * tail) + x
              = tail + y := hy.symm
          _ ≤ tail + early := by simpa [add_comm] using add_le_add_left h' tail
          _ ≤ early := htailEarly

/-- Zero tail drift is already the threshold-closure idempotent after one
application. -/
theorem iterateNonempty_zero_tail
    (early x : ℝ) (extra : ℕ) :
    iterateNonempty early 0 extra x = max early x := by
  rw [iterateNonempty_eq_max_of_tail_nonpos early 0 x le_rfl]
  simp

/-- Positive tail drift makes the tangent value exceed every finite budget
under enough repetitions. -/
theorem exists_iterateNonempty_gt_of_tail_pos
    (early tail x budget : ℝ) (htail : 0 < tail) :
    ∃ extra : ℕ, budget < iterateNonempty early tail extra x := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((budget - x) / tail)
  refine ⟨n, ?_⟩
  have hlinear : budget < (((n + 1 : ℕ) : ℝ) * tail) + x := by
    have hn' : budget - x < (n : ℝ) * tail :=
      (div_lt_iff₀ htail).mp hn
    have hnle : (n : ℝ) * tail ≤ ((n + 1 : ℕ) : ℝ) * tail := by
      apply mul_le_mul_of_nonneg_right _ htail.le
      exact_mod_cast Nat.le_succ n
    linarith
  exact hlinear.trans_le
    (linear_tail_le_iterateNonempty early tail x n)

/-- Negative tail drift reaches the constant early projector after finitely
many iterates. -/
theorem exists_eventually_iterateNonempty_eq_early_of_tail_neg
    (early tail x : ℝ) (htail : tail < 0) :
    ∃ cutoff : ℕ, ∀ extra, cutoff ≤ extra →
      iterateNonempty early tail extra x = early := by
  have hden : 0 < -tail := neg_pos.mpr htail
  obtain ⟨cutoff, hcutoff⟩ :=
    exists_nat_gt ((x - early) / (-tail))
  refine ⟨cutoff, ?_⟩
  intro extra hextra
  rw [iterateNonempty_eq_max_of_tail_nonpos early tail x htail.le]
  rw [max_eq_left]
  have hcutoffR : (cutoff : ℝ) ≤ ((extra + 1 : ℕ) : ℝ) := by
    exact_mod_cast (hextra.trans (Nat.le_succ extra))
  have hbase : x - early < (cutoff : ℝ) * (-tail) :=
    (div_lt_iff₀ hden).mp hcutoff
  have htransport :
      (cutoff : ℝ) * (-tail) ≤ ((extra + 1 : ℕ) : ℝ) * (-tail) :=
    mul_le_mul_of_nonneg_right hcutoffR hden.le
  nlinarith

/-- Tangent-dynamics trichotomy, stated without choosing which sign case
holds. -/
theorem dynamics_trichotomy (early tail x : ℝ) :
    (tail < 0 ∧ ∃ cutoff : ℕ, ∀ extra, cutoff ≤ extra →
        iterateNonempty early tail extra x = early) ∨
      (tail = 0 ∧ ∀ extra, iterateNonempty early tail extra x = max early x) ∨
      (0 < tail ∧ ∀ budget : ℝ, ∃ extra : ℕ,
        budget < iterateNonempty early tail extra x) := by
  rcases lt_trichotomy tail 0 with hneg | hzero | hpos
  · exact Or.inl ⟨hneg,
      exists_eventually_iterateNonempty_eq_early_of_tail_neg
        early tail x hneg⟩
  · exact Or.inr (Or.inl ⟨hzero, fun extra => by
      subst tail
      exact iterateNonempty_zero_tail early x extra⟩)
  · exact Or.inr (Or.inr ⟨hpos, fun budget =>
      exists_iterateNonempty_gt_of_tail_pos early tail x budget hpos⟩)

end QuittingMaxPlusTangent

end GameTheory
