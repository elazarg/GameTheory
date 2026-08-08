/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Root.SeparatedTerminalAnchor
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Repair.CertifiedBoundaryPolyhedron

/-!
# Boundary holonomy of actual finite quitting chains

This file bundles the affine prescribed-payoff and max-affine unilateral
best-response maps of a finite quitting block.  The bundled coefficients form
an associative semigroup.  More importantly, the game-facing objects below
are not arbitrary coefficient tuples: they are extracted, player by player,
from one common product-root block of a selected finite exact Nash--Bellman
minimizer.

The calibrated source also retains the positive debt owner and the marked
terminal packet.  Its preterminal opponent survival and final marked action
mass are separate fields.  A block retains its exact entry and exit dynamic-
debt points and the whole underlying finite chain, so cross-player root
compatibility and chronological provenance cannot be lost by scalarizing the
coefficients.

This is a finite-middle interface, not the missing compactness/decoder
theorem.  In particular, it does not claim that limits of arbitrarily long
realized holonomies remain realized by finite blocks, or that a close seam is
splice-admissible.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type}
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## The finite-dimensional coefficient semigroup -/

/-- An affine prescribed-payoff map `w ↦ intercept + survival * w`. -/
@[ext] structure QuittingAffineSummary where
  intercept : ℝ
  survival : ℝ
  survival_nonneg : 0 ≤ survival

namespace QuittingAffineSummary

/-- Evaluation on a supplied terminal payoff. -/
def eval (summary : QuittingAffineSummary) (w : ℝ) : ℝ :=
  summary.intercept + summary.survival * w

/-- Chronological composition: the inner block is played after the outer
block. -/
def compose (outer inner : QuittingAffineSummary) :
    QuittingAffineSummary where
  intercept := outer.intercept + outer.survival * inner.intercept
  survival := outer.survival * inner.survival
  survival_nonneg := mul_nonneg outer.survival_nonneg inner.survival_nonneg

theorem eval_compose (outer inner : QuittingAffineSummary) (w : ℝ) :
    (outer.compose inner).eval w = outer.eval (inner.eval w) := by
  simp only [eval, compose]
  ring

theorem compose_assoc (first second third : QuittingAffineSummary) :
    (first.compose second).compose third =
      first.compose (second.compose third) := by
  ext
  · simp [compose]
    ring
  · simp [compose, mul_assoc]

instance : Semigroup QuittingAffineSummary where
  mul := compose
  mul_assoc := compose_assoc

@[simp] theorem mul_eq_compose (outer inner : QuittingAffineSummary) :
    outer * inner = outer.compose inner := rfl

@[simp] theorem eval_mul (outer inner : QuittingAffineSummary) (w : ℝ) :
    (outer * inner).eval w = outer.eval (inner.eval w) :=
  eval_compose outer inner w

/-- The unique fixed point of a contracting affine block. -/
def fixedPoint (summary : QuittingAffineSummary) : ℝ :=
  summary.intercept / (1 - summary.survival)

theorem eval_fixedPoint (summary : QuittingAffineSummary)
    (hcontracting : summary.survival ≠ 1) :
    summary.eval summary.fixedPoint = summary.fixedPoint := by
  have hdenom : 1 - summary.survival ≠ 0 :=
    sub_ne_zero.mpr hcontracting.symm
  unfold eval fixedPoint
  field_simp
  ring

end QuittingAffineSummary

/-- Coefficients of `w ↦ max early (tail + survival * w)`. -/
@[ext] structure QuittingMaxAffineSummary where
  early : ℝ
  tail : ℝ
  survival : ℝ
  survival_nonneg : 0 ≤ survival

namespace QuittingMaxAffineSummary

/-- Evaluation on a supplied terminal unilateral value. -/
def eval (summary : QuittingMaxAffineSummary) (w : ℝ) : ℝ :=
  max summary.early (summary.tail + summary.survival * w)

/-- Chronological max-affine composition. -/
def compose (outer inner : QuittingMaxAffineSummary) :
    QuittingMaxAffineSummary where
  early := max outer.early
    (outer.tail + outer.survival * inner.early)
  tail := outer.tail + outer.survival * inner.tail
  survival := outer.survival * inner.survival
  survival_nonneg := mul_nonneg outer.survival_nonneg inner.survival_nonneg

theorem eval_compose (outer inner : QuittingMaxAffineSummary) (w : ℝ) :
    (outer.compose inner).eval w = outer.eval (inner.eval w) := by
  change quittingBoundaryBestResponse
      (max outer.early (outer.tail + outer.survival * inner.early))
      (outer.tail + outer.survival * inner.tail)
      (outer.survival * inner.survival) w =
    quittingBoundaryBestResponse outer.early outer.tail outer.survival
      (quittingBoundaryBestResponse inner.early inner.tail
        inner.survival w)
  exact (quittingBoundaryBestResponse_compose
      outer.early outer.tail outer.survival
      inner.early inner.tail inner.survival w
      outer.survival_nonneg).symm

theorem compose_assoc (first second third : QuittingMaxAffineSummary) :
    (first.compose second).compose third =
      first.compose (second.compose third) := by
  ext
  · simp only [compose]
    have hdistrib :
        first.tail + (first.survival : ℝ) *
            max second.early
              (second.tail + second.survival * third.early) =
          max (first.tail + first.survival * second.early)
            (first.tail + first.survival *
              (second.tail + second.survival * third.early)) := by
      rcases le_total second.early
          (second.tail + second.survival * third.early) with h | h
      · rw [max_eq_right h, max_eq_right]
        nlinarith [first.survival_nonneg]
      · rw [max_eq_left h, max_eq_left]
        nlinarith [first.survival_nonneg]
    rw [hdistrib, max_assoc]
    congr 2
    ring
  · simp only [compose]
    ring
  · simp [compose, mul_assoc]

instance : Semigroup QuittingMaxAffineSummary where
  mul := compose
  mul_assoc := compose_assoc

@[simp] theorem mul_eq_compose
    (outer inner : QuittingMaxAffineSummary) :
    outer * inner = outer.compose inner := rfl

@[simp] theorem eval_mul
    (outer inner : QuittingMaxAffineSummary) (w : ℝ) :
    (outer * inner).eval w = outer.eval (inner.eval w) :=
  eval_compose outer inner w

end QuittingMaxAffineSummary

/-- The playerwise prescribed and unilateral maps of one common quitting
block. -/
@[ext] structure QuittingBoundaryHolonomy (ι : Type) where
  prescribed : ι → QuittingAffineSummary
  bestResponse : ι → QuittingMaxAffineSummary

namespace QuittingBoundaryHolonomy

/-- Chronological composition, pointwise over players. -/
def compose (outer inner : QuittingBoundaryHolonomy ι) :
    QuittingBoundaryHolonomy ι where
  prescribed who := outer.prescribed who * inner.prescribed who
  bestResponse who := outer.bestResponse who * inner.bestResponse who

theorem compose_assoc (first second third : QuittingBoundaryHolonomy ι) :
    (first.compose second).compose third =
      first.compose (second.compose third) := by
  apply QuittingBoundaryHolonomy.ext
  · funext who
    exact QuittingAffineSummary.compose_assoc
      (first.prescribed who) (second.prescribed who)
        (third.prescribed who)
  · funext who
    exact QuittingMaxAffineSummary.compose_assoc
      (first.bestResponse who) (second.bestResponse who)
        (third.bestResponse who)

instance : Semigroup (QuittingBoundaryHolonomy ι) where
  mul := compose
  mul_assoc := compose_assoc

@[simp] theorem mul_eq_compose
    (outer inner : QuittingBoundaryHolonomy ι) :
    outer * inner = outer.compose inner := rfl

@[simp] theorem prescribed_mul
    (outer inner : QuittingBoundaryHolonomy ι) (who : ι) :
    (outer * inner).prescribed who =
      outer.prescribed who * inner.prescribed who := rfl

@[simp] theorem bestResponse_mul
    (outer inner : QuittingBoundaryHolonomy ι) (who : ι) :
    (outer * inner).bestResponse who =
      outer.bestResponse who * inner.bestResponse who := rfl

/-- Exact scalar regret after attaching a terminal payoff `w` with certified
relative unilateral debt `β`. -/
def gap (holonomy : QuittingBoundaryHolonomy ι)
    (who : ι) (β w : ℝ) : ℝ :=
  (holonomy.bestResponse who).eval (w + β) -
    (holonomy.prescribed who).eval w

/-- The bundled gap is the landed two-halfspace max-affine expression. -/
theorem gap_eq_boundaryGap (holonomy : QuittingBoundaryHolonomy ι)
    (who : ι) (β w : ℝ) :
    holonomy.gap who β w =
      quittingBoundaryGap
        (holonomy.bestResponse who).early
        (holonomy.bestResponse who).tail
        (holonomy.prescribed who).intercept
        (holonomy.prescribed who).survival
        (holonomy.bestResponse who).survival β w := by
  rfl

/-- Fixed-word cap safety is exactly two scalar affine inequalities per
player. -/
theorem gap_le_iff (holonomy : QuittingBoundaryHolonomy ι)
    (who : ι) (β w ε : ℝ) :
    holonomy.gap who β w ≤ ε ↔
      (holonomy.bestResponse who).early -
          (holonomy.prescribed who).intercept -
          (holonomy.prescribed who).survival * w ≤ ε ∧
        (holonomy.bestResponse who).tail -
          (holonomy.prescribed who).intercept +
          ((holonomy.bestResponse who).survival -
            (holonomy.prescribed who).survival) * w +
          (holonomy.bestResponse who).survival * β ≤ ε := by
  rw [gap_eq_boundaryGap, quittingBoundaryGap_le_iff]

end QuittingBoundaryHolonomy

/-! ## Extraction from one common product-root block -/

variable [Fintype ι] [DecidableEq ι]

/-- The one-stage affine/max-affine action of an actual product root. -/
def quittingBoundaryStageHolonomy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    QuittingBoundaryHolonomy ι where
  prescribed who := {
    intercept :=
      (roots time who true).toReal *
          quittingFixedOpponentsQuitValue reward roots who time +
        (roots time who false).toReal *
          quittingFixedOpponentsContinueReward reward roots who time
    survival := (roots time who false).toReal *
      quittingFixedOpponentsContinueMass roots who time
    survival_nonneg := mul_nonneg ENNReal.toReal_nonneg
      (quittingStationaryContinueMass_nonneg
        (Function.update (roots time) who (PMF.pure false))) }
  bestResponse who := {
    early := quittingFixedOpponentsQuitValue reward roots who time
    tail := quittingFixedOpponentsContinueReward reward roots who time
    survival := quittingFixedOpponentsContinueMass roots who time
    survival_nonneg := quittingStationaryContinueMass_nonneg
      (Function.update (roots time) who (PMF.pure false)) }

/-- Holonomy of `extra + 1` chronological stages.  Nonempty blocks avoid the
spurious finite early floor which would be needed to encode an identity
best-response map. -/
def quittingFiniteBoundaryHolonomy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : ℕ) : ℕ →
    QuittingBoundaryHolonomy ι
  | 0 => quittingBoundaryStageHolonomy reward roots start
  | extra + 1 =>
      quittingBoundaryStageHolonomy reward roots start *
        quittingFiniteBoundaryHolonomy reward roots (start + 1) extra

@[simp] theorem quittingFiniteBoundaryHolonomy_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) :
    quittingFiniteBoundaryHolonomy reward roots start (extra + 1) =
      quittingBoundaryStageHolonomy reward roots start *
        quittingFiniteBoundaryHolonomy reward roots (start + 1) extra := by
  rfl

/-- The prescribed component is the literal finite policy evaluation of the
player's marginal in the common root block. -/
theorem quittingFiniteBoundaryHolonomy_prescribed_eval
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ)
    (who : ι) (terminalValue : ℝ) :
    QuittingAffineSummary.eval
        (QuittingBoundaryHolonomy.prescribed
          (quittingFiniteBoundaryHolonomy reward roots start extra) who)
        terminalValue =
      quittingFiniteTerminalHazardValue reward roots who
        (fun time => roots time who) terminalValue start (extra + 1) := by
  induction extra generalizing start with
  | zero =>
      simp only [quittingFiniteBoundaryHolonomy,
        quittingBoundaryStageHolonomy, QuittingAffineSummary.eval,
        quittingFiniteTerminalHazardValue]
      ring
  | succ extra ih =>
      rw [quittingFiniteBoundaryHolonomy.eq_def,
        QuittingBoundaryHolonomy.prescribed_mul,
        QuittingAffineSummary.eval_mul, ih]
      simp only [quittingBoundaryStageHolonomy,
        QuittingAffineSummary.eval,
        quittingFiniteTerminalHazardValue]
      ring

/-- The best-response component is the literal finite Bellman stopping value
against the same opponents. -/
theorem quittingFiniteBoundaryHolonomy_bestResponse_eval
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ)
    (who : ι) (terminalValue : ℝ) :
    QuittingMaxAffineSummary.eval
        (QuittingBoundaryHolonomy.bestResponse
          (quittingFiniteBoundaryHolonomy reward roots start extra) who)
        terminalValue =
      quittingFiniteTerminalBestResponseValue reward roots who terminalValue
        start (extra + 1) := by
  induction extra generalizing start with
  | zero =>
      simp only [quittingFiniteBoundaryHolonomy,
        quittingBoundaryStageHolonomy, QuittingMaxAffineSummary.eval]
      rfl
  | succ extra ih =>
      rw [quittingFiniteBoundaryHolonomy.eq_def,
        QuittingBoundaryHolonomy.bestResponse_mul,
        QuittingMaxAffineSummary.eval_mul, ih]
      rfl

/-- For an actual finite root block, bundled scalar regret is literally the
finite arbitrary-behavior Bellman cap minus prescribed policy evaluation. -/
theorem quittingFiniteBoundaryHolonomy_gap_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ)
    (who : ι) (β w : ℝ) :
    (quittingFiniteBoundaryHolonomy reward roots start extra).gap who β w =
      quittingFiniteTerminalBestResponseValue reward roots who (w + β)
          start (extra + 1) -
        quittingFiniteTerminalHazardValue reward roots who
          (fun time => roots time who) w start (extra + 1) := by
  unfold QuittingBoundaryHolonomy.gap
  rw [quittingFiniteBoundaryHolonomy_bestResponse_eval,
    quittingFiniteBoundaryHolonomy_prescribed_eval]

/-- Actual finite root blocks compose exactly when placed chronologically.
Both sides are extracted from the same root family, so this equality also
certifies all cross-player product-root compatibility which the scalar
coefficients alone would forget. -/
theorem quittingFiniteBoundaryHolonomy_concat
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start first second : ℕ) :
    quittingFiniteBoundaryHolonomy reward roots start
        (first + second + 1) =
      quittingFiniteBoundaryHolonomy reward roots start first *
        quittingFiniteBoundaryHolonomy reward roots (start + first + 1)
          second := by
  induction first generalizing start with
  | zero => simp [quittingFiniteBoundaryHolonomy]
  | succ first ih =>
      rw [show Nat.succ first + second + 1 =
        (first + second + 1) + 1 by omega]
      rw [quittingFiniteBoundaryHolonomy_succ reward roots start
        (first + second + 1)]
      rw [quittingFiniteBoundaryHolonomy_succ reward roots start first]
      rw [ih (start + 1)]
      rw [mul_assoc]
      congr 1
      congr 1
      congr 1
      omega

/-! ## Exact five-scalar coordinates and their uniform bounds -/

/-- Front recursion for opponent-only survival. -/
theorem quittingOpponentSurvivalWeight_succ_front
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingOpponentSurvivalWeight roots who start (fuel + 1) =
      quittingFixedOpponentsContinueMass roots who start *
        quittingOpponentSurvivalWeight roots who (start + 1) fuel := by
  rw [← quittingFiniteContinueWeight_fixedOpponents_eq_survivalWeight,
    ← quittingFiniteContinueWeight_fixedOpponents_eq_survivalWeight]
  rfl

/-- The prescribed intercept is the actual zero-boundary policy value. -/
theorem quittingFiniteBoundaryHolonomy_prescribed_intercept
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι) :
    QuittingAffineSummary.intercept
        (QuittingBoundaryHolonomy.prescribed
          (quittingFiniteBoundaryHolonomy reward roots start extra) who) =
      quittingFiniteTerminalHazardValue reward roots who
        (fun time => roots time who) 0 start (extra + 1) := by
  have h := quittingFiniteBoundaryHolonomy_prescribed_eval
    reward roots start extra who 0
  simpa [QuittingAffineSummary.eval] using h

/-- The prescribed slope is full product survival through the actual block. -/
theorem quittingFiniteBoundaryHolonomy_prescribed_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι) :
    QuittingAffineSummary.survival
        (QuittingBoundaryHolonomy.prescribed
          (quittingFiniteBoundaryHolonomy reward roots start extra) who) =
      quittingFiniteFullSurvivalWeight roots who
        (fun time => roots time who) start (extra + 1) := by
  induction extra generalizing start with
  | zero =>
      simp [quittingFiniteBoundaryHolonomy,
        quittingBoundaryStageHolonomy,
        quittingFiniteFullSurvivalWeight, quittingFiniteContinueWeight,
        quittingFiniteFullContinueMass]
  | succ extra ih =>
      rw [quittingFiniteBoundaryHolonomy.eq_def,
        QuittingBoundaryHolonomy.prescribed_mul]
      change
        ((roots start who false).toReal *
            quittingFixedOpponentsContinueMass roots who start) *
              QuittingAffineSummary.survival
                (QuittingBoundaryHolonomy.prescribed
                  (quittingFiniteBoundaryHolonomy reward roots
                    (start + 1) extra) who) = _
      rw [ih]
      rfl

/-- The early-stop coordinate is the actual best pure stopping value before
the boundary. -/
theorem quittingFiniteBoundaryHolonomy_bestResponse_early
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι) :
    QuittingMaxAffineSummary.early
        (QuittingBoundaryHolonomy.bestResponse
          (quittingFiniteBoundaryHolonomy reward roots start extra) who) =
      quittingFiniteEarlyBestResponseValue reward roots who start extra := by
  induction extra generalizing start with
  | zero => rfl
  | succ extra ih =>
      rw [quittingFiniteBoundaryHolonomy.eq_def,
        QuittingBoundaryHolonomy.bestResponse_mul]
      change max (quittingFixedOpponentsQuitValue reward roots who start)
        (quittingFixedOpponentsContinueReward reward roots who start +
          quittingFixedOpponentsContinueMass roots who start *
            QuittingMaxAffineSummary.early
              (QuittingBoundaryHolonomy.bestResponse
                (quittingFiniteBoundaryHolonomy reward roots
                  (start + 1) extra) who)) = _
      rw [ih]
      rfl

/-- The continue-through intercept is the actual zero-boundary continuation
value. -/
theorem quittingFiniteBoundaryHolonomy_bestResponse_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι) :
    QuittingMaxAffineSummary.tail
        (QuittingBoundaryHolonomy.bestResponse
          (quittingFiniteBoundaryHolonomy reward roots start extra) who) =
      quittingFiniteContinueToBoundaryValue reward roots who 0
        start (extra + 1) := by
  induction extra generalizing start with
  | zero =>
      simp [quittingFiniteBoundaryHolonomy,
        quittingBoundaryStageHolonomy,
        quittingFiniteContinueToBoundaryValue]
  | succ extra ih =>
      rw [quittingFiniteBoundaryHolonomy.eq_def,
        QuittingBoundaryHolonomy.bestResponse_mul]
      change quittingFixedOpponentsContinueReward reward roots who start +
          quittingFixedOpponentsContinueMass roots who start *
            QuittingMaxAffineSummary.tail
              (QuittingBoundaryHolonomy.bestResponse
                (quittingFiniteBoundaryHolonomy reward roots
                  (start + 1) extra) who) = _
      rw [ih]
      rfl

/-- The max-affine slope is actual opponent-only survival. -/
theorem quittingFiniteBoundaryHolonomy_bestResponse_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι) :
    QuittingMaxAffineSummary.survival
        (QuittingBoundaryHolonomy.bestResponse
          (quittingFiniteBoundaryHolonomy reward roots start extra) who) =
      quittingOpponentSurvivalWeight roots who start (extra + 1) := by
  induction extra generalizing start with
  | zero =>
      simp [quittingFiniteBoundaryHolonomy,
        quittingBoundaryStageHolonomy, quittingOpponentSurvivalWeight]
  | succ extra ih =>
      rw [quittingFiniteBoundaryHolonomy.eq_def,
        QuittingBoundaryHolonomy.bestResponse_mul]
      change quittingFixedOpponentsContinueMass roots who start *
          QuittingMaxAffineSummary.survival
            (QuittingBoundaryHolonomy.bestResponse
              (quittingFiniteBoundaryHolonomy reward roots
                (start + 1) extra) who) = _
      rw [ih]
      exact (quittingOpponentSurvivalWeight_succ_front
        roots who start (extra + 1)).symm

/-- A pure-Quit endpoint against arbitrary opponent roots stays within the
common terminal reward bound. -/
theorem abs_quittingFixedOpponentsQuitValue_le_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    |quittingFixedOpponentsQuitValue reward roots who time| ≤
      quittingRewardBound reward := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    reward roots who (0 : Payoff ι) time]
  exact abs_quittingRootExpectedPayoff_le_bound reward (0 : Payoff ι)
    (Function.update (roots time) who (PMF.pure true)) who
    (abs_reward_le_quittingRewardBound reward)
    (fun _ => by simpa using quittingRewardBound_nonneg reward)

/-- Continuing through a finite block to zero remains within the terminal
reward bound. -/
theorem abs_quittingFiniteContinueToBoundaryValue_zero_le_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ start fuel,
      |quittingFiniteContinueToBoundaryValue reward roots who 0 start fuel| ≤
        quittingRewardBound reward := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      change |(0 : ℝ)| ≤ quittingRewardBound reward
      simpa using quittingRewardBound_nonneg reward
  | succ fuel ih =>
      rw [quittingFiniteContinueToBoundaryValue]
      rw [← quittingRootContinuePayoff_eq_fixedOpponents reward roots who
        (fun _ => quittingFiniteContinueToBoundaryValue reward roots who 0
          (start + 1) fuel) start]
      exact abs_quittingRootExpectedPayoff_le_bound reward
        (fun _ => quittingFiniteContinueToBoundaryValue reward roots who 0
          (start + 1) fuel)
        (Function.update (roots start) who (PMF.pure false)) who
        (abs_reward_le_quittingRewardBound reward) (fun _ => ih (start + 1))

/-- The finite early-stop maximum remains within the same reward bound. -/
theorem abs_quittingFiniteEarlyBestResponseValue_le_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ start fuel,
      |quittingFiniteEarlyBestResponseValue reward roots who start fuel| ≤
        quittingRewardBound reward := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      exact abs_quittingFixedOpponentsQuitValue_le_rewardBound
        reward roots who start
  | succ fuel ih =>
      rw [quittingFiniteEarlyBestResponseValue]
      have hquit := abs_quittingFixedOpponentsQuitValue_le_rewardBound
        reward roots who start
      have hcontinue :
          |quittingFixedOpponentsContinueReward reward roots who start +
            quittingFixedOpponentsContinueMass roots who start *
              quittingFiniteEarlyBestResponseValue reward roots who
                (start + 1) fuel| ≤ quittingRewardBound reward := by
        rw [← quittingRootContinuePayoff_eq_fixedOpponents reward roots who
          (fun _ => quittingFiniteEarlyBestResponseValue reward roots who
            (start + 1) fuel) start]
        exact abs_quittingRootExpectedPayoff_le_bound reward
          (fun _ => quittingFiniteEarlyBestResponseValue reward roots who
            (start + 1) fuel)
          (Function.update (roots start) who (PMF.pure false)) who
          (abs_reward_le_quittingRewardBound reward) (fun _ => ih (start + 1))
      rw [abs_le] at hquit hcontinue ⊢
      exact ⟨hquit.1.trans (le_max_left _ _),
        max_le hquit.2 hcontinue.2⟩

/-- The prescribed zero-boundary value of the actual root marginals is also
uniformly bounded. -/
theorem abs_quittingFiniteTerminalHazardValue_self_zero_le_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ start fuel,
      |quittingFiniteTerminalHazardValue reward roots who
        (fun time => roots time who) 0 start fuel| ≤
          quittingRewardBound reward := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      change |(0 : ℝ)| ≤ quittingRewardBound reward
      simpa using quittingRewardBound_nonneg reward
  | succ fuel ih =>
      rw [quittingFiniteTerminalHazardValue]
      rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward roots who
          (fun _ => quittingFiniteTerminalHazardValue reward roots who
            (fun time => roots time who) 0 (start + 1) fuel) start,
        ← quittingRootContinuePayoff_eq_fixedOpponents reward roots who
          (fun _ => quittingFiniteTerminalHazardValue reward roots who
            (fun time => roots time who) 0 (start + 1) fuel) start,
        ← quittingRootSuccessorPayoff_eq_endpointMix]
      exact abs_quittingRootExpectedPayoff_le_bound reward
        (fun _ => quittingFiniteTerminalHazardValue reward roots who
          (fun time => roots time who) 0 (start + 1) fuel)
        (roots start) who (abs_reward_le_quittingRewardBound reward)
        (fun _ => ih (start + 1))

/-- All five scalar coordinates of every actual finite block lie in one
fixed product box: payoff coordinates in `[-M,M]` and both survival
coordinates in `[0,1]`. -/
theorem quittingFiniteBoundaryHolonomy_coordinates_bounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) (who : ι) :
    |QuittingAffineSummary.intercept
        (QuittingBoundaryHolonomy.prescribed
          (quittingFiniteBoundaryHolonomy reward roots start extra) who)| ≤
            quittingRewardBound reward ∧
    QuittingAffineSummary.survival
        (QuittingBoundaryHolonomy.prescribed
          (quittingFiniteBoundaryHolonomy reward roots start extra) who) ≤ 1 ∧
    |QuittingMaxAffineSummary.early
        (QuittingBoundaryHolonomy.bestResponse
          (quittingFiniteBoundaryHolonomy reward roots start extra) who)| ≤
            quittingRewardBound reward ∧
    |QuittingMaxAffineSummary.tail
        (QuittingBoundaryHolonomy.bestResponse
          (quittingFiniteBoundaryHolonomy reward roots start extra) who)| ≤
            quittingRewardBound reward ∧
    QuittingMaxAffineSummary.survival
        (QuittingBoundaryHolonomy.bestResponse
          (quittingFiniteBoundaryHolonomy reward roots start extra) who) ≤ 1 := by
  rw [quittingFiniteBoundaryHolonomy_prescribed_intercept,
    quittingFiniteBoundaryHolonomy_prescribed_survival,
    quittingFiniteBoundaryHolonomy_bestResponse_early,
    quittingFiniteBoundaryHolonomy_bestResponse_tail,
    quittingFiniteBoundaryHolonomy_bestResponse_survival]
  exact ⟨
    abs_quittingFiniteTerminalHazardValue_self_zero_le_rewardBound
      reward roots who start (extra + 1),
    (quittingFiniteFullSurvivalWeight_le_opponentSurvivalWeight
      roots who (fun time => roots time who) start (extra + 1)).trans
        (quittingOpponentSurvivalWeight_le_one roots who start (extra + 1)),
    abs_quittingFiniteEarlyBestResponseValue_le_rewardBound
      reward roots who start extra,
    abs_quittingFiniteContinueToBoundaryValue_zero_le_rewardBound
      reward roots who start (extra + 1),
    quittingOpponentSurvivalWeight_le_one roots who start (extra + 1)⟩

/-! ### Compact coefficient envelope -/

/-- Raw Euclidean coordinates `(B,P)` and `(A,T,χ)` for all players.  This
forgets the source chain and is used only for compact coefficient extraction.
-/
abbrev QuittingBoundaryHolonomyCoordinates (ι : Type) :=
  (ι → ℝ × ℝ) × (ι → ℝ × (ℝ × ℝ))

/-- Forget a bundled holonomy to its five real coordinates. -/
def QuittingBoundaryHolonomy.coordinates
    (holonomy : QuittingBoundaryHolonomy ι) :
    QuittingBoundaryHolonomyCoordinates ι :=
  (fun who =>
    ((holonomy.prescribed who).intercept,
      (holonomy.prescribed who).survival),
   fun who =>
    ((holonomy.bestResponse who).early,
      ((holonomy.bestResponse who).tail,
        (holonomy.bestResponse who).survival)))

/-- The fixed product box containing the coefficients of every actual
finite block with reward bound `M`. -/
def quittingBoundaryHolonomyCoefficientBox (ι : Type) (M : ℝ) :
    Set (QuittingBoundaryHolonomyCoordinates ι) :=
  (Set.univ.pi (fun _ => Set.Icc (-M) M ×ˢ Set.Icc 0 1)) ×ˢ
    (Set.univ.pi (fun _ =>
      Set.Icc (-M) M ×ˢ (Set.Icc (-M) M ×ˢ Set.Icc 0 1)))

/-- The coefficient envelope is compact.  This is compactness of the
finite-dimensional scalar image, not closedness of the subset realized by
actual finite chains. -/
theorem isCompact_quittingBoundaryHolonomyCoefficientBox
    (ι : Type) (M : ℝ) :
    IsCompact (quittingBoundaryHolonomyCoefficientBox ι M) := by
  simpa [quittingBoundaryHolonomyCoefficientBox] using
    (isCompact_Icc : IsCompact
      (Set.Icc
        ((fun _ : ι => (-(M), (0 : ℝ))),
          fun _ : ι => (-(M), (-(M), (0 : ℝ))))
        ((fun _ : ι => (M, (1 : ℝ))),
          fun _ : ι => (M, (M, (1 : ℝ))))))

/-- Every holonomy extracted from an actual finite root block belongs to the
common compact coefficient envelope. -/
theorem quittingFiniteBoundaryHolonomy_coordinates_mem_box
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ) :
    (quittingFiniteBoundaryHolonomy reward roots start extra).coordinates ∈
      quittingBoundaryHolonomyCoefficientBox ι
        (quittingRewardBound reward) := by
  refine ⟨?_, ?_⟩
  · intro who _
    obtain ⟨hB, hP, _, _, _⟩ :=
      quittingFiniteBoundaryHolonomy_coordinates_bounded
        reward roots start extra who
    have hB' := abs_le.mp hB
    exact ⟨hB',
      ⟨QuittingAffineSummary.survival_nonneg
        (QuittingBoundaryHolonomy.prescribed
          (quittingFiniteBoundaryHolonomy reward roots start extra) who),
        hP⟩⟩
  · intro who _
    obtain ⟨_, _, hA, hT, hχ⟩ :=
      quittingFiniteBoundaryHolonomy_coordinates_bounded
        reward roots start extra who
    have hA' := abs_le.mp hA
    have hT' := abs_le.mp hT
    exact ⟨hA', ⟨hT',
      ⟨QuittingMaxAffineSummary.survival_nonneg
        (QuittingBoundaryHolonomy.bestResponse
          (quittingFiniteBoundaryHolonomy reward roots start extra) who),
        hχ⟩⟩⟩

/-! ## A calibrated terminal anchor and its realized middle blocks -/

/-- A selected min-max finite chain together with the positive terminal
packet supplied by its initial owner debt.  The finite path itself is the
canonical selected minimizer at cutoff `last + 1`; this makes minimizer
provenance definitional rather than an erasable assertion about an arbitrary
summary. -/
structure QuittingCalibratedTerminalAnchor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) [Nonempty ι] where
  last : ℕ
  owner : ι
  action : ι → Bool
  ownerDebt_pos : 0 < quittingFiniteNashBellmanPathDynamicDebt
    reward (last + 1)
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward (last + 1)) owner 0
  preterminalSurvival_pos : 0 < quittingOpponentSurvivalWeight
    (quittingFiniteNashBellmanPathRoots (last + 1)
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward (last + 1))) owner 0 last
  preterminalSurvival_le_one : quittingOpponentSurvivalWeight
    (quittingFiniteNashBellmanPathRoots (last + 1)
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward (last + 1))) owner 0 last ≤ 1
  terminalMass_pos : 0 < ((pmfPi (Function.update
    (quittingFiniteNashBellmanPathRoots (last + 1)
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward (last + 1)) last) owner (PMF.pure false))) action).toReal
  terminalMass_le_one : ((pmfPi (Function.update
    (quittingFiniteNashBellmanPathRoots (last + 1)
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward (last + 1)) last) owner (PMF.pure false))) action).toReal ≤ 1
  owner_continues : action owner = false
  terminalQuitters_nonempty : (quittingQuitters action).Nonempty
  terminalAdvantage_pos :
    0 < quittingTerminalOpponentAdvantage reward owner action
  debt_le_weighted_packet :
    quittingFiniteNashBellmanPathDynamicDebt
        reward (last + 1)
          (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
            reward (last + 1)) owner 0 ≤
      (Fintype.card (ι → Bool) : ℝ) *
        (quittingOpponentSurvivalWeight
          (quittingFiniteNashBellmanPathRoots (last + 1)
            (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
              reward (last + 1))) owner 0 last *
          ((pmfPi (Function.update
            (quittingFiniteNashBellmanPathRoots (last + 1)
              (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
                reward (last + 1)) last) owner
                  (PMF.pure false))) action).toReal) *
        quittingTerminalOpponentAdvantage reward owner action

namespace QuittingCalibratedTerminalAnchor

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The actual selected minimizing chain retained by the anchor. -/
def path [Nonempty ι]
    (anchor : QuittingCalibratedTerminalAnchor reward) :
    QuittingFiniteNashBellmanPath ι (anchor.last + 1) :=
  quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
    reward (anchor.last + 1)

/-- Its common family of product roots. -/
def roots [Nonempty ι]
    (anchor : QuittingCalibratedTerminalAnchor reward) :
    ℕ → ι → PMF Bool :=
  quittingFiniteNashBellmanPathRoots (anchor.last + 1) anchor.path

/-- Exact-D annotation of every displayed time. -/
def debtPoint [Nonempty ι]
    (anchor : QuittingCalibratedTerminalAnchor reward) (time : ℕ) :
    QuittingDebtPoint ι :=
  quittingFiniteNashBellmanPathDynamicDebtPoint reward
    (anchor.last + 1) anchor.path time

/-- The full marked terminal quitter set, kept alongside its action. -/
def terminalQuitters [Nonempty ι]
    (anchor : QuittingCalibratedTerminalAnchor reward) : Finset ι :=
  quittingQuitters anchor.action

/-- The preterminal clock excludes the final live root. -/
def preterminalSurvival [Nonempty ι]
    (anchor : QuittingCalibratedTerminalAnchor reward) : ℝ :=
  quittingOpponentSurvivalWeight anchor.roots anchor.owner 0 anchor.last

/-- The final marked product atom is a separate factor at the last live
root. -/
def terminalMass [Nonempty ι]
    (anchor : QuittingCalibratedTerminalAnchor reward) : ℝ :=
  ((pmfPi (Function.update (anchor.roots anchor.last) anchor.owner
    (PMF.pure false))) anchor.action).toReal

/-- Every positive owner on the selected finite minimizer produces a
calibrated anchor with separated clock and terminal atom. -/
theorem exists_of_ownerDebt_pos [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) (owner : ι)
    (hpositive : 0 < quittingFiniteNashBellmanPathDynamicDebt
      reward (last + 1)
        (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
          reward (last + 1)) owner 0) :
    Nonempty (QuittingCalibratedTerminalAnchor reward) := by
  let selected :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
      reward (last + 1)
  have hselected : selected ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (last + 1) :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward (last + 1)
  obtain ⟨action, hsurvival0, hsurvival1, hmass0, hmass1,
      howner, hquitters, hadvantage, hweighted, _, _⟩ :=
    exists_finiteDynamicDebt_separatedTerminalAnchor_quantitative
      reward last selected hselected owner hpositive
  exact ⟨{
    last := last
    owner := owner
    action := action
    ownerDebt_pos := hpositive
    preterminalSurvival_pos := hsurvival0
    preterminalSurvival_le_one := hsurvival1
    terminalMass_pos := hmass0
    terminalMass_le_one := hmass1
    owner_continues := howner
    terminalQuitters_nonempty := hquitters
    terminalAdvantage_pos := hadvantage
    debt_le_weighted_packet := hweighted }⟩

end QuittingCalibratedTerminalAnchor

/-- A nonempty chronological block cut from one calibrated minimizing chain.
The source anchor retains all roots and terminal-packet data; only the two
natural indices vary. -/
structure QuittingAnchoredBoundaryBlock [Nonempty ι]
    (anchor : QuittingCalibratedTerminalAnchor reward) where
  start : ℕ
  extra : ℕ
  within : start + (extra + 1) ≤ anchor.last + 1

namespace QuittingAnchoredBoundaryBlock

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Number of actual game stages in the block. -/
def length [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) : ℕ :=
  block.extra + 1

/-- Entry exact-D point. -/
def entry [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) : QuittingDebtPoint ι :=
  anchor.debtPoint block.start

/-- Exit exact-D point. -/
def exit [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) : QuittingDebtPoint ι :=
  anchor.debtPoint (block.start + block.length)

/-- The multi-player holonomy extracted from the block's actual roots. -/
def holonomy [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) :
    QuittingBoundaryHolonomy ι :=
  quittingFiniteBoundaryHolonomy reward anchor.roots block.start block.extra

/-- Every displayed transition in the block is a literal exact dynamic-debt
edge of its source minimizing chain. -/
theorem exactDebtEdge [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor)
    (offset : ℕ) (hoffset : offset < block.length) :
    IsQuittingDynamicDebtEdge reward
      (anchor.debtPoint (block.start + offset))
      (anchor.debtPoint (block.start + offset + 1)) := by
  apply quittingFiniteNashBellmanPathDynamicDebtPoint_edge
    reward (anchor.last + 1) anchor.path
    (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward (anchor.last + 1))
  have hwithin := block.within
  change offset < block.extra + 1 at hoffset
  omega

/-- The prescribed evaluation of a realized block is exact. -/
theorem prescribed_eval [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor)
    (who : ι) (terminalValue : ℝ) :
    (block.holonomy.prescribed who).eval terminalValue =
      quittingFiniteTerminalHazardValue reward anchor.roots who
        (fun time => anchor.roots time who) terminalValue
        block.start block.length := by
  exact quittingFiniteBoundaryHolonomy_prescribed_eval
    reward anchor.roots block.start block.extra who terminalValue

/-- The arbitrary-behavior unilateral Bellman value of a realized block is
exactly its max-affine evaluation. -/
theorem bestResponse_eval [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor)
    (who : ι) (terminalValue : ℝ) :
    (block.holonomy.bestResponse who).eval terminalValue =
      quittingFiniteTerminalBestResponseValue reward anchor.roots who
        terminalValue block.start block.length := by
  exact quittingFiniteBoundaryHolonomy_bestResponse_eval
    reward anchor.roots block.start block.extra who terminalValue

/-- Chronological concatenation inside one calibrated chain.  The equality
of seam indices is an explicit splice-admissibility premise. -/
def concat [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : QuittingAnchoredBoundaryBlock anchor)
    (hadjacent : inner.start = outer.start + outer.length) :
    QuittingAnchoredBoundaryBlock anchor where
  start := outer.start
  extra := outer.extra + inner.extra + 1
  within := by
    have hinner := inner.within
    change inner.start = outer.start + (outer.extra + 1) at hadjacent
    omega

/-- Concatenation has the expected actual length. -/
@[simp] theorem length_concat [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : QuittingAnchoredBoundaryBlock anchor)
    (hadjacent : inner.start = outer.start + outer.length) :
    (outer.concat inner hadjacent).length = outer.length + inner.length := by
  simp [concat, length]
  omega

/-- The exact-D seam matches literally. -/
theorem exit_eq_entry_of_adjacent [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : QuittingAnchoredBoundaryBlock anchor)
    (hadjacent : inner.start = outer.start + outer.length) :
    outer.exit = inner.entry := by
  unfold exit entry
  change inner.start = outer.start + (outer.extra + 1) at hadjacent
  rw [hadjacent]
  rfl

/-- **Realized chronological composition.**  Concatenating adjacent actual
blocks multiplies their bundled multi-player holonomies. -/
theorem holonomy_concat [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : QuittingAnchoredBoundaryBlock anchor)
    (hadjacent : inner.start = outer.start + outer.length) :
    (outer.concat inner hadjacent).holonomy =
      outer.holonomy * inner.holonomy := by
  change quittingFiniteBoundaryHolonomy reward anchor.roots outer.start
      (outer.extra + inner.extra + 1) =
    quittingFiniteBoundaryHolonomy reward anchor.roots outer.start
        outer.extra *
      quittingFiniteBoundaryHolonomy reward anchor.roots inner.start
        inner.extra
  rw [quittingFiniteBoundaryHolonomy_concat]
  change inner.start = outer.start + (outer.extra + 1) at hadjacent
  rw [hadjacent]
  rfl

end QuittingAnchoredBoundaryBlock

end GameTheory
