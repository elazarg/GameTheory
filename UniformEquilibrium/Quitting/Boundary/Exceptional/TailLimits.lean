/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.SequencePayoff

/-!
# Positive exceptional survival and summable Bellman residuals

This file isolates the analytic limit facts needed by the exceptional-clock
branch.  Finite opponent-survival products split exactly at every cutoff.
Thus, if the products from time zero converge to a positive limit, every
finite prefix is strictly positive, the conditional tail product has the
corresponding quotient as its limit, and those quotients converge to one.

The same positive limiting survival gives a uniform lower bound on the
weights.  Consequently, summability of nonnegative weighted residuals
implies summability, and hence convergence to zero, of the residuals
themselves.  No conclusion is inferred past a zero factor: positivity is
derived from the explicitly assumed positive global limit.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Opponent-survival products split exactly into a prefix and the tail
starting after that prefix. -/
theorem quittingOpponentSurvivalWeight_add
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (start cutoff suffix : ℕ) :
    quittingOpponentSurvivalWeight roots who start (cutoff + suffix) =
      quittingOpponentSurvivalWeight roots who start cutoff *
        quittingOpponentSurvivalWeight roots who (start + cutoff) suffix := by
  induction suffix with
  | zero =>
      simp [quittingOpponentSurvivalWeight]
  | succ suffix ih =>
      rw [Nat.add_succ, quittingOpponentSurvivalWeight_succ, ih,
        quittingOpponentSurvivalWeight_succ]
      simp only [Nat.add_assoc]
      ring

/-- For fixed starting time, finite opponent survival is antitone in the
horizon. -/
theorem antitone_quittingOpponentSurvivalWeight
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    Antitone (quittingOpponentSurvivalWeight roots who start) := by
  apply antitone_nat_of_succ_le
  intro fuel
  rw [quittingOpponentSurvivalWeight_succ]
  exact mul_le_of_le_one_right
    (quittingOpponentSurvivalWeight_nonneg roots who start fuel)
    (quittingStationaryContinueMass_le_one
      (Function.update (roots (start + fuel)) who (PMF.pure false)))

/-- A limit of the time-zero survival products lies below every finite
prefix. -/
theorem quittingOpponentSurvivalLimit_le_prefix
    (roots : ℕ → ι → PMF Bool) (who : ι) (limit : ℝ)
    (hlimit : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds limit))
    (cutoff : ℕ) :
    limit ≤ quittingOpponentSurvivalWeight roots who 0 cutoff := by
  have hshift : Tendsto (fun suffix =>
      quittingOpponentSurvivalWeight roots who 0 (suffix + cutoff))
      atTop (nhds limit) :=
    hlimit.comp (tendsto_add_atTop_nat cutoff)
  apply le_of_tendsto' hshift
  intro suffix
  exact antitone_quittingOpponentSurvivalWeight roots who 0
    (Nat.le_add_left cutoff suffix)

/-- A positive limiting opponent-survival probability rules out a zero in
every finite prefix. -/
theorem quittingOpponentSurvivalWeight_pos_of_limit_pos
    (roots : ℕ → ι → PMF Bool) (who : ι) (limit : ℝ)
    (hlimit : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds limit))
    (hlimitPos : 0 < limit) (cutoff : ℕ) :
    0 < quittingOpponentSurvivalWeight roots who 0 cutoff :=
  hlimitPos.trans_le
    (quittingOpponentSurvivalLimit_le_prefix roots who limit hlimit cutoff)

/-- Under positive global survival, the opponent-survival products after a
fixed live cutoff converge to the quotient of the global limit by the
surviving prefix. -/
theorem tendsto_quittingOpponentSurvivalWeight_tail
    (roots : ℕ → ι → PMF Bool) (who : ι) (limit : ℝ)
    (hlimit : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds limit))
    (hlimitPos : 0 < limit) (start : ℕ) :
    Tendsto (quittingOpponentSurvivalWeight roots who start) atTop
      (nhds (limit /
        quittingOpponentSurvivalWeight roots who 0 start)) := by
  have hprefixNe :
      quittingOpponentSurvivalWeight roots who 0 start ≠ 0 :=
    ne_of_gt (quittingOpponentSurvivalWeight_pos_of_limit_pos
      roots who limit hlimit hlimitPos start)
  have hshift : Tendsto (fun fuel =>
      quittingOpponentSurvivalWeight roots who 0 (fuel + start))
      atTop (nhds limit) :=
    hlimit.comp (tendsto_add_atTop_nat start)
  have hquotient := hshift.div_const
    (quittingOpponentSurvivalWeight roots who 0 start)
  apply hquotient.congr'
  filter_upwards [] with fuel
  rw [show fuel + start = start + fuel by omega,
    quittingOpponentSurvivalWeight_add]
  field_simp
  simp

/-- The limiting conditional tail-survival probabilities converge to one as
the live cutoff goes to infinity. -/
theorem tendsto_quittingOpponentSurvivalLimitRatio_one
    (roots : ℕ → ι → PMF Bool) (who : ι) (limit : ℝ)
    (hlimit : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds limit))
    (hlimitPos : 0 < limit) :
    Tendsto (fun start => limit /
      quittingOpponentSurvivalWeight roots who 0 start)
      atTop (nhds 1) := by
  have hconst : Tendsto (fun _ : ℕ => limit) atTop (nhds limit) :=
    tendsto_const_nhds
  have hquotient := hconst.div hlimit (ne_of_gt hlimitPos)
  simpa only [Pi.div_def, div_self hlimitPos.ne'] using hquotient

/-- Positive limiting opponent survival removes the weights from a
summable nonnegative residual sequence. -/
theorem summable_of_summable_quittingOpponentSurvivalWeight_mul
    (roots : ℕ → ι → PMF Bool) (who : ι) (limit : ℝ)
    (residual : ℕ → ℝ)
    (hlimit : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds limit))
    (hlimitPos : 0 < limit)
    (hresidual : ∀ time, 0 ≤ residual time)
    (hsummable : Summable (fun time =>
      quittingOpponentSurvivalWeight roots who 0 time * residual time)) :
    Summable residual := by
  have hscaled : Summable (fun time => limit⁻¹ *
      (quittingOpponentSurvivalWeight roots who 0 time * residual time)) :=
    Summable.mul_left limit⁻¹ hsummable
  refine hscaled.of_nonneg_of_le hresidual ?_
  intro time
  have hlower := quittingOpponentSurvivalLimit_le_prefix
    roots who limit hlimit time
  have hmul : limit * residual time ≤
      quittingOpponentSurvivalWeight roots who 0 time * residual time :=
    mul_le_mul_of_nonneg_right hlower (hresidual time)
  calc
    residual time = limit⁻¹ * (limit * residual time) := by
      field_simp
    _ ≤ limit⁻¹ *
        (quittingOpponentSurvivalWeight roots who 0 time * residual time) :=
      mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hlimitPos.le)

/-- In particular, a nonnegative residual sequence with finite weighted sum
vanishes along an exceptional positive-survival clock. -/
theorem tendsto_zero_of_summable_quittingOpponentSurvivalWeight_mul
    (roots : ℕ → ι → PMF Bool) (who : ι) (limit : ℝ)
    (residual : ℕ → ℝ)
    (hlimit : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds limit))
    (hlimitPos : 0 < limit)
    (hresidual : ∀ time, 0 ≤ residual time)
    (hsummable : Summable (fun time =>
      quittingOpponentSurvivalWeight roots who 0 time * residual time)) :
    Tendsto residual atTop (nhds 0) :=
  Summable.tendsto_atTop_zero
    (summable_of_summable_quittingOpponentSurvivalWeight_mul
      roots who limit residual hlimit hlimitPos hresidual hsummable)

end GameTheory
