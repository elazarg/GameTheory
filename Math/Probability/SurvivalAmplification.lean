/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.DiscreteHazardStopping

/-!
# Survival amplification budgets

This module isolates a scalar mechanism shared by punishment and boundary
arguments.  A positive gap sequence is amplified across a discrete hazard if

`gap t ≤ (1 - hazard.stop t) * gap (t + 1)`.

If every gap is bounded above by `B`, the initial gap pays for the whole
additive hazard clock.  Finite survival products stay uniformly positive,
the division-free clock inequality

`gap start * sum hazard ≤ B`

holds at every horizon, and the suffix hazard is summable.  No game, Bellman,
or strategic semantics enter these statements.
-/

noncomputable section

namespace Math.Probability.DiscreteHazard.ScalarHazard

/-- Finite telescoping of a scalar survival-amplification inequality. -/
theorem gap_le_survival_mul
    (hazard : ScalarHazard) (gap : ℕ → ℝ)
    (hamplify : ∀ time,
      gap time ≤ (1 - hazard.stop time) * gap (time + 1))
    (start fuel : ℕ) :
    gap start ≤ hazard.survival start fuel * gap (start + fuel) := by
  induction fuel with
  | zero => simp [survival_zero]
  | succ fuel ih =>
      have hstage := hamplify (start + fuel)
      have hsurvival := survival_nonneg hazard start fuel
      calc
        gap start ≤ hazard.survival start fuel * gap (start + fuel) := ih
        _ ≤ hazard.survival start fuel *
            ((1 - hazard.stop (start + fuel)) *
              gap (start + fuel + 1)) :=
          mul_le_mul_of_nonneg_left hstage hsurvival
        _ = hazard.survival start (fuel + 1) *
            gap (start + (fuel + 1)) := by
          rw [survival_succ]
          rw [show start + fuel + 1 = start + (fuel + 1) by omega]
          ring

/-- A positive bounded amplified gap gives a uniform lower bound on every
finite survival product. -/
theorem gap_div_bound_le_survival
    (hazard : ScalarHazard) (gap : ℕ → ℝ) (bound : ℝ)
    (hgap_pos : ∀ time, 0 < gap time)
    (hgap_le : ∀ time, gap time ≤ bound)
    (hamplify : ∀ time,
      gap time ≤ (1 - hazard.stop time) * gap (time + 1))
    (start fuel : ℕ) :
    gap start / bound ≤ hazard.survival start fuel := by
  have hbound : 0 < bound := (hgap_pos start).trans_le (hgap_le start)
  rw [div_le_iff₀ hbound]
  exact (gap_le_survival_mul hazard gap hamplify start fuel).trans
    (mul_le_mul_of_nonneg_left (hgap_le (start + fuel))
      (survival_nonneg hazard start fuel))

/-- Division-free finite additive clock budget. -/
theorem gap_mul_sum_stop_le_bound
    (hazard : ScalarHazard) (gap : ℕ → ℝ) (bound : ℝ)
    (hgap_pos : ∀ time, 0 < gap time)
    (hgap_le : ∀ time, gap time ≤ bound)
    (hamplify : ∀ time,
      gap time ≤ (1 - hazard.stop time) * gap (time + 1))
    (start fuel : ℕ) :
    gap start *
        (∑ offset ∈ Finset.range fuel, hazard.stop (start + offset)) ≤
      bound := by
  have hbound : 0 < bound := (hgap_pos start).trans_le (hgap_le start)
  have hraw : ∀ offset,
      gap start ≤ hazard.survival start offset * bound := by
    intro offset
    exact (gap_le_survival_mul hazard gap hamplify start offset).trans
      (mul_le_mul_of_nonneg_left (hgap_le (start + offset))
        (survival_nonneg hazard start offset))
  have hstep : ∀ offset,
      gap start * hazard.stop (start + offset) ≤
        bound * (hazard.survival start offset -
          hazard.survival start (offset + 1)) := by
    intro offset
    have hstop := hazard.stop_nonneg (start + offset)
    rw [survival_succ]
    calc
      gap start * hazard.stop (start + offset) ≤
          (hazard.survival start offset * bound) *
            hazard.stop (start + offset) :=
        mul_le_mul_of_nonneg_right (hraw offset) hstop
      _ = bound *
          (hazard.survival start offset -
            hazard.survival start offset *
              (1 - hazard.stop (start + offset))) := by
        ring
  have htelescope := Finset.sum_range_sub'
    (fun offset => hazard.survival start offset) fuel
  have hsurvival := hazard.survival_nonneg start fuel
  rw [Finset.mul_sum]
  calc
    (∑ offset ∈ Finset.range fuel,
        gap start * hazard.stop (start + offset)) ≤
      ∑ offset ∈ Finset.range fuel,
        bound * (hazard.survival start offset -
          hazard.survival start (offset + 1)) :=
      Finset.sum_le_sum fun offset _ => hstep offset
    _ = bound * (1 - hazard.survival start fuel) := by
      rw [← Finset.mul_sum, htelescope, survival_zero hazard start]
    _ ≤ bound := by nlinarith

/-- Every suffix hazard is summable under positive bounded survival
amplification. -/
theorem summable_stop_natAdd_of_survivalAmplification
    (hazard : ScalarHazard) (gap : ℕ → ℝ) (bound : ℝ)
    (hgap_pos : ∀ time, 0 < gap time)
    (hgap_le : ∀ time, gap time ≤ bound)
    (hamplify : ∀ time,
      gap time ≤ (1 - hazard.stop time) * gap (time + 1))
    (start : ℕ) :
    Summable (fun offset => hazard.stop (start + offset)) := by
  have hgapStart : 0 < gap start := hgap_pos start
  apply summable_of_sum_range_le
    (c := bound / gap start) (fun offset => hazard.stop_nonneg _)
  intro fuel
  apply (le_div_iff₀ hgapStart).2
  rw [mul_comm]
  exact gap_mul_sum_stop_le_bound hazard gap bound hgap_pos hgap_le
    hamplify start fuel

/-- Division-free budget for the full suffix hazard. -/
theorem gap_mul_tsum_stop_natAdd_le_bound
    (hazard : ScalarHazard) (gap : ℕ → ℝ) (bound : ℝ)
    (hgap_pos : ∀ time, 0 < gap time)
    (hgap_le : ∀ time, gap time ≤ bound)
    (hamplify : ∀ time,
      gap time ≤ (1 - hazard.stop time) * gap (time + 1))
    (start : ℕ) :
    gap start * ∑' offset, hazard.stop (start + offset) ≤ bound := by
  let clock := fun offset => hazard.stop (start + offset)
  have hnonneg : ∀ offset, 0 ≤ gap start * clock offset := fun offset =>
    mul_nonneg (hgap_pos start).le (hazard.stop_nonneg _)
  have hbound : ∀ fuel,
      ∑ offset ∈ Finset.range fuel, gap start * clock offset ≤ bound := by
    intro fuel
    rw [← Finset.mul_sum]
    exact gap_mul_sum_stop_le_bound hazard gap bound hgap_pos hgap_le
      hamplify start fuel
  have htsum := Real.tsum_le_of_sum_range_le hnonneg hbound
  change gap start * ∑' offset, clock offset ≤ bound
  rw [← tsum_mul_left]
  exact htsum

/-- In particular, the whole hazard sequence is summable. -/
theorem summable_stop_of_survivalAmplification
    (hazard : ScalarHazard) (gap : ℕ → ℝ) (bound : ℝ)
    (hgap_pos : ∀ time, 0 < gap time)
    (hgap_le : ∀ time, gap time ≤ bound)
    (hamplify : ∀ time,
      gap time ≤ (1 - hazard.stop time) * gap (time + 1)) :
    Summable hazard.stop := by
  simpa using summable_stop_natAdd_of_survivalAmplification
    hazard gap bound hgap_pos hgap_le hamplify 0

end Math.Probability.DiscreteHazard.ScalarHazard
