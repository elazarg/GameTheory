/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-!
# Finite variation bounds for real sequences

Generic accounting lemmas controlling total variation from one-sided
increment bounds.
-/

open scoped BigOperators

namespace Math

/-- A finite sum of successive drops telescopes. -/
theorem sum_range_sub_succ (sequence : ℕ → ℝ) (horizon : ℕ) :
    ∑ index ∈ Finset.range horizon,
        (sequence index - sequence (index + 1)) =
      sequence 0 - sequence horizon := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- A bounded real sequence whose positive increments are charged to a
nonnegative clock has controlled finite total variation. -/
theorem sum_abs_succ_sub_le_of_bounded_of_increase_le_clock
    (value charge : ℕ → ℝ) (bound : ℝ)
    (hbound : ∀ time, |value time| ≤ bound)
    (hcharge : ∀ time, 0 ≤ charge time)
    (hincrease : ∀ time,
      value (time + 1) - value time ≤ 2 * bound * charge time)
    (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,
        |value (time + 1) - value time|) ≤
      2 * bound + 4 * bound *
        (∑ time ∈ Finset.range horizon, charge time) := by
  have hM : 0 ≤ bound := (abs_nonneg (value 0)).trans (hbound 0)
  have hpositive : ∀ time,
      max (value (time + 1) - value time) 0 ≤
        2 * bound * charge time := by
    intro time
    exact max_le (hincrease time)
      (mul_nonneg (mul_nonneg (by norm_num) hM) (hcharge time))
  have hsumPositive :
      (∑ time ∈ Finset.range horizon,
          max (value (time + 1) - value time) 0) ≤
        2 * bound * (∑ time ∈ Finset.range horizon, charge time) := by
    calc
      (∑ time ∈ Finset.range horizon,
          max (value (time + 1) - value time) 0) ≤
          ∑ time ∈ Finset.range horizon, 2 * bound * charge time :=
        Finset.sum_le_sum fun time _ => hpositive time
      _ = 2 * bound * (∑ time ∈ Finset.range horizon, charge time) := by
        rw [Finset.mul_sum]
  have habsIdentity : ∀ x : ℝ, |x| = 2 * max x 0 - x := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_left hx]
      ring
    · have hx' : x ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hx', max_eq_right hx']
      ring
  have htelescope :
      (∑ time ∈ Finset.range horizon,
          (value (time + 1) - value time)) =
        value horizon - value 0 :=
    Finset.sum_range_sub value horizon
  have hspan : value 0 - value horizon ≤ 2 * bound := by
    have h0 := (abs_le.mp (hbound 0)).2
    have hN := (abs_le.mp (hbound horizon)).1
    linarith
  rw [Finset.sum_congr rfl (fun time _ => habsIdentity _),
    Finset.sum_sub_distrib, ← Finset.mul_sum, htelescope]
  linarith

end Math
