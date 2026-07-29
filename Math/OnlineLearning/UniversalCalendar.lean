/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.OnlineLearning.AnytimeMultiplicativeWeights
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# A universal logarithmic scale calendar

The quadratic epoch calendar from `AnytimeMultiplicativeWeights` can be paired
with the deterministic scale

`λₖ = 1 / log (k + exp 2)`.

This scale tends to zero, but more slowly than every fixed negative power of
the epoch index.  Consequently every fixed power of `log (k + exp 2)` is
negligible compared with `sqrt (k + 1)`.  This is the deterministic
asymptotic core needed when a signal has an unknown finite polynomial order
in `λₖ`, while an anytime boundary pays a `sqrt k` confidence cost.
-/

namespace Math.OnlineLearning

open Asymptotics Filter Topology

noncomputable section

/-- The shifted real epoch index used by the universal scale. -/
def universalCalendarArgument (k : ℕ) : ℝ := k + Real.exp 2

/-- A deterministic scale that tends to zero more slowly than every inverse
    polynomial in the epoch index. -/
def universalEpochScale (k : ℕ) : ℝ :=
  (Real.log (universalCalendarArgument k))⁻¹

theorem one_lt_universalCalendarArgument (k : ℕ) :
    1 < universalCalendarArgument k := by
  rw [universalCalendarArgument]
  have hexp : 1 < Real.exp 2 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 2)
  exact hexp.trans_le (le_add_of_nonneg_left (by positivity))

theorem universalCalendarArgument_pos (k : ℕ) :
    0 < universalCalendarArgument k :=
  (zero_lt_one.trans (one_lt_universalCalendarArgument k))

theorem universalEpochScale_pos (k : ℕ) :
    0 < universalEpochScale k := by
  rw [universalEpochScale]
  exact inv_pos.mpr (Real.log_pos (one_lt_universalCalendarArgument k))

theorem universalEpochScale_le_one (k : ℕ) :
    universalEpochScale k ≤ 1 := by
  rw [universalEpochScale]
  apply inv_le_one_of_one_le₀
  calc
    1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log (universalCalendarArgument k) :=
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
        (universalCalendarArgument_pos k)
        ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans
          (by
            rw [universalCalendarArgument]
            exact le_add_of_nonneg_left (by positivity)))

theorem tendsto_universalCalendarArgument :
    Tendsto universalCalendarArgument atTop atTop := by
  exact tendsto_atTop_add_const_right atTop (Real.exp 2)
    tendsto_natCast_atTop_atTop

theorem tendsto_universalEpochScale :
    Tendsto universalEpochScale atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_log_atTop.comp tendsto_universalCalendarArgument)

/-- Every fixed real power of the logarithm is negligible compared with any
    positive real power of the shifted epoch index. -/
theorem tendsto_log_rpow_div_calendarArgument_rpow
    (p s : ℝ) (hs : 0 < s) :
    Tendsto
      (fun k : ℕ =>
        Real.log (universalCalendarArgument k) ^ p /
          universalCalendarArgument k ^ s)
      atTop (𝓝 0) := by
  exact
    ((isLittleO_log_rpow_rpow_atTop p hs).comp_tendsto
      tendsto_universalCalendarArgument).tendsto_div_nhds_zero

private theorem calendarArgument_rpow_isBigO_sqrtSucc :
    (fun k : ℕ => universalCalendarArgument k ^ (1 / 2 : ℝ)) =O[atTop]
      (fun k : ℕ => Real.sqrt (k + 1)) := by
  have hbound :
      ∀ᶠ k : ℕ in atTop,
        ‖universalCalendarArgument k ^ (1 / 2 : ℝ)‖ ≤
          (Real.exp 2) ^ (1 / 2 : ℝ) * ‖Real.sqrt (k + 1)‖ := by
    filter_upwards [] with k
    have hexp : 1 ≤ Real.exp 2 := by
      exact Real.one_le_exp (by norm_num)
    have harg :
        universalCalendarArgument k ≤ Real.exp 2 * ((k : ℝ) + 1) := by
      rw [universalCalendarArgument]
      have hk : (0 : ℝ) ≤ k := by positivity
      nlinarith
    have hrpow :=
      Real.rpow_le_rpow (le_of_lt (universalCalendarArgument_pos k)) harg
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.mul_rpow (by positivity) (by positivity)] at hrpow
    rw [Real.norm_of_nonneg
      (Real.rpow_nonneg (le_of_lt (universalCalendarArgument_pos k)) _),
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [Real.sqrt_eq_rpow, Nat.cast_add, Nat.cast_one] using hrpow
  exact (IsBigOWith.of_bound hbound).isBigO

/-- The boundary-to-signal asymptotic at the quadratic epoch length:
    every fixed logarithmic power is `o(sqrt (k + 1))`. -/
theorem tendsto_log_rpow_div_sqrt_succ (p : ℝ) :
    Tendsto
      (fun k : ℕ =>
        Real.log (universalCalendarArgument k) ^ p / Real.sqrt (k + 1))
      atTop (𝓝 0) := by
  have hlog :
      (fun k : ℕ => Real.log (universalCalendarArgument k) ^ p) =o[atTop]
        (fun k : ℕ => universalCalendarArgument k ^ (1 / 2 : ℝ)) :=
    (isLittleO_log_rpow_rpow_atTop p (by norm_num)).comp_tendsto
      tendsto_universalCalendarArgument
  exact
    (hlog.trans_isBigO calendarArgument_rpow_isBigO_sqrtSucc).tendsto_div_nhds_zero

theorem universalEpochScale_rpow_neg (k : ℕ) (p : ℝ) :
    universalEpochScale k ^ (-p) =
      Real.log (universalCalendarArgument k) ^ p := by
  have hlog : 0 ≤ Real.log (universalCalendarArgument k) :=
    (Real.log_pos (one_lt_universalCalendarArgument k)).le
  rw [universalEpochScale, Real.inv_rpow hlog, Real.rpow_neg hlog]
  exact inv_inv _

/-- Direct scale formulation of the universal boundary-to-signal core:
    `λₖ⁻ᵖ / sqrt (k + 1) → 0` for every fixed finite exponent `p`. -/
theorem tendsto_scale_neg_rpow_div_sqrt_succ (p : ℝ) :
    Tendsto
      (fun k : ℕ =>
        universalEpochScale k ^ (-p) / Real.sqrt (k + 1))
      atTop (𝓝 0) := by
  simpa only [universalEpochScale_rpow_neg] using
    tendsto_log_rpow_div_sqrt_succ p

/-- Multiplicative constants in a signal lower bound do not affect the
    universal boundary-to-signal conclusion. -/
theorem tendsto_const_mul_scale_neg_rpow_div_sqrt_succ
    (C c p : ℝ) :
    Tendsto
      (fun k : ℕ =>
        (C / c) *
          (universalEpochScale k ^ (-p) / Real.sqrt (k + 1)))
      atTop (𝓝 0) := by
  simpa only [mul_zero] using
    (tendsto_scale_neg_rpow_div_sqrt_succ p).const_mul (C / c)

end

end Math.OnlineLearning
