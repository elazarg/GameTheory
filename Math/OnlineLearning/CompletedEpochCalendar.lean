/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.OnlineLearning.UniversalCalendar
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Deterministic completed-epoch estimates

This file records the deterministic asymptotic core of completed-epoch
activation arguments.  For the universal scale

`λₖ = 1 / log (k + exp 2)`

and quadratic epoch length `Lₖ = (k + 1)²`, it proves two facts.

* Every fixed finite inverse power of `λₖ`, divided by `sqrt (k + 1)`,
  tends to zero.
* If a switching complexity is `O((k + 1)^(2 - ε))` for some `ε > 0`,
  then its normalized tracking cost, including every fixed logarithmic
  power, tends to zero.

The second statement uses the filter-level definition of bounded big-O:
the normalized switching complexity need only be eventually norm-bounded.
No horizon, probability law, or activation rule occurs here.
-/

namespace Math.OnlineLearning

open Filter Topology

noncomputable section

/-- The real-valued quadratic epoch length. -/
def completedEpochLength (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ (2 : ℝ)

/-- The confidence-to-signal ratio at a completed quadratic epoch. -/
def completedEpochBoundarySignalRatio (p : ℝ) (k : ℕ) : ℝ :=
  universalEpochScale k ^ (-p) / Real.sqrt (k + 1)

/-- The universal scale defeats the confidence cost for every fixed finite
signal order. -/
theorem tendsto_completedEpochBoundarySignalRatio (p : ℝ) :
    Tendsto (completedEpochBoundarySignalRatio p) atTop (𝓝 0) := by
  exact tendsto_scale_neg_rpow_div_sqrt_succ p

private theorem calendarArgument_rpow_isBigO_succ_rpow
    (s : ℝ) (hs : 0 < s) :
    (fun k : ℕ => universalCalendarArgument k ^ s) =O[atTop]
      (fun k : ℕ => ((k : ℝ) + 1) ^ s) := by
  have hbound :
      ∀ᶠ k : ℕ in atTop,
        ‖universalCalendarArgument k ^ s‖ ≤
          (Real.exp 2) ^ s * ‖((k : ℝ) + 1) ^ s‖ := by
    filter_upwards [] with k
    have hexp : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    have harg :
        universalCalendarArgument k ≤ Real.exp 2 * ((k : ℝ) + 1) := by
      rw [universalCalendarArgument]
      have hk : (0 : ℝ) ≤ k := by positivity
      nlinarith
    have hrpow :=
      Real.rpow_le_rpow (le_of_lt (universalCalendarArgument_pos k)) harg hs.le
    rw [Real.mul_rpow (by positivity) (by positivity)] at hrpow
    rw [Real.norm_of_nonneg
      (Real.rpow_nonneg (le_of_lt (universalCalendarArgument_pos k)) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact hrpow
  exact (Asymptotics.IsBigOWith.of_bound hbound).isBigO

/-- Every fixed real power of the calendar logarithm is negligible compared
with every positive real power of `k + 1`. -/
theorem tendsto_log_rpow_div_succ_rpow (p ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun k : ℕ =>
        Real.log (universalCalendarArgument k) ^ p /
          ((k : ℝ) + 1) ^ ε)
      atTop (𝓝 0) := by
  have hlog :
      (fun k : ℕ => Real.log (universalCalendarArgument k) ^ p) =o[atTop]
        (fun k : ℕ => universalCalendarArgument k ^ ε) :=
    (isLittleO_log_rpow_rpow_atTop p hε).comp_tendsto
      tendsto_universalCalendarArgument
  exact
    (hlog.trans_isBigO
      (calendarArgument_rpow_isBigO_succ_rpow ε hε)).tendsto_div_nhds_zero

/-- Scale form of `tendsto_log_rpow_div_succ_rpow`. -/
theorem tendsto_scale_neg_rpow_div_succ_rpow (p ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun k : ℕ =>
        universalEpochScale k ^ (-p) / ((k : ℝ) + 1) ^ ε)
      atTop (𝓝 0) := by
  simpa only [universalEpochScale_rpow_neg] using
    tendsto_log_rpow_div_succ_rpow p ε hε

/-- The conventional completed-epoch switch-cost ratio.  The numerator is a
switching complexity times the inverse signal scale; the denominator is the
quadratic epoch length. -/
def completedEpochSwitchRatio
    (switchComplexity : ℕ → ℝ) (p : ℝ) (k : ℕ) : ℝ :=
  switchComplexity k * universalEpochScale k ^ (-p) /
    completedEpochLength k

private theorem completedEpochSwitchRatio_factor
    (switchComplexity : ℕ → ℝ) (p ε : ℝ) (k : ℕ) :
    completedEpochSwitchRatio switchComplexity p k =
      (switchComplexity k / ((k : ℝ) + 1) ^ (2 - ε)) *
        (universalEpochScale k ^ (-p) / ((k : ℝ) + 1) ^ ε) := by
  rw [completedEpochSwitchRatio, completedEpochLength]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [div_mul_div_comm, ← Real.rpow_add hk]
  ring_nf

/-- A switching complexity of order at most `(k + 1)^(2 - ε)` has vanishing
completed-epoch cost after paying any fixed inverse power of the universal
signal scale.

The boundedness hypothesis is exactly the filter formulation of the stated
big-O condition. -/
theorem tendsto_completedEpochSwitchRatio_of_subquadratic
    (switchComplexity : ℕ → ℝ) (p ε : ℝ) (hε : 0 < ε)
    (hSwitch :
      IsBoundedUnder (· ≤ ·) atTop
        (norm ∘ fun k : ℕ =>
          switchComplexity k / ((k : ℝ) + 1) ^ (2 - ε))) :
    Tendsto (completedEpochSwitchRatio switchComplexity p) atTop (𝓝 0) := by
  have hscale :
      Tendsto
        (fun k : ℕ =>
          universalEpochScale k ^ (-p) / ((k : ℝ) + 1) ^ ε)
        atTop (𝓝 0) :=
    tendsto_scale_neg_rpow_div_succ_rpow p ε hε
  have hproduct :
      Tendsto
        (fun k : ℕ =>
          (switchComplexity k / ((k : ℝ) + 1) ^ (2 - ε)) *
            (universalEpochScale k ^ (-p) / ((k : ℝ) + 1) ^ ε))
        atTop (𝓝 0) :=
    Filter.isBoundedUnder_le_mul_tendsto_zero hSwitch hscale
  exact hproduct.congr' <|
    Filter.Eventually.of_forall fun k =>
      (completedEpochSwitchRatio_factor switchComplexity p ε k).symm

/-- Big-O interface to
`tendsto_completedEpochSwitchRatio_of_subquadratic`. -/
theorem tendsto_completedEpochSwitchRatio_of_isBigO
    (switchComplexity : ℕ → ℝ) (p ε : ℝ) (hε : 0 < ε)
    (hSwitch :
      switchComplexity =O[atTop]
        (fun k : ℕ => ((k : ℝ) + 1) ^ (2 - ε))) :
    Tendsto (completedEpochSwitchRatio switchComplexity p) atTop (𝓝 0) := by
  apply tendsto_completedEpochSwitchRatio_of_subquadratic
    switchComplexity p ε hε
  change
    IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ =>
        ‖switchComplexity k / ((k : ℝ) + 1) ^ (2 - ε)‖)
  exact Asymptotics.div_isBoundedUnder_of_isBigO hSwitch

end

end Math.OnlineLearning
