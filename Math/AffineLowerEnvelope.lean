/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Attained lower envelopes of affine functions

An attained pointwise minimum of real affine functions is concave.  If all
slopes are nonnegative, it is monotone; if the slopes lie in a common interval
`[0, C]`, it is `C`-Lipschitz.
-/

open Set
open scoped NNReal

namespace Math

/-- `v` is the attained pointwise minimum of the affine functions
`c ↦ intercept i + c * slope i`. -/
def IsAffineLowerEnvelope {ι : Type*} (intercept slope : ι → ℝ) (v : ℝ → ℝ) : Prop :=
  ∀ c, ∃ i, v c = intercept i + c * slope i ∧
    ∀ j, v c ≤ intercept j + c * slope j

namespace IsAffineLowerEnvelope

variable {ι : Type*} {intercept slope : ι → ℝ} {v : ℝ → ℝ}

/-- A lower envelope of affine functions with nonnegative slopes is monotone. -/
theorem monotone (h : IsAffineLowerEnvelope intercept slope v)
    (hslope : ∀ i, 0 ≤ slope i) : Monotone v := by
  intro c d hcd
  obtain ⟨i, hi, -⟩ := h d
  calc
    v c ≤ intercept i + c * slope i := (h c).choose_spec.2 i
    _ ≤ intercept i + d * slope i := by
      simpa only [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_right hcd (hslope i)) (intercept i)
    _ = v d := hi.symm

/-- An attained lower envelope of affine functions is concave. -/
theorem concaveOn_univ (h : IsAffineLowerEnvelope intercept slope v) :
    ConcaveOn ℝ univ v := by
  refine ⟨convex_univ, ?_⟩
  intro c _ d _ a b ha hb hab
  obtain ⟨i, hi, -⟩ := h (a • c + b • d)
  have hc := (h c).choose_spec.2 i
  have hd := (h d).choose_spec.2 i
  simp only [smul_eq_mul] at hi ⊢
  calc
    a * v c + b * v d ≤
        a * (intercept i + c * slope i) + b * (intercept i + d * slope i) := by
      gcongr
    _ = intercept i + (a * c + b * d) * slope i := by
      linear_combination (intercept i) * hab
    _ = v (a * c + b * d) := hi.symm

/-- A lower envelope whose slopes lie in `[0, C]` is `C`-Lipschitz. -/
theorem lipschitzWith (h : IsAffineLowerEnvelope intercept slope v) (C : ℝ≥0)
    (hslope : ∀ i, slope i ∈ Icc 0 (C : ℝ)) : LipschitzWith C v := by
  have hmono : Monotone v := h.monotone fun i => (hslope i).1
  have hchange {c d : ℝ} (hcd : c ≤ d) : v d - v c ≤ C * (d - c) := by
    obtain ⟨i, hi, -⟩ := h c
    have hd := (h d).choose_spec.2 i
    calc
      v d - v c ≤ (intercept i + d * slope i) -
          (intercept i + c * slope i) := by rw [hi]; gcongr
      _ = slope i * (d - c) := by ring
      _ ≤ C * (d - c) := by
        exact mul_le_mul_of_nonneg_right (hslope i).2 (sub_nonneg.mpr hcd)
  apply LipschitzWith.of_dist_le_mul
  intro c d
  simp only [Real.dist_eq]
  rcases le_total c d with hcd | hdc
  · rw [abs_of_nonpos (sub_nonpos.mpr (hmono hcd)), abs_of_nonpos (sub_nonpos.mpr hcd)]
    simpa only [neg_sub] using hchange hcd
  · rw [abs_of_nonneg (sub_nonneg.mpr (hmono hdc)), abs_of_nonneg (sub_nonneg.mpr hdc)]
    exact hchange hdc

end IsAffineLowerEnvelope

end Math
