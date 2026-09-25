/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace GameTheory.Math.Probability

universe u v

set_option autoImplicit false

private theorem tsum_cond_mul_left {α : Type u} (c : ENNReal) (f : α → ENNReal)
    (p : α → Prop) [DecidablePred p] :
    (∑' a, if p a then c * f a else 0) = c * ∑' a, if p a then f a else 0 := by
  calc
    (∑' a, if p a then c * f a else 0) =
        ∑' a, c * (if p a then f a else 0) := by
      apply tsum_congr
      intro a
      by_cases h : p a <;> simp [h]
    _ = c * ∑' a, if p a then f a else 0 := ENNReal.tsum_mul_left

/-- Mix two PMFs with weight `t` on the first law. -/
noncomputable def mix {α : Type u} (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (μ ν : PMF α) : PMF α :=
  ⟨fun a => ENNReal.ofReal t * μ a + ENNReal.ofReal (1 - t) * ν a,
    ENNReal.summable.hasSum_iff.2 (by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
        PMF.tsum_coe, PMF.tsum_coe, mul_one, mul_one,
        ← ENNReal.ofReal_add h0 (by linarith : 0 ≤ 1 - t)]
      norm_num)⟩

@[simp]
theorem mix_apply {α : Type u} (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (μ ν : PMF α) (a : α) :
    mix t h0 h1 μ ν a = ENNReal.ofReal t * μ a + ENNReal.ofReal (1 - t) * ν a := rfl

/-- Real atom mass of a convex mixture of ordinary PMFs. -/
theorem mix_apply_toReal {α : Type u} (t : ℝ)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : PMF α) (a : α) :
    (mix t h0 h1 μ ν a).toReal =
      t * (μ a).toReal + (1 - t) * (ν a).toReal := by
  rw [mix_apply, ENNReal.toReal_add]
  · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h0,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top μ a)
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top ν a)

@[simp]
theorem mix_self {α : Type u} (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (μ : PMF α) : mix t h0 h1 μ μ = μ := by
  ext a
  rw [mix_apply, ← add_mul, ← ENNReal.ofReal_add h0 (by linarith : 0 ≤ 1 - t)]
  norm_num

@[simp]
theorem mix_zero {α : Type u} (μ ν : PMF α) :
    mix 0 le_rfl (by norm_num) μ ν = ν := by
  ext a
  simp [mix_apply]

@[simp]
theorem mix_one {α : Type u} (μ ν : PMF α) :
    mix 1 (by norm_num) le_rfl μ ν = μ := by
  ext a
  simp [mix_apply]

/-- Exchanging the two laws also exchanges the mixture weights. -/
theorem mix_swap {α : Type u} (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (μ ν : PMF α) :
    mix (1 - t) (by linarith) (by linarith) ν μ = mix t h0 h1 μ ν := by
  ext a
  rw [mix_apply, mix_apply]
  have h : 1 - (1 - t) = t := by ring
  rw [h]
  ac_rfl

/-- Repeatedly mixing the same first law combines the two weights. -/
theorem mix_assoc_left {α : Type u} (q t : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (μ ν : PMF α) :
    mix (q + (1 - q) * t) (by nlinarith) (by nlinarith) μ ν =
      mix q hq0 hq1 μ (mix t ht0 ht1 μ ν) := by
  ext a
  rw [mix_apply, mix_apply, mix_apply]
  have hleft : ENNReal.ofReal (q + (1 - q) * t) =
      ENNReal.ofReal q + ENNReal.ofReal (1 - q) * ENNReal.ofReal t := by
    rw [ENNReal.ofReal_add hq0 (mul_nonneg (by linarith) ht0),
      ENNReal.ofReal_mul (by linarith : 0 ≤ 1 - q)]
  have hright : ENNReal.ofReal (1 - (q + (1 - q) * t)) =
      ENNReal.ofReal (1 - q) * ENNReal.ofReal (1 - t) := by
    have h : 1 - (q + (1 - q) * t) = (1 - q) * (1 - t) := by ring
    rw [h, ENNReal.ofReal_mul (by linarith : 0 ≤ 1 - q)]
  rw [hleft, hright]
  ring

theorem mix_map {α : Type u} {β : Type v} (t : ℝ) (h0 : 0 ≤ t)
    (h1 : t ≤ 1) (μ ν : PMF α) (f : α → β) :
    (mix t h0 h1 μ ν).map f = mix t h0 h1 (μ.map f) (ν.map f) := by
  classical
  ext b
  rw [PMF.map_apply]
  simp_rw [mix_apply]
  calc
    (∑' a, if b = f a then
      ENNReal.ofReal t * μ a + ENNReal.ofReal (1 - t) * ν a else 0) =
      (∑' a, if b = f a then ENNReal.ofReal t * μ a else 0) +
        ∑' a, if b = f a then ENNReal.ofReal (1 - t) * ν a else 0 := by
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro a
      by_cases h : b = f a <;> simp [h]
    _ = ENNReal.ofReal t * (∑' a, if b = f a then μ a else 0) +
        ENNReal.ofReal (1 - t) * (∑' a, if b = f a then ν a else 0) := by
      rw [tsum_cond_mul_left, tsum_cond_mul_left]
    _ = _ := by rw [PMF.map_apply, PMF.map_apply]

theorem mix_bind {α : Type u} {β : Type v} (t : ℝ) (h0 : 0 ≤ t)
    (h1 : t ≤ 1) (μ ν : PMF α) (f : α → PMF β) :
    (mix t h0 h1 μ ν).bind f = mix t h0 h1 (μ.bind f) (ν.bind f) := by
  classical
  ext b
  rw [PMF.bind_apply]
  calc
    (∑' a, (mix t h0 h1 μ ν) a * (f a) b) =
        ∑' a, (ENNReal.ofReal t * μ a + ENNReal.ofReal (1 - t) * ν a) *
          (f a) b := by
      apply tsum_congr
      intro a
      rw [mix_apply]
    _ = ∑' a, (ENNReal.ofReal t * (μ a * (f a) b) +
        ENNReal.ofReal (1 - t) * (ν a * (f a) b)) := by
      apply tsum_congr
      intro a
      rw [add_mul]
      ring
    _ = ENNReal.ofReal t * (∑' a, μ a * (f a) b) +
        ENNReal.ofReal (1 - t) * (∑' a, ν a * (f a) b) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ = _ := by rw [mix_apply, PMF.bind_apply, PMF.bind_apply]

theorem mem_support_mix_left {α : Type u} (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (ht : 0 < t) {μ ν : PMF α} {a : α} (ha : a ∈ μ.support) :
    a ∈ (mix t h0 h1 μ ν).support := by
  rw [PMF.mem_support_iff, mix_apply]
  apply ne_of_gt
  apply lt_of_lt_of_le
  · exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr ht).ne'
      ((μ.apply_pos_iff a).mpr ha).ne'
  · exact le_add_of_nonneg_right (by positivity)

/-- Positive weight on the second law preserves its supported outcomes. -/
theorem mem_support_mix_right {α : Type u} (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (ht : t < 1) {μ ν : PMF α} {a : α} (ha : a ∈ ν.support) :
    a ∈ (mix t h0 h1 μ ν).support := by
  rw [PMF.mem_support_iff, mix_apply]
  apply ne_of_gt
  apply lt_of_lt_of_le
  · have hweight : 0 < 1 - t := by linarith
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hweight).ne'
      ((ν.apply_pos_iff a).mpr ha).ne'
  · exact le_add_of_nonneg_left (by positivity)

theorem support_mix_eq_univ_of_left {α : Type u} (t : ℝ)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) (ht : 0 < t) {μ ν : PMF α}
    (hμ : μ.support = Set.univ) : (mix t h0 h1 μ ν).support = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro a
  apply mem_support_mix_left t h0 h1 ht
  rw [hμ]
  trivial

end GameTheory.Math.Probability
