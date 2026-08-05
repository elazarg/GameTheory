/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Deterministic contraction-error recurrence

This file isolates the elementary analytic kernel used in approximate
predictive compression.  If a nonnegative contraction factor `ρ < 1`, a
one-step additive error `δ`, and a sequence `error` satisfy

`error 0 ≤ δ` and `error (t + 1) ≤ ρ * error t + δ`,

then `error t` is bounded by a finite geometric sum and cumulative error up
to horizon `N` is at most `δ * N / (1 - ρ)`.

These are deterministic real inequalities.  They do not construct a causal
shadow-history transfer, a coupling, or a disintegration, and they do not
assert that arbitrary policies in two controlled models can be coupled.  A
predictive-compression theorem must establish the displayed one-step
recurrence separately before applying this module.
-/

namespace Math

namespace Probability

/-- The finite geometric envelope for an affine contraction recurrence. -/
def contractionErrorEnvelope (ρ δ : ℝ) (time : ℕ) : ℝ :=
  δ * ∑ lag ∈ Finset.range (time + 1), ρ ^ lag

@[simp] theorem contractionErrorEnvelope_zero (ρ δ : ℝ) :
    contractionErrorEnvelope ρ δ 0 = δ := by
  simp [contractionErrorEnvelope]

/-- The envelope satisfies the affine recurrence with equality. -/
theorem contractionErrorEnvelope_succ (ρ δ : ℝ) (time : ℕ) :
    contractionErrorEnvelope ρ δ (time + 1) =
      ρ * contractionErrorEnvelope ρ δ time + δ := by
  unfold contractionErrorEnvelope
  rw [show time + 1 + 1 = (time + 1) + 1 by omega,
    geom_sum_succ]
  ring

/-- Iterating the one-step affine contraction inequality gives the finite
geometric envelope. -/
theorem error_le_contractionErrorEnvelope
    (error : ℕ → ℝ) {ρ δ : ℝ} (hρ : 0 ≤ ρ)
    (hzero : error 0 ≤ δ)
    (hstep : ∀ time, error (time + 1) ≤ ρ * error time + δ) :
    ∀ time, error time ≤ contractionErrorEnvelope ρ δ time := by
  intro time
  induction time with
  | zero => simpa using hzero
  | succ time ih =>
      calc
        error (time + 1) ≤ ρ * error time + δ := hstep time
        _ ≤ ρ * contractionErrorEnvelope ρ δ time + δ := by
          simpa [add_comm] using
            (add_le_add_right (mul_le_mul_of_nonneg_left ih hρ) δ)
        _ = contractionErrorEnvelope ρ δ (time + 1) :=
          (contractionErrorEnvelope_succ ρ δ time).symm

/-- Closed form of the finite geometric envelope away from `ρ = 1`. -/
theorem contractionErrorEnvelope_eq_closedForm
    {ρ δ : ℝ} (hρ : ρ ≠ 1) (time : ℕ) :
    contractionErrorEnvelope ρ δ time =
      δ * (1 - ρ ^ (time + 1)) / (1 - ρ) := by
  have hden : 1 - ρ ≠ 0 := sub_ne_zero.mpr hρ.symm
  apply (eq_div_iff hden).2
  unfold contractionErrorEnvelope
  calc
    (δ * ∑ lag ∈ Finset.range (time + 1), ρ ^ lag) * (1 - ρ) =
        δ * ((∑ lag ∈ Finset.range (time + 1), ρ ^ lag) *
          (1 - ρ)) := by ring
    _ = δ * (1 - ρ ^ (time + 1)) := by
      rw [geom_sum_mul_neg]

/-- Pointwise closed-form error estimate for a strict affine contraction. -/
theorem error_le_contraction_closedForm
    (error : ℕ → ℝ) {ρ δ : ℝ} (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1)
    (hzero : error 0 ≤ δ)
    (hstep : ∀ time, error (time + 1) ≤ ρ * error time + δ)
    (time : ℕ) :
    error time ≤ δ * (1 - ρ ^ (time + 1)) / (1 - ρ) := by
  rw [← contractionErrorEnvelope_eq_closedForm hρlt.ne time]
  exact error_le_contractionErrorEnvelope error hρnonneg hzero hstep time

/-- A nonnegative strict-contraction envelope is uniformly bounded by the
infinite geometric bound `δ / (1 - ρ)`. -/
theorem contractionErrorEnvelope_le
    {ρ δ : ℝ} (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1) (hδ : 0 ≤ δ)
    (time : ℕ) :
    contractionErrorEnvelope ρ δ time ≤ δ / (1 - ρ) := by
  have hdenpos : 0 < 1 - ρ := sub_pos.mpr hρlt
  have hgeom :
      (∑ lag ∈ Finset.range (time + 1), ρ ^ lag) ≤ 1 / (1 - ρ) := by
    apply (le_div_iff₀ hdenpos).2
    rw [geom_sum_mul_neg]
    exact sub_le_self 1 (pow_nonneg hρnonneg _)
  unfold contractionErrorEnvelope
  calc
    δ * ∑ lag ∈ Finset.range (time + 1), ρ ^ lag ≤
        δ * (1 / (1 - ρ)) :=
      mul_le_mul_of_nonneg_left hgeom hδ
    _ = δ / (1 - ρ) := by ring

/-- Exact cumulative value of the finite geometric envelopes. -/
theorem sum_contractionErrorEnvelope_eq_closedForm
    {ρ δ : ℝ} (hρ : ρ ≠ 1) (horizon : ℕ) :
    ∑ time ∈ Finset.range horizon, contractionErrorEnvelope ρ δ time =
      δ * ((horizon : ℝ) / (1 - ρ) -
        ρ * (1 - ρ ^ horizon) / (1 - ρ) ^ 2) := by
  have hden : 1 - ρ ≠ 0 := sub_ne_zero.mpr hρ.symm
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [Finset.sum_range_succ, ih,
        contractionErrorEnvelope_eq_closedForm hρ]
      push_cast
      field_simp [hden]
      ring

/-- The sharper cumulative estimate retaining the finite geometric tail. -/
theorem sum_error_le_contraction_closedForm
    (error : ℕ → ℝ) {ρ δ : ℝ} (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1)
    (hzero : error 0 ≤ δ)
    (hstep : ∀ time, error (time + 1) ≤ ρ * error time + δ)
    (horizon : ℕ) :
    ∑ time ∈ Finset.range horizon, error time ≤
      δ * ((horizon : ℝ) / (1 - ρ) -
        ρ * (1 - ρ ^ horizon) / (1 - ρ) ^ 2) := by
  calc
    ∑ time ∈ Finset.range horizon, error time ≤
        ∑ time ∈ Finset.range horizon,
          contractionErrorEnvelope ρ δ time := by
      apply Finset.sum_le_sum
      intro time _
      exact error_le_contractionErrorEnvelope
        error hρnonneg hzero hstep time
    _ = δ * ((horizon : ℝ) / (1 - ρ) -
        ρ * (1 - ρ ^ horizon) / (1 - ρ) ^ 2) :=
      sum_contractionErrorEnvelope_eq_closedForm hρlt.ne horizon

/-- Uniform cumulative error bound through an arbitrary finite horizon. -/
theorem sum_error_le_contraction_bound
    (error : ℕ → ℝ) {ρ δ : ℝ} (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1)
    (hδ : 0 ≤ δ) (hzero : error 0 ≤ δ)
    (hstep : ∀ time, error (time + 1) ≤ ρ * error time + δ)
    (horizon : ℕ) :
    ∑ time ∈ Finset.range horizon, error time ≤
      δ * (horizon : ℝ) / (1 - ρ) := by
  calc
    ∑ time ∈ Finset.range horizon, error time ≤
        ∑ _time ∈ Finset.range horizon, δ / (1 - ρ) := by
      apply Finset.sum_le_sum
      intro time htime
      exact (error_le_contractionErrorEnvelope
        error hρnonneg hzero hstep time).trans
        (contractionErrorEnvelope_le hρnonneg hρlt hδ time)
    _ = δ * (horizon : ℝ) / (1 - ρ) := by
      simp
      ring

/-- Multiplying by a nonnegative Lipschitz constant gives the corresponding
cumulative reward-error estimate. -/
theorem mul_sum_error_le_contraction_bound
    (error : ℕ → ℝ) {ρ δ lipschitz : ℝ}
    (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1) (hδ : 0 ≤ δ)
    (hlipschitz : 0 ≤ lipschitz) (hzero : error 0 ≤ δ)
    (hstep : ∀ time, error (time + 1) ≤ ρ * error time + δ)
    (horizon : ℕ) :
    lipschitz * (∑ time ∈ Finset.range horizon, error time) ≤
      lipschitz * δ * (horizon : ℝ) / (1 - ρ) := by
  have hsum := sum_error_le_contraction_bound error hρnonneg hρlt hδ
    hzero hstep horizon
  have := mul_le_mul_of_nonneg_left hsum hlipschitz
  calc
    lipschitz * (∑ time ∈ Finset.range horizon, error time) ≤
        lipschitz * (δ * (horizon : ℝ) / (1 - ρ)) := this
    _ = lipschitz * δ * (horizon : ℝ) / (1 - ρ) := by ring

end Probability

end Math
