/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.SublinearLedger

/-!
# Realized-account deflation

Membership of a charge direction in a processed linear span is qualitative.
It does not by itself pay repeated occurrences of that direction.  The
additional datum needed for an accounting deflation is a realized account:
the processed charge at each stage is the increment of an account whose
endpoint motion is controlled.

This file states that interface, proves its telescoping bound, and gives the
minimal one-dimensional boundary.  The constant charge `1` lies in the full
processed span at every stage, but no bounded account realizes it.  Thus span
membership alone cannot close an already-processed branch of a recursive
response construction.
-/

namespace Math.Probability

open Finset

/-- A stage charge is realized by an account when it is exactly the
account's one-step increment. -/
def IsRealizedByAccount
    (charge account : ℕ → ℝ) : Prop :=
  ∀ t, charge t = account (t + 1) - account t

/-- Realized charges telescope to the net motion of their account. -/
theorem IsRealizedByAccount.sum_range_eq
    {charge account : ℕ → ℝ}
    (realized : IsRealizedByAccount charge account)
    (T : ℕ) :
    ∑ t ∈ Finset.range T, charge t =
      account T - account 0 := by
  induction T with
  | zero => simp
  | succ T inductionHypothesis =>
      rw [Finset.sum_range_succ, realized T,
        inductionHypothesis]
      ring

/-- A uniformly bounded realized account pays at most twice its bound over
every finite horizon. -/
theorem IsRealizedByAccount.abs_sum_range_le_two_mul
    {charge account : ℕ → ℝ}
    (realized : IsRealizedByAccount charge account)
    {bound : ℝ}
    (account_bounded : ∀ t, |account t| ≤ bound)
    (T : ℕ) :
    |∑ t ∈ Finset.range T, charge t| ≤ 2 * bound := by
  rw [realized.sum_range_eq]
  calc
    |account T - account 0| ≤
        |account T| + |account 0| := abs_sub _ _
    _ ≤ bound + bound :=
      add_le_add (account_bounded T) (account_bounded 0)
    _ = 2 * bound := by ring

/-- A bounded realized account makes its cumulative charge asymptotically
sublinear. -/
theorem IsRealizedByAccount.cumulative_isAsymptoticallySublinear
    {charge account : ℕ → ℝ}
    (realized : IsRealizedByAccount charge account)
    {bound : ℝ}
    (account_bounded : ∀ t, |account t| ≤ bound) :
    IsAsymptoticallySublinear
      (fun T => ∑ t ∈ Finset.range T, charge t) := by
  change Filter.Tendsto
    (fun T : ℕ =>
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, charge t)
    Filter.atTop (nhds 0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (g := fun T : ℕ => (T : ℝ)⁻¹ * (2 * bound))
  · filter_upwards with T
    exact norm_nonneg _
  · filter_upwards with T
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T))]
    exact mul_le_mul_of_nonneg_left
      (realized.abs_sum_range_le_two_mul account_bounded T)
      (inv_nonneg.mpr (Nat.cast_nonneg T))
  · exact IsAsymptoticallySublinear.const (2 * bound)

namespace ProcessedSpanCounterexample

/-- The smallest possible processed span: the whole one-dimensional real
space. -/
def processedSpan : Submodule ℝ ℝ := ⊤

/-- The recurring unit direction is already processed. -/
theorem one_mem_processedSpan :
    (1 : ℝ) ∈ processedSpan := by
  trivial

/-- Nevertheless the recurring unit charge has no uniformly bounded
realized account. -/
theorem not_exists_bounded_realizedAccount_constant_one :
    ¬ ∃ (account : ℕ → ℝ) (bound : ℝ),
      (∀ t, |account t| ≤ bound) ∧
      IsRealizedByAccount (fun _ => 1) account := by
  rintro ⟨account, bound, account_bounded, realized⟩
  obtain ⟨T, hT⟩ := exists_nat_gt (2 * bound)
  have hsum :=
    realized.abs_sum_range_le_two_mul account_bounded T
  have hcast : (T : ℝ) ≤ 2 * bound := by
    simpa using hsum
  exact (not_lt_of_ge hcast) hT

end ProcessedSpanCounterexample

end Math.Probability
