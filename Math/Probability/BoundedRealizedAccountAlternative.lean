/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.RealizedAccountDeflation

/-!
# Exact alternative for bounded realized accounts

A processed direction can be discharged by a bounded account exactly when
its realized cumulative charge is bounded.  The canonical account is the
partial-sum process itself.  If those partial sums are not bounded, every
account realizing the charge is necessarily unbounded.

This is the sharp extra hypothesis missing from qualitative processed-span
membership.  The file also records closure under finite linear combinations:
processed basis directions can be combined only when their charge
decomposition is realized by the same coefficients.
-/

namespace Math.Probability

open Finset

/-- The canonical account of a stage charge is its cumulative partial sum. -/
def cumulativeChargeAccount (charge : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, charge t

@[simp]
theorem cumulativeChargeAccount_zero (charge : ℕ → ℝ) :
    cumulativeChargeAccount charge 0 = 0 := by
  simp [cumulativeChargeAccount]

@[simp]
theorem cumulativeChargeAccount_succ
    (charge : ℕ → ℝ) (T : ℕ) :
    cumulativeChargeAccount charge (T + 1) =
      cumulativeChargeAccount charge T + charge T := by
  simp [cumulativeChargeAccount, Finset.sum_range_succ]

/-- Every charge is realized by its canonical partial-sum account. -/
theorem isRealizedByAccount_cumulativeChargeAccount
    (charge : ℕ → ℝ) :
    IsRealizedByAccount charge (cumulativeChargeAccount charge) := by
  intro T
  rw [cumulativeChargeAccount_succ]
  ring

/-- Every account realizing a charge is its canonical partial-sum account,
up to the single additive constant given by its initial value. -/
theorem IsRealizedByAccount.eq_initial_add_cumulativeChargeAccount
    {charge account : ℕ → ℝ}
    (realized : IsRealizedByAccount charge account)
    (T : ℕ) :
    account T =
      account 0 + cumulativeChargeAccount charge T := by
  rw [cumulativeChargeAccount, realized.sum_range_eq]
  ring

/-- The canonical partial-sum account is the unique realization normalized
to start at zero. -/
theorem IsRealizedByAccount.eq_cumulativeChargeAccount_of_zero
    {charge account : ℕ → ℝ}
    (realized : IsRealizedByAccount charge account)
    (account_zero : account 0 = 0) :
    account = cumulativeChargeAccount charge := by
  funext T
  rw [realized.eq_initial_add_cumulativeChargeAccount T, account_zero,
    zero_add]

/-- Boundedness of the charge partial sums. -/
def HasBoundedCumulativeCharge (charge : ℕ → ℝ) : Prop :=
  ∃ bound : ℝ, ∀ T, |cumulativeChargeAccount charge T| ≤ bound

/-- Bounded partial sums are exactly the existence of a bounded realized
account normalized to start at zero.  The same bound works in both
directions. -/
theorem hasBoundedCumulativeCharge_iff_exists_normalizedAccount
    (charge : ℕ → ℝ) :
    HasBoundedCumulativeCharge charge ↔
      ∃ (account : ℕ → ℝ) (bound : ℝ),
        account 0 = 0 ∧
        (∀ T, |account T| ≤ bound) ∧
        IsRealizedByAccount charge account := by
  constructor
  · rintro ⟨bound, bounded⟩
    exact
      ⟨cumulativeChargeAccount charge, bound,
        cumulativeChargeAccount_zero charge, bounded,
        isRealizedByAccount_cumulativeChargeAccount charge⟩
  · rintro ⟨account, bound, account_zero, bounded, realized⟩
    refine ⟨bound, ?_⟩
    intro T
    rw [cumulativeChargeAccount, realized.sum_range_eq,
      account_zero, sub_zero]
    exact bounded T

/-- Normalization is inessential for existence: a charge has some bounded
realized account exactly when its partial sums are bounded. -/
theorem hasBoundedCumulativeCharge_iff_exists_boundedAccount
    (charge : ℕ → ℝ) :
    HasBoundedCumulativeCharge charge ↔
      ∃ (account : ℕ → ℝ) (bound : ℝ),
        (∀ T, |account T| ≤ bound) ∧
        IsRealizedByAccount charge account := by
  constructor
  · intro bounded
    obtain ⟨account, bound, _, account_bounded, realized⟩ :=
      (hasBoundedCumulativeCharge_iff_exists_normalizedAccount charge).mp
        bounded
    exact ⟨account, bound, account_bounded, realized⟩
  · rintro ⟨account, bound, account_bounded, realized⟩
    refine ⟨2 * bound, ?_⟩
    intro T
    exact realized.abs_sum_range_le_two_mul account_bounded T

/-- Exact bounded-account obstruction: either a bounded realized account
exists, or the absolute cumulative charge exceeds every proposed bound. -/
theorem exists_boundedRealizedAccount_or_cumulativeCharge_unbounded
    (charge : ℕ → ℝ) :
    (∃ (account : ℕ → ℝ) (bound : ℝ),
        (∀ T, |account T| ≤ bound) ∧
        IsRealizedByAccount charge account) ∨
      (∀ bound : ℝ, ∃ T,
        bound < |cumulativeChargeAccount charge T|) := by
  classical
  by_cases bounded : HasBoundedCumulativeCharge charge
  · exact Or.inl
      ((hasBoundedCumulativeCharge_iff_exists_boundedAccount charge).mp
        bounded)
  · right
    intro bound
    by_contra no_large_partial_sum
    apply bounded
    refine ⟨bound, ?_⟩
    intro T
    exact le_of_not_gt (fun larger =>
      no_large_partial_sum ⟨T, larger⟩)

/-- Realized accounts are closed under a finite linear combination, provided
the stage charge is combined with the same coefficients. -/
theorem IsRealizedByAccount.finset_linearCombination
    {J : Type} [Fintype J]
    (coefficient : J → ℝ)
    (charge account : J → ℕ → ℝ)
    (realized : ∀ j, IsRealizedByAccount (charge j) (account j)) :
    IsRealizedByAccount
      (fun T => ∑ j, coefficient j * charge j T)
      (fun T => ∑ j, coefficient j * account j T) := by
  intro T
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [realized j T, mul_sub]

/-- A finite linear combination of bounded realized accounts is bounded by
the corresponding weighted sum of bounds. -/
theorem abs_finset_linearCombination_account_le
    {J : Type} [Fintype J]
    (coefficient bound : J → ℝ)
    (account : J → ℕ → ℝ)
    (account_bounded : ∀ j T, |account j T| ≤ bound j)
    (T : ℕ) :
    |∑ j, coefficient j * account j T| ≤
      ∑ j, |coefficient j| * bound j := by
  calc
    |∑ j, coefficient j * account j T| ≤
        ∑ j, |coefficient j * account j T| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |coefficient j| * |account j T| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul]
    _ ≤ ∑ j, |coefficient j| * bound j := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (account_bounded j T) (abs_nonneg _)

end Math.Probability
