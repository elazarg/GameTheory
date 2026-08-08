/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Tactic

/-!
# Exceptional square-norm rigidity for finite edge laws

This file isolates the algebraic rigidity step in the exceptional branch of a
quitting-game edge law.  If only one player has hazard `X`, the Bellman
identity around its solo reward `R` has the form

`v - R = (1 - X) * (w - R)`.

Equality of the weighted current and successor squared-distance moments then
forces

`sum weight * (2 * X - X^2) * ||w - R||^2 = 0`.

All summands are nonnegative when the edge weights and hazards are in their
probability ranges.  Consequently every positive-weight, positive-hazard edge
has `v = w = R`.

This is only a finite weighted-law statement.  No ergodicity, recurrence,
pathwise constancy, or component-selection conclusion is asserted here.
-/

namespace GameTheory

namespace QuittingExceptionalSquareNormRigidity

/-- Squared Euclidean distance between two finite payoff vectors. -/
def payoffSqDist {ι : Type*} [Fintype ι] [DecidableEq ι]
    (left right : ι → ℝ) : ℝ :=
  ∑ i, (left i - right i) ^ 2

/-- Squared payoff distance is nonnegative. -/
theorem payoffSqDist_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (left right : ι → ℝ) :
    0 ≤ payoffSqDist left right := by
  unfold payoffSqDist
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Squared payoff distance vanishes exactly at equality. -/
theorem payoffSqDist_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (left right : ι → ℝ) :
    payoffSqDist left right = 0 ↔ left = right := by
  constructor
  · intro hzero
    funext i
    have hfun : (fun j => (left j - right j) ^ 2) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg
        (fun j => sq_nonneg (left j - right j))).mp hzero
    have hi : (left i - right i) ^ 2 = 0 := by
      simpa using congrFun hfun i
    nlinarith
  · intro heq
    subst left
    simp [payoffSqDist]

/-- A scalar Bellman identity scales the squared distance by the square of
the survival factor. -/
theorem payoffSqDist_eq_survival_sq_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (current successor root : ι → ℝ) (X : ℝ)
    (hbellman : ∀ i,
      current i - root i = (1 - X) * (successor i - root i)) :
    payoffSqDist current root =
      (1 - X) ^ 2 * payoffSqDist successor root := by
  unfold payoffSqDist
  calc
    (∑ i, (current i - root i) ^ 2) =
        ∑ i, ((1 - X) * (successor i - root i)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hbellman i]
    _ = (1 - X) ^ 2 * ∑ i, (successor i - root i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Equal current and successor squared-distance moments turn the exceptional
Bellman equation into the weighted square-norm identity.  This algebraic
identity does not need sign assumptions on the weights or hazards. -/
theorem weighted_exceptional_square_norm_identity
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (weight X : Ω → ℝ)
    (current successor : Ω → ι → ℝ) (root : ι → ℝ)
    (hbellman : ∀ ω i,
      current ω i - root i =
        (1 - X ω) * (successor ω i - root i))
    (hmoment :
      (∑ ω, weight ω * payoffSqDist (current ω) root) =
        ∑ ω, weight ω * payoffSqDist (successor ω) root) :
    (∑ ω, weight ω * (2 * X ω - X ω ^ 2) *
      payoffSqDist (successor ω) root) = 0 := by
  have hscaled :
      (∑ ω, weight ω * payoffSqDist (current ω) root) =
        ∑ ω, weight ω * (1 - X ω) ^ 2 *
          payoffSqDist (successor ω) root := by
    apply Finset.sum_congr rfl
    intro ω _
    rw [payoffSqDist_eq_survival_sq_mul
      (current ω) (successor ω) root (X ω) (hbellman ω)]
    ring
  have hscaled_eq_successor :
      (∑ ω, weight ω * (1 - X ω) ^ 2 *
          payoffSqDist (successor ω) root) =
        ∑ ω, weight ω * payoffSqDist (successor ω) root :=
    hscaled.symm.trans hmoment
  calc
    (∑ ω, weight ω * (2 * X ω - X ω ^ 2) *
        payoffSqDist (successor ω) root) =
      ∑ ω, (weight ω * payoffSqDist (successor ω) root -
        weight ω * (1 - X ω) ^ 2 *
          payoffSqDist (successor ω) root) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = (∑ ω, weight ω * payoffSqDist (successor ω) root) -
        ∑ ω, weight ω * (1 - X ω) ^ 2 *
          payoffSqDist (successor ω) root := by
      rw [Finset.sum_sub_distrib]
    _ = 0 := by rw [hscaled_eq_successor]; ring

/-- Under probability-range assumptions, the square-norm factor vanishes on
every positive-weight edge. -/
theorem exceptional_square_norm_eq_zero_of_weight_pos
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (weight X : Ω → ℝ)
    (current successor : Ω → ι → ℝ) (root : ι → ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hX_le_one : ∀ ω, X ω ≤ 1)
    (hbellman : ∀ ω i,
      current ω i - root i =
        (1 - X ω) * (successor ω i - root i))
    (hmoment :
      (∑ ω, weight ω * payoffSqDist (current ω) root) =
        ∑ ω, weight ω * payoffSqDist (successor ω) root)
    (ω : Ω) (hωweight : 0 < weight ω) :
    (2 * X ω - X ω ^ 2) * payoffSqDist (successor ω) root = 0 := by
  have hcoefficient (edge : Ω) : 0 ≤ 2 * X edge - X edge ^ 2 := by
    calc
      2 * X edge - X edge ^ 2 = X edge * (2 - X edge) := by ring
      _ ≥ 0 := mul_nonneg (hX_nonneg edge) (by linarith [hX_le_one edge])
  have hterm_nonneg (edge : Ω) :
      0 ≤ weight edge * (2 * X edge - X edge ^ 2) *
        payoffSqDist (successor edge) root :=
    mul_nonneg
      (mul_nonneg (hweight edge) (hcoefficient edge))
      (payoffSqDist_nonneg (successor edge) root)
  have hsum := weighted_exceptional_square_norm_identity
    weight X current successor root hbellman hmoment
  have hzero_fun :
      (fun edge => weight edge * (2 * X edge - X edge ^ 2) *
        payoffSqDist (successor edge) root) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum
  have hweighted_zero :
      weight ω * (2 * X ω - X ω ^ 2) *
        payoffSqDist (successor ω) root = 0 := by
    simpa using congrFun hzero_fun ω
  rw [mul_assoc] at hweighted_zero
  exact (mul_eq_zero.mp hweighted_zero).resolve_left (ne_of_gt hωweight)

/-- Every positive-weight, positive-hazard edge is pinned to the solo root at
both endpoints. -/
theorem current_eq_root_and_successor_eq_root_of_weight_pos_of_hazard_pos
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (weight X : Ω → ℝ)
    (current successor : Ω → ι → ℝ) (root : ι → ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hX_le_one : ∀ ω, X ω ≤ 1)
    (hbellman : ∀ ω i,
      current ω i - root i =
        (1 - X ω) * (successor ω i - root i))
    (hmoment :
      (∑ ω, weight ω * payoffSqDist (current ω) root) =
        ∑ ω, weight ω * payoffSqDist (successor ω) root)
    (ω : Ω) (hωweight : 0 < weight ω) (hωX : 0 < X ω) :
    current ω = root ∧ successor ω = root := by
  have hfactor := exceptional_square_norm_eq_zero_of_weight_pos
    weight X current successor root hweight hX_nonneg hX_le_one
      hbellman hmoment ω hωweight
  have hcoefficient_pos : 0 < 2 * X ω - X ω ^ 2 := by
    calc
      2 * X ω - X ω ^ 2 = X ω * (2 - X ω) := by ring
      _ > 0 := mul_pos hωX (by linarith [hX_le_one ω])
  have hsuccessorSq : payoffSqDist (successor ω) root = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (ne_of_gt hcoefficient_pos)
  have hsuccessor : successor ω = root :=
    (payoffSqDist_eq_zero_iff (successor ω) root).mp hsuccessorSq
  have hcurrent : current ω = root := by
    funext i
    have hi := hbellman ω i
    rw [hsuccessor] at hi
    simp only [sub_self, mul_zero] at hi
    linarith
  exact ⟨hcurrent, hsuccessor⟩

/-- On every positive-weight edge the current and successor payoff vectors
agree.  At zero hazard this is the Bellman equation itself; at positive hazard
both endpoints are pinned to the solo root. -/
theorem current_eq_successor_of_weight_pos
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (weight X : Ω → ℝ)
    (current successor : Ω → ι → ℝ) (root : ι → ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hX_le_one : ∀ ω, X ω ≤ 1)
    (hbellman : ∀ ω i,
      current ω i - root i =
        (1 - X ω) * (successor ω i - root i))
    (hmoment :
      (∑ ω, weight ω * payoffSqDist (current ω) root) =
        ∑ ω, weight ω * payoffSqDist (successor ω) root)
    (ω : Ω) (hωweight : 0 < weight ω) :
    current ω = successor ω := by
  by_cases hωXzero : X ω = 0
  · funext i
    have hi := hbellman ω i
    rw [hωXzero] at hi
    norm_num at hi
    linarith
  · have hωX : 0 < X ω :=
      lt_of_le_of_ne (hX_nonneg ω) (Ne.symm hωXzero)
    obtain ⟨hcurrent, hsuccessor⟩ :=
      current_eq_root_and_successor_eq_root_of_weight_pos_of_hazard_pos
        weight X current successor root hweight hX_nonneg hX_le_one
          hbellman hmoment ω hωweight hωX
    rw [hcurrent, hsuccessor]

/-- A positive weighted mean hazard contains an edge on which both its weight
and its hazard are positive. -/
theorem exists_weight_pos_and_hazard_pos_of_weighted_mean_pos
    {Ω : Type*} [Fintype Ω]
    (weight X : Ω → ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hmean : 0 < ∑ ω, weight ω * X ω) :
    ∃ ω, 0 < weight ω ∧ 0 < X ω := by
  obtain ⟨ω, _, hproduct⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun edge _ => mul_nonneg (hweight edge) (hX_nonneg edge))).mp hmean
  have hweight_ne : weight ω ≠ 0 := by
    intro hzero
    simp [hzero] at hproduct
  have hX_ne : X ω ≠ 0 := by
    intro hzero
    simp [hzero] at hproduct
  exact ⟨ω,
    lt_of_le_of_ne (hweight ω) (Ne.symm hweight_ne),
    lt_of_le_of_ne (hX_nonneg ω) (Ne.symm hX_ne)⟩

/-- Positive mean exceptional hazard selects a concrete positive-hazard edge
whose two payoff endpoints are the solo root. -/
theorem exists_positive_hazard_root_edge_of_weighted_mean_pos
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (weight X : Ω → ℝ)
    (current successor : Ω → ι → ℝ) (root : ι → ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hX_le_one : ∀ ω, X ω ≤ 1)
    (hbellman : ∀ ω i,
      current ω i - root i =
        (1 - X ω) * (successor ω i - root i))
    (hmoment :
      (∑ ω, weight ω * payoffSqDist (current ω) root) =
        ∑ ω, weight ω * payoffSqDist (successor ω) root)
    (hmean : 0 < ∑ ω, weight ω * X ω) :
    ∃ ω, 0 < weight ω ∧ 0 < X ω ∧
      current ω = root ∧ successor ω = root := by
  obtain ⟨ω, hωweight, hωX⟩ :=
    exists_weight_pos_and_hazard_pos_of_weighted_mean_pos
      weight X hweight hX_nonneg hmean
  obtain ⟨hcurrent, hsuccessor⟩ :=
    current_eq_root_and_successor_eq_root_of_weight_pos_of_hazard_pos
      weight X current successor root hweight hX_nonneg hX_le_one
        hbellman hmoment ω hωweight hωX
  exact ⟨ω, hωweight, hωX, hcurrent, hsuccessor⟩

end QuittingExceptionalSquareNormRigidity

end GameTheory
