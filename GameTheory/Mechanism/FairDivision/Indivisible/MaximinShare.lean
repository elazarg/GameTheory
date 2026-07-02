/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.FairDivision.Indivisible.Basic

/-!
# Indivisible Fair Division: Maximin Share

Maximin-share benchmarks for finite additive indivisible-goods allocations.
-/

namespace GameTheory
namespace SocialChoice
namespace FairDivision
namespace Indivisible

open Finset

variable {ι G : Type*}

section MaximinShare

variable [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype G] [DecidableEq G]

/-- The allocation that gives every good to one fixed agent. -/
def allGoodsAllocation (i₀ : ι) : Allocation ι G :=
  fun i => if i = i₀ then Finset.univ else ∅

omit [Fintype ι] [Nonempty ι] in
theorem allGoodsAllocation_isAllocation (i₀ : ι) :
    IsAllocation (allGoodsAllocation (G := G) i₀) := by
  constructor
  · intro i j hij
    by_cases hi : i = i₀
    · by_cases hj : j = i₀
      · exact (hij (hi.trans hj.symm)).elim
      · simp [allGoodsAllocation, hi, hj]
    · simp [allGoodsAllocation, hi]
  · intro g
    exact ⟨i₀, by simp [allGoodsAllocation]⟩

/-- The finite set of complete feasible allocations. -/
noncomputable def feasibleAllocations : Finset (Allocation ι G) := by
  classical
  exact (Finset.univ : Finset (Allocation ι G)).filter IsAllocation

omit [Nonempty ι] in
theorem mem_feasibleAllocations {A : Allocation ι G} :
    A ∈ feasibleAllocations (ι := ι) (G := G) ↔ IsAllocation A := by
  classical
  simp [feasibleAllocations]

theorem feasibleAllocations_nonempty :
    (feasibleAllocations (ι := ι) (G := G)).Nonempty := by
  classical
  rcases ‹Nonempty ι› with ⟨i₀⟩
  exact ⟨allGoodsAllocation (G := G) i₀,
    mem_feasibleAllocations.mpr (allGoodsAllocation_isAllocation (G := G) i₀)⟩

/-- The least bundle value an agent receives in a fixed allocation, evaluated
using agent `i`'s valuation for every bundle. -/
noncomputable def minBundleValue (v : AdditiveValuation ι G) (i : ι)
    (A : Allocation ι G) : ℝ :=
  ((Finset.univ : Finset ι).image fun j => value v i (A j)).min' (by
    classical
    rcases ‹Nonempty ι› with ⟨j⟩
    exact ⟨value v i (A j), by simp⟩)

omit [DecidableEq ι] [Fintype G] in
theorem minBundleValue_le (v : AdditiveValuation ι G) (i j : ι)
    (A : Allocation ι G) :
    minBundleValue v i A ≤ value v i (A j) := by
  classical
  unfold minBundleValue
  exact Finset.min'_le _ _ (by simp)

omit [DecidableEq ι] in
theorem exists_bundleValue_le_average_of_isAllocation
    {v : AdditiveValuation ι G} {B : Allocation ι G} (hB : IsAllocation B) (i : ι) :
    ∃ j : ι, value v i (B j) ≤ value v i Finset.univ / (Fintype.card ι : ℝ) := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := by
    rcases ‹Nonempty ι› with ⟨j⟩
    exact ⟨j, by simp⟩
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hconst :
      (∑ _j : ι, value v i Finset.univ / (Fintype.card ι : ℝ)) =
        value v i Finset.univ := by
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [mul_comm]
    exact div_mul_cancel₀ _ hcard_ne
  have hsum :
      (∑ j : ι, value v i (B j)) ≤
        ∑ _j : ι, value v i Finset.univ / (Fintype.card ι : ℝ) := by
    rw [hconst]
    exact le_of_eq (value_univ_eq_sum_allocation hB v i).symm
  rcases Finset.exists_le_of_sum_le (s := (Finset.univ : Finset ι))
      (f := fun j => value v i (B j))
      (g := fun _j => value v i Finset.univ / (Fintype.card ι : ℝ)) hne hsum with
    ⟨j, _hj, hj⟩
  exact ⟨j, hj⟩

omit [DecidableEq ι] in
theorem minBundleValue_le_average_of_isAllocation
    {v : AdditiveValuation ι G} {B : Allocation ι G} (hB : IsAllocation B) (i : ι) :
    minBundleValue v i B ≤ value v i Finset.univ / (Fintype.card ι : ℝ) := by
  rcases exists_bundleValue_le_average_of_isAllocation (B := B) hB i with ⟨j, hj⟩
  exact (minBundleValue_le v i j B).trans hj

/-- Agent `i`'s maximin share: the largest minimum bundle value they can
guarantee over all complete feasible allocations. -/
noncomputable def maximinShare (v : AdditiveValuation ι G) (i : ι) : ℝ :=
  ((feasibleAllocations (ι := ι) (G := G)).image fun A => minBundleValue v i A).max' (by
    classical
    exact feasibleAllocations_nonempty.image _)

theorem minBundleValue_le_maximinShare {v : AdditiveValuation ι G}
    {A : Allocation ι G} (hA : IsAllocation A) (i : ι) :
    minBundleValue v i A ≤ maximinShare v i := by
  classical
  unfold maximinShare
  exact Finset.le_max' _ _ (by
    exact Finset.mem_image.mpr ⟨A, mem_feasibleAllocations.mpr hA, rfl⟩)

theorem maximinShare_le_average (v : AdditiveValuation ι G) (i : ι) :
    maximinShare v i ≤ value v i Finset.univ / (Fintype.card ι : ℝ) := by
  classical
  unfold maximinShare
  rw [Finset.max'_le_iff]
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨B, hB, rfl⟩
  exact minBundleValue_le_average_of_isAllocation
    (B := B) (mem_feasibleAllocations.mp hB) i

/-- An allocation gives every agent at least their maximin share. -/
def IsMaxminShare (v : AdditiveValuation ι G) (A : Allocation ι G) : Prop :=
  ∀ i, value v i (A i) ≥ maximinShare v i

theorem isMaxminShare_iff_isAlphaMMS_one (v : AdditiveValuation ι G)
    (A : Allocation ι G) :
    IsMaxminShare v A ↔ IsAlphaMMS v A (maximinShare v) 1 := by
  simp [IsMaxminShare, IsAlphaMMS]

/-- Proportional complete additive allocations satisfy maximin share. -/
theorem IsProportional.isMaxminShare {v : AdditiveValuation ι G}
    {A : Allocation ι G} (hp : IsProportional v A) :
    IsMaxminShare v A := by
  intro i
  have hcard_pos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hratio : value v i Finset.univ / (Fintype.card ι : ℝ) ≤ value v i (A i) := by
    rw [div_le_iff₀ hcard_pos]
    simpa [mul_comm] using hp i
  exact (maximinShare_le_average v i).trans hratio

end MaximinShare

end Indivisible
end FairDivision
end SocialChoice
end GameTheory
