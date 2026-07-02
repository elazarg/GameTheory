/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Indivisible Fair Division

Basic finite indivisible-goods fair-division definitions for additive
valuations, plus a first existence result: every two-agent additive
nonnegative instance has an EFX allocation.
-/

namespace GameTheory
namespace SocialChoice
namespace FairDivision
namespace Indivisible

open Finset

variable {ι G : Type*}

/-- A bundle of indivisible goods. -/
abbrev Bundle (G : Type*) := Finset G

/-- An allocation assigns each agent a bundle of goods. -/
abbrev Allocation (ι G : Type*) := ι → Bundle G

/-- Additive item values: `v i g` is agent `i`'s value for good `g`. -/
abbrev AdditiveValuation (ι G : Type*) := ι → G → ℝ

/-- The additive value of a bundle. -/
noncomputable def value [DecidableEq G] (v : AdditiveValuation ι G) (i : ι)
    (S : Bundle G) : ℝ :=
  ∑ g ∈ S, v i g

/-- Item values are nonnegative. -/
def Nonnegative (v : AdditiveValuation ι G) : Prop :=
  ∀ i g, 0 ≤ v i g

/-- An allocation is feasible and complete: bundles are pairwise disjoint and
every good is allocated. -/
def IsAllocation [Fintype G] [DecidableEq G] (A : Allocation ι G) : Prop :=
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
    ∀ g : G, ∃ i : ι, g ∈ A i

/-- Envy-freeness for additive valuations. -/
def IsEnvyFree [DecidableEq G] (v : AdditiveValuation ι G)
    (A : Allocation ι G) : Prop :=
  ∀ i j, value v i (A i) ≥ value v i (A j)

/-- EF1: envy can be eliminated by removing one good from the envied bundle. -/
def IsEF1 [DecidableEq G] (v : AdditiveValuation ι G)
    (A : Allocation ι G) : Prop :=
  ∀ i j, value v i (A i) ≥ value v i (A j) ∨
    ∃ g ∈ A j, value v i (A i) ≥ value v i ((A j).erase g)

/-- EFX: envy can be eliminated by removing any positively-valued good from the
envied bundle. -/
def IsEFX [DecidableEq G] (v : AdditiveValuation ι G)
    (A : Allocation ι G) : Prop :=
  ∀ i j g, g ∈ A j → 0 < v i g →
    value v i (A i) ≥ value v i ((A j).erase g)

/-- Proportionality for finite additive allocations. -/
def IsProportional [Fintype ι] [Fintype G] [DecidableEq G]
    (v : AdditiveValuation ι G) (A : Allocation ι G) : Prop :=
  ∀ i, (Fintype.card ι : ℝ) * value v i (A i) ≥ value v i Finset.univ

/-- An allocation gives every agent at least an `α` fraction of their maximin
share when `mms i` is the chosen maximin-share benchmark for agent `i`. -/
def IsAlphaMMS [DecidableEq G] (v : AdditiveValuation ι G)
    (A : Allocation ι G) (mms : ι → ℝ) (α : ℝ) : Prop :=
  ∀ i, value v i (A i) ≥ α * mms i

theorem isEnvyFree_iff [DecidableEq G] (v : AdditiveValuation ι G)
    (A : Allocation ι G) :
    IsEnvyFree v A ↔ ∀ i j, value v i (A i) ≥ value v i (A j) :=
  Iff.rfl

theorem isEF1_iff [DecidableEq G] (v : AdditiveValuation ι G)
    (A : Allocation ι G) :
    IsEF1 v A ↔ ∀ i j, value v i (A i) ≥ value v i (A j) ∨
      ∃ g ∈ A j, value v i (A i) ≥ value v i ((A j).erase g) :=
  Iff.rfl

theorem isEFX_iff [DecidableEq G] (v : AdditiveValuation ι G)
    (A : Allocation ι G) :
    IsEFX v A ↔ ∀ i j g, g ∈ A j → 0 < v i g →
      value v i (A i) ≥ value v i ((A j).erase g) :=
  Iff.rfl

theorem isProportional_iff [Fintype ι] [Fintype G] [DecidableEq G]
    (v : AdditiveValuation ι G) (A : Allocation ι G) :
    IsProportional v A ↔
      ∀ i, (Fintype.card ι : ℝ) * value v i (A i) ≥ value v i Finset.univ :=
  Iff.rfl

@[simp] theorem value_empty [DecidableEq G] (v : AdditiveValuation ι G) (i : ι) :
    value v i (∅ : Bundle G) = 0 := by
  simp [value]

theorem value_mono [DecidableEq G] {v : AdditiveValuation ι G} (hnonneg : Nonnegative v)
    (i : ι) {S T : Bundle G} (hST : S ⊆ T) :
    value v i S ≤ value v i T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hST
    (by intro g _ _; exact hnonneg i g)

theorem value_erase_le [DecidableEq G] {v : AdditiveValuation ι G}
    (hnonneg : Nonnegative v) (i : ι) (S : Bundle G) (g : G) :
    value v i (S.erase g) ≤ value v i S :=
  value_mono hnonneg i (Finset.erase_subset g S)

theorem value_insert_of_notMem [DecidableEq G] (v : AdditiveValuation ι G)
    (i : ι) {S : Bundle G} {g : G} (hg : g ∉ S) :
    value v i (insert g S) = v i g + value v i S := by
  simp [value, hg]

theorem value_erase_add [DecidableEq G] (v : AdditiveValuation ι G)
    (i : ι) {S : Bundle G} {g : G} (hg : g ∈ S) :
    value v i S = value v i (S.erase g) + v i g := by
  rw [value, value]
  rw [← Finset.sum_erase_add (s := S) (f := fun g => v i g) hg]

theorem value_nonneg [DecidableEq G] {v : AdditiveValuation ι G}
    (hnonneg : Nonnegative v) (i : ι) (S : Bundle G) :
    0 ≤ value v i S := by
  exact Finset.sum_nonneg (fun g _ => hnonneg i g)

theorem value_eq_zero_of_forall_eq_zero [DecidableEq G] (v : AdditiveValuation ι G)
    (i : ι) {S : Bundle G} (hzero : ∀ g ∈ S, v i g = 0) :
    value v i S = 0 := by
  rw [value]
  exact Finset.sum_eq_zero hzero

/-- Envy-free allocations are EFX for nonnegative additive valuations. -/
theorem IsEnvyFree.isEFX_of_nonnegative [DecidableEq G]
    {v : AdditiveValuation ι G} {A : Allocation ι G}
    (hef : IsEnvyFree v A) (hnonneg : Nonnegative v) :
    IsEFX v A := by
  intro i j g _hg _hpos
  exact le_trans (value_erase_le hnonneg i (A j) g) (hef i j)

/-- Envy-free allocations are EF1. -/
theorem IsEnvyFree.isEF1 [DecidableEq G]
    {v : AdditiveValuation ι G} {A : Allocation ι G}
    (hef : IsEnvyFree v A) :
    IsEF1 v A := by
  intro i j
  exact Or.inl (hef i j)

/-- EFX allocations are EF1 for nonnegative additive valuations. -/
theorem IsEFX.isEF1_of_nonnegative [DecidableEq G]
    {v : AdditiveValuation ι G} {A : Allocation ι G}
    (hefx : IsEFX v A) (hnonneg : Nonnegative v) :
    IsEF1 v A := by
  intro i j
  by_cases henvy : value v i (A i) ≥ value v i (A j)
  · exact Or.inl henvy
  · right
    have hlt : value v i (A i) < value v i (A j) := lt_of_not_ge henvy
    have hpos_other : 0 < value v i (A j) :=
      lt_of_le_of_lt (value_nonneg hnonneg i (A i)) hlt
    have hexists : ∃ g ∈ A j, 0 < v i g := by
      by_contra hnone
      push Not at hnone
      have hzero : ∀ g ∈ A j, v i g = 0 := by
        intro g hg
        exact le_antisymm (hnone g hg) (hnonneg i g)
      have hvalue_zero : value v i (A j) = 0 :=
        value_eq_zero_of_forall_eq_zero v i hzero
      linarith
    rcases hexists with ⟨g, hg, hpos⟩
    exact ⟨g, hg, hefx i j g hg hpos⟩

/-- A complete disjoint allocation decomposes the additive value of all goods
as the sum of the values of allocated bundles. -/
theorem value_univ_eq_sum_allocation [Fintype ι] [Fintype G] [DecidableEq G]
    {A : Allocation ι G} (hA : IsAllocation A)
    (v : AdditiveValuation ι G) (i : ι) :
    value v i Finset.univ = ∑ j : ι, value v i (A j) := by
  classical
  have hpair : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint A := by
    intro j _ k _ hjk
    exact hA.1 j k hjk
  have hcover : (Finset.univ : Finset G) = Finset.univ.biUnion A := by
    ext g
    constructor
    · intro _hg
      rcases hA.2 g with ⟨j, hj⟩
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩
    · intro _hg
      exact Finset.mem_univ g
  calc
    value v i Finset.univ = ∑ g ∈ Finset.univ.biUnion A, v i g := by
      rw [hcover, value]
    _ = ∑ j ∈ (Finset.univ : Finset ι), ∑ g ∈ A j, v i g := by
      exact Finset.sum_biUnion hpair
    _ = ∑ j : ι, value v i (A j) := by
      simp [value]

/-- Envy-free complete additive allocations are proportional. -/
theorem IsEnvyFree.isProportional [Fintype ι] [Fintype G] [DecidableEq G]
    {v : AdditiveValuation ι G} {A : Allocation ι G}
    (hef : IsEnvyFree v A) (hA : IsAllocation A) :
    IsProportional v A := by
  intro i
  calc
    value v i Finset.univ = ∑ j : ι, value v i (A j) :=
      value_univ_eq_sum_allocation hA v i
    _ ≤ ∑ _j : ι, value v i (A i) := by
      exact Finset.sum_le_sum (fun j _ => hef i j)
    _ = (Fintype.card ι : ℝ) * value v i (A i) := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- The two-bundle allocation with agent `0` receiving `S` and agent `1`
receiving `T`. -/
def twoAgentAllocation (S T : Bundle G) : Allocation (Fin 2) G :=
  fun i => if i = 0 then S else T

@[simp] theorem twoAgentAllocation_zero (S T : Bundle G) :
    twoAgentAllocation S T (0 : Fin 2) = S := by
  simp [twoAgentAllocation]

@[simp] theorem twoAgentAllocation_one (S T : Bundle G) :
    twoAgentAllocation S T (1 : Fin 2) = T := by
  simp [twoAgentAllocation]

theorem twoAgentAllocation_isAllocation [Fintype G] [DecidableEq G]
    (S T : Bundle G) (hdisj : Disjoint S T) (hcover : S ∪ T = Finset.univ) :
    IsAllocation (twoAgentAllocation S T) := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa using hdisj
    · simpa [disjoint_comm] using hdisj
    · exact (hij rfl).elim
  · intro g
    have hg : g ∈ S ∪ T := by simp [hcover]
    rcases Finset.mem_union.mp hg with hgS | hgT
    · exact ⟨0, by simpa using hgS⟩
    · exact ⟨1, by simpa using hgT⟩

/-- Two agents who both value a single good positively need not have an
envy-free allocation. -/
theorem ef_impossible_two_agents_one_good :
    ∃ v : AdditiveValuation (Fin 2) (Fin 1), Nonnegative v ∧
      ¬ ∃ A : Allocation (Fin 2) (Fin 1), IsAllocation A ∧ IsEnvyFree v A := by
  classical
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro _i _g
    norm_num
  · rintro ⟨A, hA, hef⟩
    rcases hA.2 0 with ⟨owner, howner⟩
    fin_cases owner
    · have hnot : (0 : Fin 1) ∉ A (1 : Fin 2) := by
        intro hmem
        exact Finset.disjoint_left.mp (hA.1 (0 : Fin 2) (1 : Fin 2) (by decide))
          howner hmem
      have howner0 : (0 : Fin 1) ∈ A (0 : Fin 2) := by
        simpa using howner
      have hown : A (0 : Fin 2) = Finset.univ := by
        ext g
        fin_cases g
        simp [howner0]
      have hother : A (1 : Fin 2) = ∅ := by
        ext g
        fin_cases g
        simp [hnot]
      have hle := hef (1 : Fin 2) (0 : Fin 2)
      have hself : value (fun _ _ => (1 : ℝ)) (1 : Fin 2) (A (1 : Fin 2)) = 0 := by
        simp [hother]
      have henvied : value (fun _ _ => (1 : ℝ)) (1 : Fin 2) (A (0 : Fin 2)) = 1 := by
        simp [hown, value]
      linarith
    · have hnot : (0 : Fin 1) ∉ A (0 : Fin 2) := by
        intro hmem
        exact Finset.disjoint_left.mp (hA.1 (1 : Fin 2) (0 : Fin 2) (by decide))
          howner hmem
      have howner1 : (0 : Fin 1) ∈ A (1 : Fin 2) := by
        simpa using howner
      have hown : A (1 : Fin 2) = Finset.univ := by
        ext g
        fin_cases g
        simp [howner1]
      have hother : A (0 : Fin 2) = ∅ := by
        ext g
        fin_cases g
        simp [hnot]
      have hle := hef (0 : Fin 2) (1 : Fin 2)
      have hself : value (fun _ _ => (1 : ℝ)) (0 : Fin 2) (A (0 : Fin 2)) = 0 := by
        simp [hother]
      have henvied : value (fun _ _ => (1 : ℝ)) (0 : Fin 2) (A (1 : Fin 2)) = 1 := by
        simp [hown, value]
      linarith

section TwoAgents

variable [Fintype G] [DecidableEq G]

private noncomputable def cutScore (v : AdditiveValuation (Fin 2) G)
    (S : Bundle G) : ℝ :=
  min (value v (0 : Fin 2) S) (value v (0 : Fin 2) (Finset.univ \ S))

private theorem cutScore_compl (v : AdditiveValuation (Fin 2) G)
    (S : Bundle G) :
    cutScore v (Finset.univ \ S) = cutScore v S := by
  unfold cutScore
  rw [Finset.sdiff_sdiff_eq_self
    (s := (Finset.univ : Finset G)) (t := S) (Finset.subset_univ S)]
  exact min_comm _ _

private theorem maximin_cut_no_envy_after_erase_right
    {v : AdditiveValuation (Fin 2) G} (hnonneg : Nonnegative v)
    {S : Bundle G}
    (hmax : ∀ R ∈ Finset.univ.powerset, cutScore v R ≤ cutScore v S)
    {g : G} (hg : g ∈ Finset.univ \ S) (hpos : 0 < v (0 : Fin 2) g) :
    value v (0 : Fin 2) S ≥ value v (0 : Fin 2) ((Finset.univ \ S).erase g) := by
  by_contra hnot
  have hlt : value v (0 : Fin 2) S <
      value v (0 : Fin 2) ((Finset.univ \ S).erase g) := lt_of_not_ge hnot
  have hgS : g ∉ S := (Finset.mem_sdiff.mp hg).2
  have hcomp :
      Finset.univ \ insert g S = (Finset.univ \ S).erase g := by
    ext x
    by_cases hxg : x = g
    · subst x
      simp [hgS]
    · simp [hxg]
  have hnewS :
      value v (0 : Fin 2) (insert g S) =
        v (0 : Fin 2) g + value v (0 : Fin 2) S :=
    value_insert_of_notMem v (0 : Fin 2) hgS
  have hnew_score :
      cutScore v (insert g S) > cutScore v S := by
    unfold cutScore
    rw [hcomp, hnewS]
    have hmin_old : min (value v (0 : Fin 2) S)
        (value v (0 : Fin 2) (Finset.univ \ S)) = value v (0 : Fin 2) S := by
      exact min_eq_left (le_trans (le_of_lt hlt)
        (value_erase_le hnonneg (0 : Fin 2) (Finset.univ \ S) g))
    rw [hmin_old]
    exact lt_min (by linarith [hpos]) hlt
  have hle := hmax (insert g S) (by simp)
  exact not_lt_of_ge hle hnew_score

private theorem maximin_cut_no_envy_after_erase_left
    {v : AdditiveValuation (Fin 2) G} (hnonneg : Nonnegative v)
    {S : Bundle G}
    (hmax : ∀ R ∈ Finset.univ.powerset, cutScore v R ≤ cutScore v S)
    {g : G} (hg : g ∈ S) (hpos : 0 < v (0 : Fin 2) g) :
    value v (0 : Fin 2) (Finset.univ \ S) ≥ value v (0 : Fin 2) (S.erase g) := by
  have hmax_compl : ∀ R ∈ Finset.univ.powerset,
      cutScore v R ≤ cutScore v (Finset.univ \ S) := by
    intro R hR
    simpa [cutScore_compl v S] using hmax R hR
  have hgcomp : g ∈ Finset.univ \ (Finset.univ \ S) := by
    simp [hg]
  have h := maximin_cut_no_envy_after_erase_right
    (v := v) hnonneg (S := Finset.univ \ S) hmax_compl hgcomp hpos
  rwa [Finset.sdiff_sdiff_eq_self
    (s := (Finset.univ : Finset G)) (t := S) (Finset.subset_univ S)] at h

private theorem maximin_cut_partition_efx_for_zero
    {v : AdditiveValuation (Fin 2) G} (hnonneg : Nonnegative v)
    {S : Bundle G}
    (hmax : ∀ R ∈ Finset.univ.powerset, cutScore v R ≤ cutScore v S)
    (hchoose : value v (1 : Fin 2) S ≤ value v (1 : Fin 2) (Finset.univ \ S)) :
    IsEFX v (twoAgentAllocation S (Finset.univ \ S)) := by
  intro i j g hg hpos
  fin_cases i <;> fin_cases j
  · exact value_erase_le hnonneg (0 : Fin 2) S g
  · simpa using maximin_cut_no_envy_after_erase_right hnonneg hmax
      (by simpa using hg) hpos
  · exact le_trans (value_erase_le hnonneg (1 : Fin 2) S g)
      hchoose
  · exact value_erase_le hnonneg (1 : Fin 2) (Finset.univ \ S) g

private theorem maximin_cut_partition_efx_for_zero_swapped
    {v : AdditiveValuation (Fin 2) G} (hnonneg : Nonnegative v)
    {S : Bundle G}
    (hmax : ∀ R ∈ Finset.univ.powerset, cutScore v R ≤ cutScore v S)
    (hchoose : value v (1 : Fin 2) (Finset.univ \ S) ≤ value v (1 : Fin 2) S) :
    IsEFX v (twoAgentAllocation (Finset.univ \ S) S) := by
  intro i j g hg hpos
  fin_cases i <;> fin_cases j
  · exact value_erase_le hnonneg (0 : Fin 2) (Finset.univ \ S) g
  · simpa using maximin_cut_no_envy_after_erase_left hnonneg hmax
      (by simpa using hg) hpos
  · exact le_trans (value_erase_le hnonneg (1 : Fin 2) (Finset.univ \ S) g)
      hchoose
  · exact value_erase_le hnonneg (1 : Fin 2) S g

/-- Every finite two-agent additive nonnegative indivisible-goods instance has
an EFX allocation. The proof chooses a partition maximizing agent `0`'s minimum
side value, then lets agent `1` choose their preferred side. -/
theorem exists_efx_two_agents (v : AdditiveValuation (Fin 2) G)
    (hnonneg : Nonnegative v) :
    ∃ A : Allocation (Fin 2) G, IsAllocation A ∧ IsEFX v A := by
  classical
  let cuts : Finset (Bundle G) := Finset.univ.powerset
  have hcuts_nonempty : cuts.Nonempty := ⟨∅, by simp [cuts]⟩
  obtain ⟨S, _hS, hmax⟩ := Finset.exists_max_image cuts (cutScore v) hcuts_nonempty
  have hmax' : ∀ R ∈ Finset.univ.powerset, cutScore v R ≤ cutScore v S := by
    intro R hR
    exact hmax R (by simp [cuts])
  by_cases hchoose : value v (1 : Fin 2) S ≤ value v (1 : Fin 2) (Finset.univ \ S)
  · refine ⟨twoAgentAllocation S (Finset.univ \ S), ?_, ?_⟩
    · exact twoAgentAllocation_isAllocation S (Finset.univ \ S)
        Finset.disjoint_sdiff (by ext g; simp)
    · exact maximin_cut_partition_efx_for_zero hnonneg hmax' hchoose
  · refine ⟨twoAgentAllocation (Finset.univ \ S) S, ?_, ?_⟩
    · exact twoAgentAllocation_isAllocation (Finset.univ \ S) S
        Finset.sdiff_disjoint (by
          ext g
          simp)
    · exact maximin_cut_partition_efx_for_zero_swapped hnonneg hmax'
        (le_of_lt (lt_of_not_ge hchoose))

theorem efx_exists_two_agents (v : AdditiveValuation (Fin 2) G)
    (hnonneg : Nonnegative v) :
    ∃ A : Allocation (Fin 2) G, IsAllocation A ∧ IsEFX v A :=
  exists_efx_two_agents v hnonneg

theorem efx_two_agents_two_goods (v : AdditiveValuation (Fin 2) (Fin 2))
    (hnonneg : Nonnegative v) :
    ∃ A : Allocation (Fin 2) (Fin 2), IsAllocation A ∧ IsEFX v A :=
  exists_efx_two_agents v hnonneg

end TwoAgents

end Indivisible
end FairDivision
end SocialChoice
end GameTheory
