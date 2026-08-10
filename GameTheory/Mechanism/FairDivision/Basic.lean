/-
# Finite indivisible fair division

Additive valuations and fairness predicates over the canonical disjoint
allocation from `Mechanism.Combinatorial`.  Completeness is a separate
certificate; neither carrier finiteness nor decidable equality is stored in
the allocation itself.
-/

import GameTheory.Mechanism.Combinatorial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

namespace GameTheory.Mechanism.FairDivision

open Finset

variable {ι G : Type}

/-- A finite bundle of indivisible goods. -/
abbrev Bundle (G : Type) := Finset G

/-- Fair division uses the mechanism branch's sole disjoint-allocation
carrier. -/
abbrev Allocation (ι G : Type) := Combinatorial.Allocation ι G

/-- Additive item values: `v i g` is agent `i`'s value for good `g`. -/
abbrev AdditiveValuation (ι G : Type) := ι → G → ℝ

/-- Additive value of a finite bundle. -/
noncomputable def value [DecidableEq G] (v : AdditiveValuation ι G) (i : ι)
    (S : Bundle G) : ℝ :=
  ∑ g ∈ S, v i g

/-- Every item has nonnegative value to every agent. -/
def Nonnegative (v : AdditiveValuation ι G) : Prop :=
  ∀ i g, 0 ≤ v i g

/-- Every good is assigned.  Pairwise disjointness is already carried by the
canonical allocation type. -/
def IsComplete (A : Allocation ι G) : Prop :=
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

/-- EFX: removing any positively valued good eliminates envy. -/
def IsEFX [DecidableEq G] (v : AdditiveValuation ι G)
    (A : Allocation ι G) : Prop :=
  ∀ i j g, g ∈ A j → 0 < v i g →
    value v i (A i) ≥ value v i ((A j).erase g)

/-- Proportionality for a complete finite additive allocation. -/
def IsProportional [Fintype ι] [Fintype G] [DecidableEq G]
    (v : AdditiveValuation ι G) (A : Allocation ι G) : Prop :=
  ∀ i, (Fintype.card ι : ℝ) * value v i (A i) ≥ value v i Finset.univ

/-- An allocation gives every agent at least an `alpha` fraction of a chosen
maximin-share benchmark. -/
def IsAlphaMMS [DecidableEq G] (v : AdditiveValuation ι G)
    (A : Allocation ι G) (mms : ι → ℝ) (alpha : ℝ) : Prop :=
  ∀ i, value v i (A i) ≥ alpha * mms i

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

@[simp]
theorem value_empty [DecidableEq G] (v : AdditiveValuation ι G) (i : ι) :
    value v i (∅ : Bundle G) = 0 := by
  simp [value]

theorem value_mono [DecidableEq G] {v : AdditiveValuation ι G}
    (hnonneg : Nonnegative v) (i : ι) {S T : Bundle G} (hST : S ⊆ T) :
    value v i S ≤ value v i T :=
  Finset.sum_le_sum_of_subset_of_nonneg hST fun g _ _ => hnonneg i g

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
  rw [value, value, ← Finset.sum_erase_add (s := S) (f := fun good => v i good) hg]

theorem value_nonneg [DecidableEq G] {v : AdditiveValuation ι G}
    (hnonneg : Nonnegative v) (i : ι) (S : Bundle G) :
    0 ≤ value v i S :=
  Finset.sum_nonneg fun g _ => hnonneg i g

theorem value_eq_zero_of_forall_eq_zero [DecidableEq G]
    (v : AdditiveValuation ι G) (i : ι) {S : Bundle G}
    (hzero : ∀ g ∈ S, v i g = 0) : value v i S = 0 := by
  rw [value]
  exact Finset.sum_eq_zero hzero

/-- Envy-free allocations are EFX for nonnegative additive valuations. -/
theorem IsEnvyFree.isEFX_of_nonnegative [DecidableEq G]
    {v : AdditiveValuation ι G} {A : Allocation ι G}
    (hef : IsEnvyFree v A) (hnonneg : Nonnegative v) : IsEFX v A := by
  intro i j g _ _
  exact le_trans (value_erase_le hnonneg i (A j) g) (hef i j)

/-- Envy-free allocations are EF1. -/
theorem IsEnvyFree.isEF1 [DecidableEq G]
    {v : AdditiveValuation ι G} {A : Allocation ι G}
    (hef : IsEnvyFree v A) : IsEF1 v A :=
  fun i j => Or.inl (hef i j)

/-- EFX implies EF1 under nonnegative additive values. -/
theorem IsEFX.isEF1_of_nonnegative [DecidableEq G]
    {v : AdditiveValuation ι G} {A : Allocation ι G}
    (hefx : IsEFX v A) (hnonneg : Nonnegative v) : IsEF1 v A := by
  intro i j
  by_cases henvy : value v i (A i) ≥ value v i (A j)
  · exact Or.inl henvy
  · right
    have hlt : value v i (A i) < value v i (A j) := lt_of_not_ge henvy
    have hpos : 0 < value v i (A j) :=
      lt_of_le_of_lt (value_nonneg hnonneg i (A i)) hlt
    have hexists : ∃ g ∈ A j, 0 < v i g := by
      by_contra hnone
      push Not at hnone
      have hzero : ∀ g ∈ A j, v i g = 0 := by
        intro g hg
        exact le_antisymm (hnone g hg) (hnonneg i g)
      rw [value_eq_zero_of_forall_eq_zero v i hzero] at hpos
      exact lt_irrefl 0 hpos
    obtain ⟨g, hg, hgpos⟩ := hexists
    exact ⟨g, hg, hefx i j g hg hgpos⟩

/-- Completeness and canonical disjointness decompose the value of all goods
into allocated-bundle values. -/
theorem value_univ_eq_sum_allocation [Fintype ι] [Fintype G] [DecidableEq G]
    {A : Allocation ι G} (hA : IsComplete A)
    (v : AdditiveValuation ι G) (i : ι) :
    value v i Finset.univ = ∑ j : ι, value v i (A j) := by
  classical
  have hpair : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint A.bundle := by
    intro j _ k _ hjk
    exact A.pairwise_disjoint hjk
  have hcover : (Finset.univ : Finset G) = Finset.univ.biUnion A := by
    ext g
    constructor
    · intro _
      obtain ⟨j, hj⟩ := hA g
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩
    · exact fun _ => Finset.mem_univ g
  calc
    value v i Finset.univ = ∑ g ∈ Finset.univ.biUnion A, v i g := by
      rw [hcover, value]
    _ = ∑ j ∈ (Finset.univ : Finset ι), ∑ g ∈ A j, v i g :=
      Finset.sum_biUnion hpair
    _ = ∑ j : ι, value v i (A j) := by simp [value]

/-- A complete envy-free allocation is proportional. -/
theorem IsEnvyFree.isProportional [Fintype ι] [Fintype G] [DecidableEq G]
    {v : AdditiveValuation ι G} {A : Allocation ι G}
    (hef : IsEnvyFree v A) (hA : IsComplete A) : IsProportional v A := by
  intro i
  calc
    value v i Finset.univ = ∑ j : ι, value v i (A j) :=
      value_univ_eq_sum_allocation hA v i
    _ ≤ ∑ _j : ι, value v i (A i) := Finset.sum_le_sum fun j _ => hef i j
    _ = (Fintype.card ι : ℝ) * value v i (A i) := by
      simp [Finset.sum_const, nsmul_eq_mul]

end GameTheory.Mechanism.FairDivision
