/-
# Surplus-maximizing combinatorial allocations

Finite optimization and frugal tie-breaking over the basic combinatorial
auction primitives. Ported mathematically from
`reference/GameTheory-v1/GameTheory/Auctions/Combinatorial.lean` at pinned
commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
-/

import GameTheory.Mechanism.Combinatorial.Basic

namespace GameTheory.Mechanism.Combinatorial

open scoped BigOperators

variable {ι A : Type}

section AllocationRules

variable [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

/-- Total reported surplus of an allocation. -/
noncomputable def surplus (v : ι → Valuation A) (γ : Allocation ι A) : ℝ :=
  ∑ i, v i (γ.bundle i)

/-- An allocation rule is surplus maximizing for every valuation profile. -/
def IsSurplusMaximizer (d : (ι → Valuation A) → Allocation ι A) : Prop :=
  ∀ v γ, surplus v (d v) ≥ surplus v γ

/-- Total number of allocated good-buyer incidences. -/
noncomputable def allocationSize (γ : Allocation ι A) : ℕ :=
  ∑ i, (γ.bundle i).card

theorem exists_surplus_maximizing_allocation (v : ι → Valuation A) :
    ∃ γ : Allocation ι A, ∀ δ, surplus v γ ≥ surplus v δ := by
  classical
  obtain ⟨γ, _, hγ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun γ : Allocation ι A => surplus v γ)
  refine ⟨γ, ?_⟩
  intro δ
  have hδ := Finset.le_sup' (s := Finset.univ) (f := fun γ : Allocation ι A => surplus v γ)
    (by simp : δ ∈ Finset.univ)
  rw [hγ] at hδ
  exact hδ

/-- A surplus-maximizing allocation rule, with arbitrary tie-breaking. -/
noncomputable def surplusMaximizingAllocation (v : ι → Valuation A) : Allocation ι A :=
  Classical.choose (exists_surplus_maximizing_allocation v)

theorem surplusMaximizingAllocation_isSurplusMaximizer :
    IsSurplusMaximizer (surplusMaximizingAllocation (ι := ι) (A := A)) := by
  intro v γ
  exact Classical.choose_spec (exists_surplus_maximizing_allocation v) γ

omit [Fintype A] in
theorem surplus_shrink_eq_of_value_eq (v : ι → Valuation A) (γ : Allocation ι A)
    (i : ι) {B : Finset A} (hB : B ⊆ γ.bundle i) (hval : v i B = v i (γ.bundle i)) :
    surplus v (γ.shrink i B hB) = surplus v γ := by
  classical
  unfold surplus
  rw [← Finset.add_sum_erase Finset.univ (fun j => v j ((γ.shrink i B hB).bundle j))
      (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ (fun j => v j (γ.bundle j)) (Finset.mem_univ i)]
  congr 1
  · simp [hval]
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using (Finset.mem_erase.mp hj).1
    simp [Allocation.shrink_bundle_ne γ hji B hB]

omit [Fintype A] in
theorem allocationSize_shrink_lt (γ : Allocation ι A) (i : ι) {B : Finset A}
    (hB : B ⊂ γ.bundle i) : allocationSize (γ.shrink i B hB.1) < allocationSize γ := by
  classical
  unfold allocationSize
  rw [← Finset.add_sum_erase Finset.univ (fun j => ((γ.shrink i B hB.1).bundle j).card)
      (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ (fun j => (γ.bundle j).card) (Finset.mem_univ i)]
  have hsum :
      (∑ x ∈ Finset.univ.erase i, ((γ.shrink i B hB.1).bundle x).card) =
        ∑ x ∈ Finset.univ.erase i, (γ.bundle x).card := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Allocation.shrink_bundle_ne γ hji B hB.1]
  rw [hsum]
  simpa using Nat.add_lt_add_right (Finset.card_lt_card hB)
    (∑ x ∈ Finset.univ.erase i, (γ.bundle x).card)

/-- Surplus maximizers for a fixed valuation profile. -/
def surplusMaximizers (v : ι → Valuation A) : Set (Allocation ι A) :=
  {γ | ∀ δ, surplus v γ ≥ surplus v δ}

theorem surplusMaximizers_nonempty (v : ι → Valuation A) : (surplusMaximizers v).Nonempty := by
  obtain ⟨γ, hγ⟩ := exists_surplus_maximizing_allocation v
  exact ⟨γ, hγ⟩

/-- A surplus-maximizing allocation rule with minimum total allocated bundle size. -/
noncomputable def frugalSurplusMaximizingAllocation (v : ι → Valuation A) : Allocation ι A :=
  Function.argminOn allocationSize (surplusMaximizers v) (surplusMaximizers_nonempty v)

theorem frugalSurplusMaximizingAllocation_isSurplusMaximizer :
    IsSurplusMaximizer (frugalSurplusMaximizingAllocation (ι := ι) (A := A)) := by
  intro v γ
  exact Function.argminOn_mem allocationSize (surplusMaximizers v)
    (surplusMaximizers_nonempty v) γ

end AllocationRules

section Frugality

variable [DecidableEq ι] [DecidableEq A]

/-- Every strict sub-bundle of an allocated bundle is strictly less valuable. -/
def IsFrugal (d : (ι → Valuation A) → Allocation ι A) : Prop :=
  ∀ v i B, B ⊂ (d v).bundle i → v i B < v i ((d v).bundle i)

section FrugalSelection

variable [Fintype ι] [Fintype A]

theorem frugalSurplusMaximizingAllocation_isFrugal :
    IsFrugal (frugalSurplusMaximizingAllocation (ι := ι) (A := A)) := by
  classical
  intro v i B hstrict
  let γ := frugalSurplusMaximizingAllocation (ι := ι) (A := A) v
  have hmax : γ ∈ surplusMaximizers v :=
    Function.argminOn_mem allocationSize (surplusMaximizers v) (surplusMaximizers_nonempty v)
  by_contra hnot
  have hle : v i (γ.bundle i) ≤ v i B := le_of_not_gt hnot
  have hmono : v i B ≤ v i (γ.bundle i) := (v i).mono hstrict.1
  have hval : v i B = v i (γ.bundle i) := le_antisymm hmono hle
  let γ' := γ.shrink i B hstrict.1
  have hsurplus_eq : surplus v γ' = surplus v γ :=
    surplus_shrink_eq_of_value_eq v γ i hstrict.1 hval
  have hγ'max : γ' ∈ surplusMaximizers v := by
    intro δ
    rw [hsurplus_eq]
    exact hmax δ
  have hmin := Function.argminOn_le allocationSize (surplusMaximizers v) hγ'max
  have hlt : allocationSize γ' < allocationSize γ := allocationSize_shrink_lt γ i hstrict
  exact (not_lt_of_ge hmin) hlt

end FrugalSelection

/-- A frugal allocation assigns a `Q`-based bidder a bundle in `Q`. -/
theorem IsFrugal.allocated_bundle_mem_of_based {d : (ι → Valuation A) → Allocation ι A}
    (hfrugal : IsFrugal d) {Q : Finset (Finset A)} {hQempty : ∅ ∈ Q}
    {v : ι → Valuation A} {i : ι} (hbased : Valuation.IsBasedOn Q hQempty (v i)) :
    (d v).bundle i ∈ Q := by
  classical
  let B : Finset A := (d v).bundle i
  let feasible := Valuation.feasibleBundles Q B
  have hnonempty : feasible.Nonempty := Valuation.feasibleBundles_nonempty hQempty B
  obtain ⟨C, hCfeasible, hsupC⟩ := Finset.exists_mem_eq_sup' hnonempty (fun C : Finset A => v i C)
  rcases Finset.mem_filter.mp hCfeasible with ⟨hCQ, hCB⟩
  by_cases hCB_eq : C = B
  · rwa [hCB_eq] at hCQ
  · have hstrict : C ⊂ B := by
      refine ⟨hCB, ?_⟩
      intro hBC
      exact hCB_eq (Finset.Subset.antisymm hCB hBC)
    have hlt := hfrugal v i C hstrict
    have hB_eq_C : v i B = v i C := by
      calc
        v i B = Valuation.bundling Q hQempty (v i) B := (hbased B).symm
        _ = v i C := hsupC
    have hcontradiction : v i B < v i B := by
      calc
        v i B = v i C := hB_eq_C
        _ < v i ((d v).bundle i) := hlt
        _ = v i B := rfl
    exact False.elim (lt_irrefl _ hcontradiction)

end Frugality

end GameTheory.Mechanism.Combinatorial
