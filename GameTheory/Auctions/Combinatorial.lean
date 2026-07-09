/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.WellFounded
import Math.Fintype
import Math.Probability

/-!
# Combinatorial auctions

Finite combinatorial-auction primitives used by the k-implementation VCG
arguments. A valuation is normalized and monotone over bundles of goods; an
allocation assigns pairwise-disjoint bundles to buyers, leaving any remaining
goods unallocated.
-/

namespace GameTheory

open scoped BigOperators

namespace CombinatorialAuction

variable {ι A : Type}

/-- A normalized monotone valuation over finite bundles of goods. -/
structure Valuation (A : Type) [DecidableEq A] where
  /-- Value assigned to a bundle. -/
  value : Finset A → ℝ
  /-- The empty bundle has value zero. -/
  empty_value : value ∅ = 0
  /-- Values are monotone in bundle inclusion. -/
  monotone : ∀ {B C : Finset A}, B ⊆ C → value B ≤ value C

namespace Valuation

variable [DecidableEq A]

instance : CoeFun (Valuation A) (fun _ => Finset A → ℝ) :=
  ⟨Valuation.value⟩

@[simp] theorem empty (v : Valuation A) : v (∅ : Finset A) = 0 :=
  v.empty_value

@[ext] theorem ext {v w : Valuation A} (h : ∀ B, v B = w B) : v = w := by
  cases v
  cases w
  simp only [Valuation.mk.injEq]
  funext B
  exact h B

theorem mono (v : Valuation A) {B C : Finset A} (hBC : B ⊆ C) :
    v B ≤ v C :=
  v.monotone hBC

theorem nonneg (v : Valuation A) (B : Finset A) : 0 ≤ v B := by
  rw [← v.empty]
  exact v.mono (by simp)

/-- A valuation that pays `R` exactly on bundles containing `S`, and zero
otherwise. The nonempty hypothesis keeps the valuation normalized at `∅`. -/
def thresholdBundle (S : Finset A) (hS : S.Nonempty) (R : ℝ) (hR : 0 ≤ R) :
    Valuation A where
  value B := if S ⊆ B then R else 0
  empty_value := by
    have hnot : ¬ S ⊆ (∅ : Finset A) := by
      intro hsub
      obtain ⟨a, ha⟩ := hS
      simpa using hsub ha
    simp [hnot]
  monotone := by
    intro B C hBC
    by_cases hSB : S ⊆ B
    · have hSC : S ⊆ C := hSB.trans hBC
      simp [hSB, hSC]
    · by_cases hSC : S ⊆ C
      · simp [hSB, hSC, hR]
      · simp [hSB, hSC]

@[simp] theorem thresholdBundle_apply_of_subset {S B : Finset A} {hS : S.Nonempty}
    {R : ℝ} {hR : 0 ≤ R} (hSB : S ⊆ B) :
    thresholdBundle S hS R hR B = R := by
  simp [thresholdBundle, hSB]

@[simp] theorem thresholdBundle_apply_of_not_subset {S B : Finset A} {hS : S.Nonempty}
    {R : ℝ} {hR : 0 ≤ R} (hSB : ¬ S ⊆ B) :
    thresholdBundle S hS R hR B = 0 := by
  simp [thresholdBundle, hSB]

/-- The zero valuation. -/
instance : Inhabited (Valuation A) where
  default :=
    { value := fun _ => 0
      empty_value := rfl
      monotone := by
        intro B C hBC
        rfl }

/-- Candidate quasi-field bundles contained in `B`. -/
def feasibleBundles (Q : Finset (Finset A)) (B : Finset A) : Finset (Finset A) :=
  Q.filter (fun C => C ⊆ B)

theorem empty_mem_feasibleBundles {Q : Finset (Finset A)} (hQempty : ∅ ∈ Q)
    (B : Finset A) :
    (∅ : Finset A) ∈ feasibleBundles Q B := by
  simp [feasibleBundles, hQempty]

theorem feasibleBundles_nonempty {Q : Finset (Finset A)} (hQempty : ∅ ∈ Q)
    (B : Finset A) :
    (feasibleBundles Q B).Nonempty :=
  ⟨∅, empty_mem_feasibleBundles hQempty B⟩

theorem feasibleBundles_mono {Q : Finset (Finset A)} {B C : Finset A}
    (hBC : B ⊆ C) :
    feasibleBundles Q B ⊆ feasibleBundles Q C := by
  intro D hD
  rcases Finset.mem_filter.mp hD with ⟨hDQ, hDB⟩
  exact Finset.mem_filter.mpr ⟨hDQ, hDB.trans hBC⟩

/-- The `Q`-bundled valuation: the value of a bundle is the best value of a
`Q`-bundle contained in it. This is `v^Q`/`vΣ` in the paper. -/
noncomputable def bundling (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (v : Valuation A) : Valuation A where
  value B :=
    (feasibleBundles Q B).sup' (feasibleBundles_nonempty hQempty B)
      (fun C => v C)
  empty_value := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro C hC
      rcases Finset.mem_filter.mp hC with ⟨_, hCempty⟩
      have hC_eq : C = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        simpa using hCempty ha
      rw [hC_eq]
      simp
    · simpa using Finset.le_sup' (fun C => v C)
        (empty_mem_feasibleBundles hQempty (∅ : Finset A))
  monotone := by
    intro B C hBC
    change
      (feasibleBundles Q B).sup' (feasibleBundles_nonempty hQempty B)
          (fun D => v D) ≤
        (feasibleBundles Q C).sup' (feasibleBundles_nonempty hQempty C)
          (fun D => v D)
    apply Finset.sup'_le
    intro D hD
    exact Finset.le_sup' (fun E => v E)
      ((feasibleBundles_mono (Q := Q) hBC) hD)

theorem bundling_value_eq_sup (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (v : Valuation A) (B : Finset A) :
    bundling Q hQempty v B =
      (feasibleBundles Q B).sup' (feasibleBundles_nonempty hQempty B)
        (fun C => v C) :=
  rfl

theorem bundling_le_original (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (v : Valuation A) (B : Finset A) :
    bundling Q hQempty v B ≤ v B := by
  change
    (feasibleBundles Q B).sup' (feasibleBundles_nonempty hQempty B)
        (fun C => v C) ≤ v B
  apply Finset.sup'_le
  intro C hC
  exact v.mono (Finset.mem_filter.mp hC).2

theorem le_bundling_of_mem {Q : Finset (Finset A)} (hQempty : ∅ ∈ Q)
    {v : Valuation A} {B C : Finset A} (hCQ : C ∈ Q) (hCB : C ⊆ B) :
    v C ≤ bundling Q hQempty v B := by
  change v C ≤
    (feasibleBundles Q B).sup' (feasibleBundles_nonempty hQempty B)
      (fun D => v D)
  exact Finset.le_sup' (fun D => v D)
    (Finset.mem_filter.mpr ⟨hCQ, hCB⟩)

theorem bundling_eq_original_of_mem {Q : Finset (Finset A)} (hQempty : ∅ ∈ Q)
    {v : Valuation A} {B : Finset A} (hBQ : B ∈ Q) :
    bundling Q hQempty v B = v B := by
  apply le_antisymm
  · exact bundling_le_original Q hQempty v B
  · exact le_bundling_of_mem hQempty hBQ (by simp)

/-- A valuation is `Q`-based when bundling it through `Q` changes nothing. -/
def IsBasedOn (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (v : Valuation A) : Prop :=
  ∀ B : Finset A, bundling Q hQempty v B = v B

/-- Bundling is idempotent: the bundled valuation is `Q`-based. -/
theorem bundling_isBasedOn (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (v : Valuation A) :
    IsBasedOn Q hQempty (bundling Q hQempty v) := by
  intro B
  apply le_antisymm
  · exact bundling_le_original Q hQempty (bundling Q hQempty v) B
  · change
      (feasibleBundles Q B).sup' (feasibleBundles_nonempty hQempty B)
          (fun C => v C) ≤
        (feasibleBundles Q B).sup' (feasibleBundles_nonempty hQempty B)
          (fun C => bundling Q hQempty v C)
    apply Finset.sup'_le
    intro C hC
    rcases Finset.mem_filter.mp hC with ⟨hCQ, hCB⟩
    rw [← bundling_eq_original_of_mem (Q := Q) hQempty (v := v) hCQ]
    exact le_bundling_of_mem (Q := Q) hQempty
      (v := bundling Q hQempty v) hCQ hCB

end Valuation

/-- An allocation gives each buyer a bundle, with no good assigned to two
different buyers. Goods not in any bundle remain with the seller. -/
structure Allocation (ι A : Type) [DecidableEq ι] [DecidableEq A] where
  /-- Bundle assigned to each buyer. -/
  bundle : ι → Finset A
  /-- Distinct buyers receive disjoint bundles. -/
  pairwise_disjoint : ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (bundle i) (bundle j)

namespace Allocation

variable [DecidableEq ι] [DecidableEq A]
variable (γ : Allocation ι A)

/-- Shrink one buyer's allocated bundle to a sub-bundle. -/
def shrink (i : ι) (B : Finset A) (hB : B ⊆ γ.bundle i) : Allocation ι A where
  bundle j := if j = i then B else γ.bundle j
  pairwise_disjoint := by
    intro j k hjk
    by_cases hji : j = i
    · by_cases hki : k = i
      · exact False.elim (hjk (hji.trans hki.symm))
      · have hjk' : j ≠ k := hjk
        have hBj : B ⊆ γ.bundle j := by
          simpa [hji] using hB
        simpa only [hji, hki, ↓reduceIte] using
          Disjoint.mono_left hBj (γ.pairwise_disjoint hjk')
    · by_cases hki : k = i
      · have hBk : B ⊆ γ.bundle k := by
          simpa [hki] using hB
        simpa only [hji, hki, ↓reduceIte] using
          Disjoint.mono_right hBk (γ.pairwise_disjoint hjk)
      · simpa only [hji, hki, ↓reduceIte] using
          γ.pairwise_disjoint hjk

@[simp] theorem shrink_bundle_self (i : ι) (B : Finset A) (hB : B ⊆ γ.bundle i) :
    (γ.shrink i B hB).bundle i = B := by
  simp [shrink]

@[simp] theorem shrink_bundle_ne {i j : ι} (hji : j ≠ i)
    (B : Finset A) (hB : B ⊆ γ.bundle i) :
    (γ.shrink i B hB).bundle j = γ.bundle j := by
  simp [shrink, hji]

section Residual

variable [Fintype ι]
variable [Fintype A]

/-- The goods left after all buyers other than `i` keep their allocated bundles. -/
noncomputable def residualAfterOpponents (i : ι) : Finset A :=
  Finset.univ \ ((Finset.univ.filter fun j => j ≠ i).biUnion γ.bundle)

/-- Give buyer `i` every good not allocated to the other buyers, leaving all
other buyers' bundles unchanged. -/
noncomputable def giveResidualTo (i : ι) : Allocation ι A where
  bundle j := if j = i then γ.residualAfterOpponents i else γ.bundle j
  pairwise_disjoint := by
    classical
    intro j k hjk
    by_cases hji : j = i
    · have hki : k ≠ i := by
        intro hk
        exact hjk (hji.trans hk.symm)
      rw [if_pos hji, if_neg hki]
      change Disjoint (γ.residualAfterOpponents i) (γ.bundle k)
      rw [Finset.disjoint_left]
      intro x hx hxk
      simp only [residualAfterOpponents, Finset.mem_sdiff] at hx
      have hkOpp : k ∈ Finset.univ.filter fun j => j ≠ i :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, hki⟩
      exact hx.2 (Finset.mem_biUnion.mpr ⟨k, hkOpp, hxk⟩)
    · by_cases hki : k = i
      · rw [if_neg hji, if_pos hki]
        rw [Finset.disjoint_left]
        intro x hxj hx
        simp only [residualAfterOpponents, Finset.mem_sdiff] at hx
        have hjOpp : j ∈ Finset.univ.filter fun j => j ≠ i :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hji⟩
        exact hx.2 (Finset.mem_biUnion.mpr ⟨j, hjOpp, hxj⟩)
      · rw [if_neg hji, if_neg hki]
        exact γ.pairwise_disjoint hjk

@[simp] theorem giveResidualTo_bundle_self (i : ι) :
    (γ.giveResidualTo i).bundle i = γ.residualAfterOpponents i := by
  simp [giveResidualTo]

@[simp] theorem giveResidualTo_bundle_ne {i j : ι} (hji : j ≠ i) :
    (γ.giveResidualTo i).bundle j = γ.bundle j := by
  simp [giveResidualTo, hji]

/-- Buyer `i`'s original bundle is contained in the residual after the other
buyers keep their bundles. -/
theorem bundle_subset_residualAfterOpponents (i : ι) :
    γ.bundle i ⊆ γ.residualAfterOpponents i := by
  classical
  intro x hx
  simp only [residualAfterOpponents, Finset.mem_sdiff]
  constructor
  · exact Finset.mem_univ x
  · intro hxUnion
    rcases Finset.mem_biUnion.mp hxUnion with ⟨j, hj, hxj⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact (Finset.disjoint_left.mp (γ.pairwise_disjoint hj.symm)) hx hxj

end Residual

end Allocation

/-- Empty allocation: every buyer receives the empty bundle. -/
def emptyAllocation (ι A : Type) [DecidableEq ι] [DecidableEq A] :
    Allocation ι A where
  bundle := fun _ => ∅
  pairwise_disjoint := by
    intro i j hij
    simp

instance allocationInhabited [DecidableEq ι] [DecidableEq A] :
    Inhabited (Allocation ι A) :=
  ⟨emptyAllocation ι A⟩

instance allocationFintype [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] :
    Fintype (Allocation ι A) := by
  classical
  let valid : (ι → Finset A) → Prop :=
    fun bundle => ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (bundle i) (bundle j)
  haveI : DecidablePred valid := by
    intro bundle
    unfold valid
    infer_instance
  let e : Allocation ι A ≃ {bundle : ι → Finset A // valid bundle} := {
    toFun γ := ⟨γ.bundle, γ.pairwise_disjoint⟩
    invFun bundle := ⟨bundle.1, bundle.2⟩
    left_inv := by
      intro γ
      cases γ
      rfl
    right_inv := by
      intro bundle
      cases bundle
      rfl
  }
  exact Fintype.ofEquiv {bundle : ι → Finset A // valid bundle} e.symm

section AllocationRules

variable [Fintype ι] [DecidableEq ι] [DecidableEq A]

/-- Total reported surplus of an allocation. -/
noncomputable def surplus (v : ι → Valuation A)
    (γ : Allocation ι A) : ℝ :=
  ∑ i, v i (γ.bundle i)

/-- An allocation rule is surplus maximizing for every valuation profile. -/
def IsSurplusMaximizer (d : (ι → Valuation A) → Allocation ι A) : Prop :=
  ∀ v γ, surplus v (d v) ≥ surplus v γ

/-- Total number of allocated good-buyer incidences. -/
noncomputable def allocationSize (γ : Allocation ι A) : ℕ :=
  ∑ i, (γ.bundle i).card

theorem exists_surplus_maximizing_allocation [Finite A] (v : ι → Valuation A) :
    ∃ γ : Allocation ι A, ∀ δ, surplus v γ ≥ surplus v δ := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  obtain ⟨γ, _hγmem, hγ⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty) (fun γ : Allocation ι A =>
      surplus v γ)
  refine ⟨γ, ?_⟩
  intro δ
  have hδ := Finset.le_sup' (s := Finset.univ)
    (f := fun γ : Allocation ι A => surplus v γ) (by simp : δ ∈ Finset.univ)
  rw [hγ] at hδ
  exact hδ

/-- A surplus-maximizing allocation rule, with arbitrary tie-breaking. -/
noncomputable def surplusMaximizingAllocation [Finite A] (v : ι → Valuation A) :
    Allocation ι A :=
  Classical.choose (exists_surplus_maximizing_allocation v)

theorem surplusMaximizingAllocation_isSurplusMaximizer [Finite A] :
    IsSurplusMaximizer (surplusMaximizingAllocation (ι := ι) (A := A)) := by
  intro v γ
  exact Classical.choose_spec (exists_surplus_maximizing_allocation v) γ

theorem surplus_shrink_eq_of_value_eq (v : ι → Valuation A) (γ : Allocation ι A)
    (i : ι) {B : Finset A} (hB : B ⊆ γ.bundle i)
    (hval : v i B = v i (γ.bundle i)) :
    surplus v (γ.shrink i B hB) = surplus v γ := by
  classical
  unfold surplus
  rw [← Finset.add_sum_erase Finset.univ
      (fun j => v j ((γ.shrink i B hB).bundle j)) (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ
      (fun j => v j (γ.bundle j)) (Finset.mem_univ i)]
  congr 1
  · simp [hval]
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := by
      simpa using Finset.mem_erase.mp hj |>.1
    simp [Allocation.shrink_bundle_ne γ hji B hB]

theorem allocationSize_shrink_lt (γ : Allocation ι A)
    (i : ι) {B : Finset A} (hB : B ⊂ γ.bundle i) :
    allocationSize (γ.shrink i B hB.1) < allocationSize γ := by
  classical
  unfold allocationSize
  rw [← Finset.add_sum_erase Finset.univ
      (fun j => ((γ.shrink i B hB.1).bundle j).card) (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ
      (fun j => (γ.bundle j).card) (Finset.mem_univ i)]
  have hsum :
      (∑ x ∈ Finset.univ.erase i, ((γ.shrink i B hB.1).bundle x).card) =
        ∑ x ∈ Finset.univ.erase i, (γ.bundle x).card := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := by
      exact (Finset.mem_erase.mp hj).1
    simp [Allocation.shrink_bundle_ne γ hji B hB.1]
  rw [hsum]
  simpa using Nat.add_lt_add_right (Finset.card_lt_card hB)
    (∑ x ∈ Finset.univ.erase i, (γ.bundle x).card)

/-- Surplus maximizers for a fixed valuation profile. -/
def surplusMaximizers (v : ι → Valuation A) : Set (Allocation ι A) :=
  {γ | ∀ δ, surplus v γ ≥ surplus v δ}

theorem surplusMaximizers_nonempty [Finite A] (v : ι → Valuation A) :
    (surplusMaximizers v).Nonempty := by
  obtain ⟨γ, hγ⟩ := exists_surplus_maximizing_allocation v
  exact ⟨γ, hγ⟩

/-- A surplus-maximizing allocation rule with frugal tie-breaking: among all
surplus maximizers it picks one with minimal total allocated bundle size. -/
noncomputable def frugalSurplusMaximizingAllocation [Finite A]
    (v : ι → Valuation A) : Allocation ι A :=
  Function.argminOn allocationSize (surplusMaximizers v)
    (surplusMaximizers_nonempty v)

theorem frugalSurplusMaximizingAllocation_isSurplusMaximizer [Finite A] :
    IsSurplusMaximizer
      (frugalSurplusMaximizingAllocation (ι := ι) (A := A)) := by
  intro v γ
  exact Function.argminOn_mem allocationSize (surplusMaximizers v)
    (surplusMaximizers_nonempty v) γ

end AllocationRules

section Frugality

variable [DecidableEq ι] [DecidableEq A]

/-- Frugality from the paper: every strict sub-bundle of an allocated bundle is
strictly less valuable for that buyer under the reported valuation. -/
def IsFrugal (d : (ι → Valuation A) → Allocation ι A) : Prop :=
  ∀ v i B, B ⊂ (d v).bundle i → v i B < v i ((d v).bundle i)

section FrugalSelection

variable [Fintype ι]

theorem frugalSurplusMaximizingAllocation_isFrugal [Finite A] :
    IsFrugal (frugalSurplusMaximizingAllocation (ι := ι) (A := A)) := by
  classical
  intro v i B hstrict
  let γ := frugalSurplusMaximizingAllocation (ι := ι) (A := A) v
  have hmax : γ ∈ surplusMaximizers v :=
    Function.argminOn_mem allocationSize (surplusMaximizers v)
      (surplusMaximizers_nonempty v)
  by_contra hnot
  have hle : v i (γ.bundle i) ≤ v i B :=
    le_of_not_gt hnot
  have hmono : v i B ≤ v i (γ.bundle i) :=
    (v i).mono hstrict.1
  have hval : v i B = v i (γ.bundle i) :=
    le_antisymm hmono hle
  let γ' := γ.shrink i B hstrict.1
  have hsurplus_eq : surplus v γ' = surplus v γ :=
    surplus_shrink_eq_of_value_eq v γ i hstrict.1 hval
  have hγ'max : γ' ∈ surplusMaximizers v := by
    intro δ
    rw [hsurplus_eq]
    exact hmax δ
  have hmin := Function.argminOn_le allocationSize (surplusMaximizers v)
    hγ'max
  have hlt : allocationSize γ' < allocationSize γ :=
    allocationSize_shrink_lt γ i hstrict
  exact (not_lt_of_ge hmin) hlt

end FrugalSelection

/-- In a frugal allocation rule, if player `i` reports a `Q`-based valuation,
then the bundle allocated to `i` is itself a member of `Q`. Otherwise some
`Q`-subbundle attains the same reported value, contradicting frugality. -/
theorem IsFrugal.allocated_bundle_mem_of_based
    {d : (ι → Valuation A) → Allocation ι A} (hfrugal : IsFrugal d)
    {Q : Finset (Finset A)} {hQempty : ∅ ∈ Q}
    {v : ι → Valuation A} {i : ι}
    (hbased : Valuation.IsBasedOn Q hQempty (v i)) :
    (d v).bundle i ∈ Q := by
  classical
  let B : Finset A := (d v).bundle i
  let feasible := Valuation.feasibleBundles Q B
  have hnonempty : feasible.Nonempty :=
    Valuation.feasibleBundles_nonempty hQempty B
  obtain ⟨C, hCfeasible, hsupC⟩ :=
    Finset.exists_mem_eq_sup' hnonempty (fun C : Finset A => v i C)
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
    linarith

end Frugality

section QuasiField

variable [Fintype A] [DecidableEq A]

/-- A quasi-field of bundles: contains the empty bundle, is closed under
complement relative to all goods, and under disjoint union.

The VCG implementation layer currently needs only the empty-bundle projection;
additional accessor lemmas should be added when a theorem consumes the closure
fields directly. -/
def IsQuasiField (Q : Finset (Finset A)) : Prop :=
  (∅ : Finset A) ∈ Q ∧
    (∀ B ∈ Q, (Finset.univ \ B : Finset A) ∈ Q) ∧
      ∀ B ∈ Q, ∀ C ∈ Q, Disjoint B C → B ∪ C ∈ Q

theorem IsQuasiField.empty_mem {Q : Finset (Finset A)}
    (hQ : IsQuasiField (A := A) Q) :
    (∅ : Finset A) ∈ Q :=
  hQ.1

theorem IsQuasiField.compl_mem {Q : Finset (Finset A)}
    (hQ : IsQuasiField (A := A) Q) {B : Finset A}
    (hB : B ∈ Q) :
    (Finset.univ \ B : Finset A) ∈ Q :=
  hQ.2.1 B hB

theorem IsQuasiField.disjoint_union_mem {Q : Finset (Finset A)}
    (hQ : IsQuasiField (A := A) Q) {B C : Finset A}
    (hB : B ∈ Q) (hC : C ∈ Q) (hdisj : Disjoint B C) :
    B ∪ C ∈ Q :=
  hQ.2.2 B hB C hC hdisj

/-- A quasi-field contains finite unions of pairwise-disjoint member bundles. -/
theorem IsQuasiField.biUnion_mem_of_pairwise_disjoint
    {Q : Finset (Finset A)}
    (hQ : IsQuasiField (A := A) Q)
    {ι : Type}
    (s : Finset ι) (B : ι → Finset A)
    (hmem : ∀ i, i ∈ s → B i ∈ Q)
    (hdisj : ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j → Disjoint (B i) (B j)) :
    s.biUnion B ∈ Q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using hQ.empty_mem
  | insert a s has ih =>
      rw [Finset.biUnion_insert]
      apply hQ.disjoint_union_mem
      · exact hmem a (by simp)
      · apply ih
        · intro i hi
          exact hmem i (by simp [hi])
        · intro i hi j hj hij
          exact hdisj i (by simp [hi]) j (by simp [hj]) hij
      · rw [Finset.disjoint_biUnion_right]
        intro j hj
        have haj : a ≠ j := by
          intro h
          subst h
          exact has hj
        exact hdisj a (by simp) j (by simp [hj]) haj

/-- The residual bundle after a family of `Q`-bundles is again in `Q`. -/
theorem IsQuasiField.residualAfterOpponents_mem
    {Q : Finset (Finset A)}
    (hQ : IsQuasiField (A := A) Q)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (γ : Allocation ι A) (i : ι)
    (hmem : ∀ j, j ≠ i → γ.bundle j ∈ Q) :
    γ.residualAfterOpponents i ∈ Q := by
  classical
  change (Finset.univ \
      ((Finset.univ.filter fun j => j ≠ i).biUnion γ.bundle) : Finset A) ∈ Q
  apply hQ.compl_mem
  apply hQ.biUnion_mem_of_pairwise_disjoint
  · intro j hj
    exact hmem j (by simpa using hj)
  · intro j hj k hk hjk
    exact γ.pairwise_disjoint hjk

end QuasiField

end CombinatorialAuction

end GameTheory
