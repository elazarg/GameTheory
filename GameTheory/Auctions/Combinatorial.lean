/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
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

end AllocationRules

section Frugality

variable [DecidableEq ι] [DecidableEq A]

/-- Frugality from the paper: every strict sub-bundle of an allocated bundle is
strictly less valuable for that buyer under the reported valuation. -/
def IsFrugal (d : (ι → Valuation A) → Allocation ι A) : Prop :=
  ∀ v i B, B ⊂ (d v).bundle i → v i B < v i ((d v).bundle i)

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
complement relative to all goods, and under disjoint union. -/
def IsQuasiField (Q : Finset (Finset A)) : Prop :=
  (∅ : Finset A) ∈ Q ∧
    (∀ B ∈ Q, (Finset.univ \ B : Finset A) ∈ Q) ∧
      ∀ B ∈ Q, ∀ C ∈ Q, Disjoint B C → B ∪ C ∈ Q

theorem IsQuasiField.empty_mem {Q : Finset (Finset A)}
    (hQ : IsQuasiField (A := A) Q) :
    (∅ : Finset A) ∈ Q :=
  hQ.1

theorem IsQuasiField.compl_mem {Q : Finset (Finset A)}
    (hQ : IsQuasiField (A := A) Q) {B : Finset A} (hB : B ∈ Q) :
    (Finset.univ \ B : Finset A) ∈ Q :=
  hQ.2.1 B hB

theorem IsQuasiField.union_mem_of_disjoint {Q : Finset (Finset A)}
    (hQ : IsQuasiField (A := A) Q) {B C : Finset A}
    (hB : B ∈ Q) (hC : C ∈ Q) (hdisj : Disjoint B C) :
    B ∪ C ∈ Q :=
  hQ.2.2 B hB C hC hdisj

end QuasiField

variable [DecidableEq A]

/-- Valuation profile obtained by bundling every buyer's valuation through the
same quasi-field. -/
noncomputable def bundledProfile (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (v : ι → Valuation A) : ι → Valuation A :=
  fun i => Valuation.bundling Q hQempty (v i)

end CombinatorialAuction

end GameTheory
