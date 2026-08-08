/-
# Finite combinatorial-auction primitives

This opt-in mechanism layer defines normalized monotone valuations and feasible
allocations.  It does not commit the core to an auction-specific outcome type.
Ported mathematically from `reference/GameTheory-v1/GameTheory/Auctions/Combinatorial.lean`
at pinned commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic

namespace GameTheory.Mechanism.Combinatorial

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

instance : CoeFun (Valuation A) (fun _ => Finset A → ℝ) := ⟨Valuation.value⟩

@[simp]
theorem empty (v : Valuation A) : v (∅ : Finset A) = 0 := v.empty_value

@[ext]
theorem ext {v w : Valuation A} (h : ∀ B, v B = w B) : v = w := by
  cases v
  cases w
  simp only [Valuation.mk.injEq]
  funext B
  exact h B

theorem mono (v : Valuation A) {B C : Finset A} (hBC : B ⊆ C) : v B ≤ v C :=
  v.monotone hBC

theorem nonneg (v : Valuation A) (B : Finset A) : 0 ≤ v B := by
  rw [← v.empty]
  exact v.mono (by simp)

/-- A valuation that pays `R` exactly on bundles containing nonempty `S`. -/
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

@[simp]
theorem thresholdBundle_apply_of_subset {S B : Finset A} {hS : S.Nonempty}
    {R : ℝ} {hR : 0 ≤ R} (hSB : S ⊆ B) : thresholdBundle S hS R hR B = R := by
  simp [thresholdBundle, hSB]

@[simp]
theorem thresholdBundle_apply_of_not_subset {S B : Finset A} {hS : S.Nonempty}
    {R : ℝ} {hR : 0 ≤ R} (hSB : ¬ S ⊆ B) : thresholdBundle S hS R hR B = 0 := by
  simp [thresholdBundle, hSB]

/-- The zero valuation. -/
instance : Inhabited (Valuation A) where
  default :=
    { value := fun _ => 0
      empty_value := rfl
      monotone := by
        intro _ _ _
        rfl }

/-- Candidate quasi-field bundles contained in `B`. -/
def feasibleBundles (Q : Finset (Finset A)) (B : Finset A) : Finset (Finset A) :=
  Q.filter (fun C => C ⊆ B)

theorem empty_mem_feasibleBundles {Q : Finset (Finset A)} (hQempty : ∅ ∈ Q)
    (B : Finset A) : (∅ : Finset A) ∈ feasibleBundles Q B := by
  simp [feasibleBundles, hQempty]

theorem feasibleBundles_nonempty {Q : Finset (Finset A)} (hQempty : ∅ ∈ Q)
    (B : Finset A) : (feasibleBundles Q B).Nonempty :=
  ⟨∅, empty_mem_feasibleBundles hQempty B⟩

theorem feasibleBundles_mono {Q : Finset (Finset A)} {B C : Finset A} (hBC : B ⊆ C) :
    feasibleBundles Q B ⊆ feasibleBundles Q C := by
  intro D hD
  rcases Finset.mem_filter.mp hD with ⟨hDQ, hDB⟩
  exact Finset.mem_filter.mpr ⟨hDQ, hDB.trans hBC⟩

/-- The `Q`-bundled valuation takes the best `Q`-bundle contained in a bundle. -/
noncomputable def bundling (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (v : Valuation A) : Valuation A where
  value B :=
    (feasibleBundles Q B).sup' (feasibleBundles_nonempty hQempty B) (fun C => v C)
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
    apply Finset.sup'_le
    intro D hD
    exact Finset.le_sup' (fun E => v E) ((feasibleBundles_mono (Q := Q) hBC) hD)

theorem bundling_value_eq_sup (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (v : Valuation A) (B : Finset A) :
    bundling Q hQempty v B =
      (feasibleBundles Q B).sup' (feasibleBundles_nonempty hQempty B) (fun C => v C) :=
  rfl

theorem bundling_le_original (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (v : Valuation A) (B : Finset A) : bundling Q hQempty v B ≤ v B := by
  show (feasibleBundles Q B).sup' (feasibleBundles_nonempty hQempty B) (fun C => v C) ≤ v B
  apply Finset.sup'_le
  intro C hC
  exact v.mono (Finset.mem_filter.mp hC).2

theorem le_bundling_of_mem {Q : Finset (Finset A)} (hQempty : ∅ ∈ Q)
    {v : Valuation A} {B C : Finset A} (hCQ : C ∈ Q) (hCB : C ⊆ B) :
    v C ≤ bundling Q hQempty v B :=
  Finset.le_sup' (fun D => v D) (Finset.mem_filter.mpr ⟨hCQ, hCB⟩)

theorem bundling_eq_original_of_mem {Q : Finset (Finset A)} (hQempty : ∅ ∈ Q)
    {v : Valuation A} {B : Finset A} (hBQ : B ∈ Q) : bundling Q hQempty v B = v B := by
  apply le_antisymm
  · exact bundling_le_original Q hQempty v B
  · exact le_bundling_of_mem hQempty hBQ (by simp)

/-- A valuation is `Q`-based when bundling through `Q` changes nothing. -/
def IsBasedOn (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q) (v : Valuation A) : Prop :=
  ∀ B : Finset A, bundling Q hQempty v B = v B

/-- Bundling is idempotent. -/
theorem bundling_isBasedOn (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (v : Valuation A) : IsBasedOn Q hQempty (bundling Q hQempty v) := by
  intro B
  apply le_antisymm
  · exact bundling_le_original Q hQempty (bundling Q hQempty v) B
  · show (feasibleBundles Q B).sup' (feasibleBundles_nonempty hQempty B) (fun C => v C) ≤
      (feasibleBundles Q B).sup' (feasibleBundles_nonempty hQempty B)
        (fun C => bundling Q hQempty v C)
    apply Finset.sup'_le
    intro C hC
    rcases Finset.mem_filter.mp hC with ⟨hCQ, hCB⟩
    rw [← bundling_eq_original_of_mem (Q := Q) hQempty (v := v) hCQ]
    exact le_bundling_of_mem (Q := Q) hQempty (v := bundling Q hQempty v) hCQ hCB

end Valuation

/-- An allocation gives each buyer a bundle, with distinct bundles disjoint.
The semantic object stores no finiteness or decidable-equality capability. -/
structure Allocation (ι A : Type) where
  /-- Bundle assigned to each buyer. -/
  bundle : ι → Finset A
  /-- Distinct buyers receive disjoint bundles. -/
  pairwise_disjoint : ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (bundle i) (bundle j)

instance : CoeFun (Allocation ι A) (fun _ => ι → Finset A) :=
  ⟨Allocation.bundle⟩

namespace Allocation

variable [DecidableEq ι]
variable (γ : Allocation ι A)

/-- Shrink one buyer's allocated bundle to a sub-bundle. -/
def shrink (i : ι) (B : Finset A) (hB : B ⊆ γ.bundle i) : Allocation ι A where
  bundle j := if j = i then B else γ.bundle j
  pairwise_disjoint := by
    intro j k hjk
    by_cases hji : j = i
    · by_cases hki : k = i
      · exact False.elim (hjk (hji.trans hki.symm))
      · have hBj : B ⊆ γ.bundle j := by simpa [hji] using hB
        simpa only [hji, hki, ↓reduceIte] using
          Disjoint.mono_left hBj (γ.pairwise_disjoint hjk)
    · by_cases hki : k = i
      · have hBk : B ⊆ γ.bundle k := by simpa [hki] using hB
        simpa only [hji, hki, ↓reduceIte] using
          Disjoint.mono_right hBk (γ.pairwise_disjoint hjk)
      · simpa only [hji, hki, ↓reduceIte] using γ.pairwise_disjoint hjk

@[simp]
theorem shrink_bundle_self (i : ι) (B : Finset A) (hB : B ⊆ γ.bundle i) :
    (γ.shrink i B hB).bundle i = B := by
  simp [shrink]

@[simp]
theorem shrink_bundle_ne {i j : ι} (hji : j ≠ i) (B : Finset A)
    (hB : B ⊆ γ.bundle i) : (γ.shrink i B hB).bundle j = γ.bundle j := by
  simp [shrink, hji]

section Residual

variable [DecidableEq A] [Fintype ι] [Fintype A]

/-- Goods remaining after the buyers other than `i` keep their bundles. -/
noncomputable def residualAfterOpponents (i : ι) : Finset A :=
  Finset.univ \ ((Finset.univ.filter fun j => j ≠ i).biUnion γ.bundle)

/-- Give buyer `i` all goods not allocated to the other buyers. -/
noncomputable def giveResidualTo (i : ι) : Allocation ι A where
  bundle j := if j = i then γ.residualAfterOpponents i else γ.bundle j
  pairwise_disjoint := by
    classical
    intro j k hjk
    by_cases hji : j = i
    · have hki : k ≠ i := by
        intro hk
        exact hjk (hji.trans hk.symm)
      rw [if_pos hji, if_neg hki, Finset.disjoint_left]
      intro x hx hxk
      simp only [residualAfterOpponents, Finset.mem_sdiff] at hx
      have hkOpp : k ∈ Finset.univ.filter fun j => j ≠ i :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, hki⟩
      exact hx.2 (Finset.mem_biUnion.mpr ⟨k, hkOpp, hxk⟩)
    · by_cases hki : k = i
      · rw [if_neg hji, if_pos hki, Finset.disjoint_left]
        intro x hxj hx
        simp only [residualAfterOpponents, Finset.mem_sdiff] at hx
        have hjOpp : j ∈ Finset.univ.filter fun j => j ≠ i :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hji⟩
        exact hx.2 (Finset.mem_biUnion.mpr ⟨j, hjOpp, hxj⟩)
      · rw [if_neg hji, if_neg hki]
        exact γ.pairwise_disjoint hjk

@[simp]
theorem giveResidualTo_bundle_self (i : ι) :
    (γ.giveResidualTo i).bundle i = γ.residualAfterOpponents i := by
  simp [giveResidualTo]

@[simp]
theorem giveResidualTo_bundle_ne {i j : ι} (hji : j ≠ i) :
    (γ.giveResidualTo i).bundle j = γ.bundle j := by
  simp [giveResidualTo, hji]

/-- A buyer's old bundle is part of the residual after the other buyers act. -/
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

/-- Empty allocation: every buyer receives no goods. -/
def emptyAllocation (ι A : Type) : Allocation ι A where
  bundle := fun _ => ∅
  pairwise_disjoint := by
    intro _ _ _
    simp

instance allocationInhabited : Inhabited (Allocation ι A) :=
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
  let e : Allocation ι A ≃ {bundle : ι → Finset A // valid bundle} :=
    { toFun := fun γ => ⟨γ.bundle, γ.pairwise_disjoint⟩
      invFun := fun bundle => ⟨bundle.1, bundle.2⟩
      left_inv := by intro γ; cases γ; rfl
      right_inv := by intro bundle; cases bundle; rfl }
  exact Fintype.ofEquiv {bundle : ι → Finset A // valid bundle} e.symm

end GameTheory.Mechanism.Combinatorial
