/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.SchauderFixedPoint
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Tactic

/-!
# KKM Lemma

The Knaster-Kuratowski-Mazurkiewicz lemma for closed covers of the standard
simplex.
-/

open Set Finset

namespace Math
namespace FixedPoint

variable {n : ℕ}

/-- The face of the standard simplex opposite vertex `i`: simplex points with
zero `i`-th coordinate. -/
def simplexFaceOpp (i : Fin n) : Set (Fin n → ℝ) :=
  {x | x i = 0} ∩ stdSimplex ℝ (Fin n)

/-- The KKM condition: every face supported on `σ` is covered by the subfamily
indexed by `σ`. -/
def IsKKMCover (F : Fin n → Set (Fin n → ℝ)) : Prop :=
  ∀ σ : Finset (Fin n),
    (stdSimplex ℝ (Fin n) ∩ {x | ∀ i ∉ σ, x i = 0}) ⊆ ⋃ i ∈ σ, F i

/-- Knaster-Kuratowski-Mazurkiewicz lemma, closed-cover version. -/
theorem kkm_closed_cover (hn : 0 < n)
    (F : Fin n → Set (Fin n → ℝ))
    (hclosed : ∀ i, IsClosed (F i))
    (hkkm : IsKKMCover F) :
    ∃ x ∈ stdSimplex ℝ (Fin n), ∀ i, x ∈ F i := by
  have hF_nonempty : ∀ i, (F i).Nonempty := by
    intro i
    let e : Fin n → ℝ := fun j => if j = i then 1 else 0
    have he_simp : e ∈ stdSimplex ℝ (Fin n) := by
      constructor
      · intro j
        simp [e]
        split <;> norm_num
      · simp [e, Finset.sum_ite_eq', Finset.mem_univ]
    have he_face : ∀ j ∉ ({i} : Finset (Fin n)), e j = 0 := by
      intro j hj
      simp only [e]
      rw [if_neg]
      simp only [Finset.mem_singleton] at hj
      exact hj
    have he_mem : e ∈ ⋃ j ∈ ({i} : Finset (Fin n)), F j :=
      hkkm {i} ⟨he_simp, he_face⟩
    rw [Set.mem_iUnion₂] at he_mem
    obtain ⟨j, hj_mem, hj_F⟩ := he_mem
    simp only [Finset.mem_singleton] at hj_mem
    exact ⟨e, hj_mem ▸ hj_F⟩
  by_contra h_not
  push Not at h_not
  let D : (Fin n → ℝ) → ℝ := fun x => ∑ i : Fin n, Metric.infDist x (F i)
  have hD_pos : ∀ x ∈ stdSimplex ℝ (Fin n), 0 < D x := by
    intro x hx
    obtain ⟨i, hi⟩ := h_not x hx
    have hpos : 0 < Metric.infDist x (F i) := by
      rcases lt_or_eq_of_le (Metric.infDist_nonneg (s := F i) (x := x)) with h | h
      · exact h
      · exfalso
        exact hi (((hclosed i).mem_iff_infDist_zero (hF_nonempty i)).mpr h.symm)
    exact lt_of_lt_of_le hpos
      (Finset.single_le_sum (fun _ _ => Metric.infDist_nonneg) (Finset.mem_univ i))
  let K : Set (Fin n → ℝ) := stdSimplex ℝ (Fin n)
  have hK_ne : K.Nonempty := by
    let i0 : Fin n := ⟨0, hn⟩
    exact ⟨Pi.single i0 1, single_mem_stdSimplex ℝ i0⟩
  let g : K → K := fun x =>
    ⟨fun j => (x.1 j + Metric.infDist x.1 (F j)) / (1 + D x.1), by
      constructor
      · intro j
        exact div_nonneg
          (add_nonneg (x.2.1 j) Metric.infDist_nonneg)
          (by linarith [hD_pos x.1 x.2])
      · rw [← Finset.sum_div]
        rw [div_eq_one_iff_eq (by linarith [hD_pos x.1 x.2] : (1 + D x.1) ≠ 0)]
        simp only [Finset.sum_add_distrib]
        linarith [x.2.2]⟩
  have hg_cont : Continuous g := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    apply Continuous.div
    · exact ((continuous_apply j).comp continuous_subtype_val).add
        ((Metric.continuous_infDist_pt (F j)).comp continuous_subtype_val)
    · exact continuous_const.add
        (continuous_finsetSum _ fun i _ =>
          (Metric.continuous_infDist_pt (F i)).comp continuous_subtype_val)
    · intro x
      linarith [hD_pos x.1 x.2]
  let G : C(K, K) := ⟨g, hg_cont⟩
  obtain ⟨x₀, hfp⟩ :=
    Schauder.schauder_fixed_point
      (convex_stdSimplex ℝ (Fin n))
      (isCompact_stdSimplex ℝ (Fin n))
      hK_ne
      G
  have hfp_coord : ∀ j : Fin n,
      (x₀.1 j + Metric.infDist x₀.1 (F j)) / (1 + D x₀.1) = x₀.1 j := by
    intro j
    exact congr_fun (congr_arg Subtype.val hfp) j
  have hD_ne_zero : 1 + D x₀.1 ≠ 0 := by
    linarith [hD_pos x₀.1 x₀.2]
  have hrearrange : ∀ j : Fin n,
      x₀.1 j * D x₀.1 = Metric.infDist x₀.1 (F j) := by
    intro j
    have h := hfp_coord j
    rw [div_eq_iff hD_ne_zero] at h
    linarith
  let σ : Finset (Fin n) := Finset.filter (fun j => 0 < x₀.1 j) Finset.univ
  have hσ_nonempty : σ.Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    have hall_zero : ∀ j : Fin n, x₀.1 j = 0 := by
      intro j
      have h1 := x₀.2.1 j
      have h2 : ¬ 0 < x₀.1 j := by
        intro hpos
        have : j ∈ σ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩
        rw [h_empty] at this
        simp at this
      linarith
    have hsum_zero : ∑ j : Fin n, x₀.1 j = 0 :=
      Finset.sum_eq_zero fun j _ => hall_zero j
    have hsum_one : ∑ j : Fin n, x₀.1 j = 1 := x₀.2.2
    linarith
  have hx₀_face : x₀.1 ∈ stdSimplex ℝ (Fin n) ∩ {x | ∀ i ∉ σ, x i = 0} := by
    exact ⟨x₀.2, fun i hi => by
      simp only [σ, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      linarith [x₀.2.1 i]⟩
  have hx₀_union : x₀.1 ∈ ⋃ j ∈ σ, F j := hkkm σ hx₀_face
  obtain ⟨j₀, hx₀_union_j₀⟩ := Set.mem_iUnion.mp hx₀_union
  obtain ⟨hj₀_mem, hj₀_F⟩ := Set.mem_iUnion.mp hx₀_union_j₀
  have hj₀_pos : 0 < x₀.1 j₀ := by
    simp only [σ, Finset.mem_filter, Finset.mem_univ, true_and] at hj₀_mem
    exact hj₀_mem
  have hinfDist_zero : Metric.infDist x₀.1 (F j₀) = 0 :=
    ((hclosed j₀).mem_iff_infDist_zero (hF_nonempty j₀)).mp hj₀_F
  have hmul_zero : x₀.1 j₀ * D x₀.1 = 0 := by
    rw [hrearrange j₀, hinfDist_zero]
  have hD_zero : D x₀.1 = 0 := by
    rcases mul_eq_zero.mp hmul_zero with h | h
    · linarith
    · exact h
  linarith [hD_pos x₀.1 x₀.2]

/-- KKM lemma, open-cover variant. If the standard simplex is covered by open
sets `U i` and no `U i` meets the face opposite vertex `i`, then the whole
family has a common point. -/
theorem kkm_open_cover (hn : 0 < n)
    (U : Fin n → Set (Fin n → ℝ))
    (hopen : ∀ i, IsOpen (U i))
    (hface : ∀ i, simplexFaceOpp i ⊆ (U i)ᶜ)
    (hcover : stdSimplex ℝ (Fin n) ⊆ ⋃ i, U i) :
    ∃ x ∈ stdSimplex ℝ (Fin n), ∀ i, x ∈ U i := by
  obtain ⟨φ, htsup, hsum, hnn, _hcompact⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact hopen
      (isCompact_stdSimplex ℝ (Fin n)) hcover
  let F : Fin n → Set (Fin n → ℝ) :=
    fun j => stdSimplex ℝ (Fin n) ∩ {x | ∀ k : Fin n, φ k x ≤ φ j x}
  have hF_closed : ∀ j, IsClosed (F j) := fun j => by
    apply (isCompact_stdSimplex ℝ (Fin n)).isClosed.inter
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun k => isClosed_le (φ k).continuous (φ j).continuous
  have hkkm : IsKKMCover F := by
    intro σ x hx
    rcases hx with ⟨hxS, hxzero⟩
    by_cases hσ : σ.Nonempty
    · obtain ⟨j, hjσ, hjmax⟩ := Finset.exists_max_image σ (fun i => φ i x) hσ
      refine Set.mem_iUnion₂.2 ⟨j, hjσ, ?_⟩
      refine ⟨hxS, ?_⟩
      intro k
      by_cases hkσ : k ∈ σ
      · exact hjmax k hkσ
      · have hxface : x ∈ simplexFaceOpp k := ⟨hxzero k hkσ, hxS⟩
        have hxnotU : x ∉ U k := hface k hxface
        have hφzero : φ k x = 0 := by
          by_contra hne
          exact hxnotU (htsup k (subset_tsupport (φ k) hne))
        rw [hφzero]
        exact (hnn j x).1
    · exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hσ
      have hall_zero : ∀ i : Fin n, x i = 0 := by
        intro i
        exact hxzero i (by simp [hσ])
      have hsum_zero : ∑ i : Fin n, x i = 0 :=
        Finset.sum_eq_zero fun i _ => hall_zero i
      linarith [hxS.2]
  obtain ⟨x, hxS, hxF⟩ := kkm_closed_cover hn F hF_closed hkkm
  refine ⟨x, hxS, fun i => ?_⟩
  have hsumx : (∑ j : Fin n, φ j x) = 1 := by
    simpa [Finset.sum_apply] using hsum hxS
  have hall_eq : ∀ j : Fin n, φ j x = φ i x := by
    intro j
    exact le_antisymm ((hxF i).2 j) ((hxF j).2 i)
  have hpos : 0 < φ i x := by
    have hnonneg : 0 ≤ φ i x := (hnn i x).1
    rcases lt_or_eq_of_le hnonneg with hlt | heq
    · exact hlt
    · exfalso
      have hsum_zero : (∑ j : Fin n, φ j x) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hall_eq j, heq]
      linarith
  exact htsup i (subset_tsupport (φ i) (ne_of_gt hpos))

end FixedPoint
end Math
