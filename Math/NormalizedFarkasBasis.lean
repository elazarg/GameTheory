/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ParametricFarkasBasis
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Basic supports for normalized Farkas polyhedra

This file supplies the static basic-feasible-support step for a standard-form
polyhedron.  At an extreme feasible point, the columns indexed by its positive
support are linearly independent.  The proof is the usual symmetric
support-preserving perturbation argument.

The support columns therefore have a nonsingular Gram matrix.  This avoids
choosing a square row minor and gives a canonical Cramer system for every
finite support.
-/

open Finset Set

namespace Math
namespace LinearAlgebra

noncomputable section

/-- A finite family of analytic quotient candidates which pointwise covers
an analytic target has one fixed candidate covering it throughout a smaller
right neighborhood.  Candidates whose denominator germ is identically zero
are discarded automatically. -/
theorem exists_fixed_eventual_analytic_quotient_eq_of_finite_cover
    {I : Type*} [Finite I]
    (num den : I → ℝ → ℝ) (target : ℝ → ℝ) {x₀ : ℝ}
    (hnum : ∀ i, AnalyticAt ℝ (num i) x₀)
    (hden : ∀ i, AnalyticAt ℝ (den i) x₀)
    (htarget : AnalyticAt ℝ target x₀)
    (hcover :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        ∃ i, den i x ≠ 0 ∧ num i x / den i x = target x) :
    ∃ i,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        den i x ≠ 0 ∧ num i x / den i x = target x := by
  let denSq : I → ℝ → ℝ := fun i x => den i x ^ 2
  let residualSq : I → ℝ → ℝ :=
    fun i x => (num i x - target x * den i x) ^ 2
  have hdenSq : ∀ i, AnalyticAt ℝ (denSq i) x₀ := by
    intro i
    exact (hden i).pow 2
  have hresidualSq :
      ∀ i, AnalyticAt ℝ (residualSq i) x₀ := by
    intro i
    exact ((hnum i).sub (htarget.mul (hden i))).pow 2
  have hdenSq_nonnegative : ∀ i,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        0 ≤ denSq i x :=
    fun i => Filter.Eventually.of_forall fun x => sq_nonneg (den i x)
  have hresidualSq_nonnegative : ∀ i,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        0 ≤ residualSq i x :=
    fun i => Filter.Eventually.of_forall fun x =>
      sq_nonneg (num i x - target x * den i x)
  obtain ⟨denZero, hdenStable⟩ :=
    finite_analytic_nonnegative_family_eventually_active_set
      denSq hdenSq hdenSq_nonnegative
  obtain ⟨residualZero, hresidualStable⟩ :=
    finite_analytic_nonnegative_family_eventually_active_set
      residualSq hresidualSq hresidualSq_nonnegative
  obtain ⟨x, hxDen, hxResidual, i, hdenx, hvaluex⟩ :=
    (hdenStable.and (hresidualStable.and hcover)).exists
  have hiDen : ¬denZero i := by
    exact (hxDen i).2.mp (sq_pos_of_ne_zero hdenx)
  have hresidualx :
      num i x - target x * den i x = 0 := by
    apply sub_eq_zero.mpr
    exact (div_eq_iff hdenx).mp hvaluex
  have hiResidual : residualZero i := by
    exact (hxResidual i).1.mp (by simp [residualSq, hresidualx])
  refine ⟨i, ?_⟩
  filter_upwards [hdenStable, hresidualStable] with y hyDen hyResidual
  have hdenSqPos : 0 < denSq i y :=
    (hyDen i).2.mpr hiDen
  have hresidualSqZero : residualSq i y = 0 :=
    (hyResidual i).1.mpr hiResidual
  have hdeny : den i y ≠ 0 := by
    intro hzero
    simp [denSq, hzero] at hdenSqPos
  have hresidualy :
      num i y - target y * den i y = 0 := by
    simpa [residualSq] using
      (sq_eq_zero_iff.mp hresidualSqZero)
  exact ⟨hdeny, (div_eq_iff hdeny).mpr (sub_eq_zero.mp hresidualy)⟩

/-- A finite conjunction of analytic weak inequalities and equalities has an
eventually fixed truth value for every member of a finite candidate family. -/
theorem finite_analytic_constraint_predicate_stabilizes
    {I J K : Type*} [Finite I] [Finite J] [Finite K]
    (inequality : I → J → ℝ → ℝ)
    (equality : I → K → ℝ → ℝ) {x₀ : ℝ}
    (hinequality : ∀ i j,
      AnalyticAt ℝ (inequality i j) x₀)
    (hequality : ∀ i k,
      AnalyticAt ℝ (equality i k) x₀) :
    ∃ Good : I → Prop,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ i,
        (((∀ j, 0 ≤ inequality i j x) ∧
            ∀ k, equality i k x = 0) ↔ Good i) := by
  let Q := Option (I × J)
  let value : Q → ℝ → ℝ
    | none => fun _ => 0
    | some ij => inequality ij.1 ij.2
  have hvalue : ∀ q, AnalyticAt ℝ (value q) x₀ := by
    intro q
    cases q with
    | none => exact analyticAt_const
    | some ij => exact hinequality ij.1 ij.2
  obtain ⟨R, hR⟩ :=
    finite_analytic_family_eventually_stable value hvalue
  let equalitySq : I × K → ℝ → ℝ :=
    fun ik x => equality ik.1 ik.2 x ^ 2
  have hequalitySq : ∀ ik,
      AnalyticAt ℝ (equalitySq ik) x₀ := by
    intro ik
    exact (hequality ik.1 ik.2).pow 2
  have hequalitySq_nonnegative : ∀ ik,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        0 ≤ equalitySq ik x :=
    fun ik => Filter.Eventually.of_forall fun x =>
      sq_nonneg (equality ik.1 ik.2 x)
  obtain ⟨active, hactive⟩ :=
    finite_analytic_nonnegative_family_eventually_active_set
      equalitySq hequalitySq hequalitySq_nonnegative
  let Good : I → Prop :=
    fun i =>
      (∀ j, R none (some (i, j))) ∧
        ∀ k, active (i, k)
  refine ⟨Good, ?_⟩
  filter_upwards [hR, hactive] with x hxR hxActive
  intro i
  constructor
  · rintro ⟨hineq, heq⟩
    constructor
    · intro j
      exact (hxR none (some (i, j))).mp (by
        simpa [value] using hineq j)
    · intro k
      exact (hxActive (i, k)).1.mp (by
        simp [equalitySq, heq k])
  · rintro ⟨hineq, heq⟩
    constructor
    · intro j
      have := (hxR none (some (i, j))).mpr (hineq j)
      simpa [value] using this
    · intro k
      have hsq := (hxActive (i, k)).1.mpr (heq k)
      simpa [equalitySq] using (sq_eq_zero_iff.mp hsq)

/-- Feasible version of finite analytic quotient freezing.  The finite
analytic constraint atoms prevent selection of an infeasible quotient which
merely happens to have the target value. -/
theorem exists_fixed_eventual_feasible_analytic_quotient_eq
    {I J K : Type*} [Finite I] [Finite J] [Finite K]
    (num den : I → ℝ → ℝ) (target : ℝ → ℝ)
    (inequality : I → J → ℝ → ℝ)
    (equality : I → K → ℝ → ℝ) {x₀ : ℝ}
    (hnum : ∀ i, AnalyticAt ℝ (num i) x₀)
    (hden : ∀ i, AnalyticAt ℝ (den i) x₀)
    (htarget : AnalyticAt ℝ target x₀)
    (hinequality : ∀ i j,
      AnalyticAt ℝ (inequality i j) x₀)
    (hequality : ∀ i k,
      AnalyticAt ℝ (equality i k) x₀)
    (hcover :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        ∃ i,
          (∀ j, 0 ≤ inequality i j x) ∧
          (∀ k, equality i k x = 0) ∧
          den i x ≠ 0 ∧ num i x / den i x = target x) :
    ∃ i,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        (∀ j, 0 ≤ inequality i j x) ∧
        (∀ k, equality i k x = 0) ∧
        den i x ≠ 0 ∧ num i x / den i x = target x := by
  obtain ⟨Good, hgood⟩ :=
    finite_analytic_constraint_predicate_stabilizes
      inequality equality hinequality hequality
  obtain ⟨x, hxGood, i₀, hi₀⟩ := (hgood.and hcover).exists
  have hGoodNonempty : Nonempty {i : I // Good i} := by
    refine ⟨⟨i₀, (hxGood i₀).mp ⟨hi₀.1, hi₀.2.1⟩⟩⟩
  letI : Nonempty {i : I // Good i} := hGoodNonempty
  have hcoverGood :
      ∀ᶠ y in nhdsWithin x₀ (Set.Ioi x₀),
        ∃ i : {i : I // Good i},
          den i.1 y ≠ 0 ∧
            num i.1 y / den i.1 y = target y := by
    filter_upwards [hgood, hcover] with y hyGood hyCover
    obtain ⟨i, hineq, heq, hdeni, hvalue⟩ := hyCover
    exact ⟨⟨i, (hyGood i).mp ⟨hineq, heq⟩⟩, hdeni, hvalue⟩
  obtain ⟨i, hi⟩ :=
    exists_fixed_eventual_analytic_quotient_eq_of_finite_cover
      (fun i : {i : I // Good i} => num i.1)
      (fun i : {i : I // Good i} => den i.1)
      target (fun i => hnum i.1) (fun i => hden i.1)
      htarget hcoverGood
  refine ⟨i.1, ?_⟩
  filter_upwards [hgood, hi] with y hyGood hy
  have hconstraints := (hyGood i.1).mpr i.2
  exact ⟨hconstraints.1, hconstraints.2, hy.1, hy.2⟩

/-- A standard-form nonnegative affine fiber. -/
def standardFeasibleSet
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ) : Set (Col → ℝ) :=
  {z | (∀ j, 0 ≤ z j) ∧ Matrix.mulVec A z = rhs}

/-- A feasible vector is optimal for a moving linear objective. -/
def IsStandardOptimal
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    (objective : Col → ℝ) (z : Col → ℝ) : Prop :=
  z ∈ standardFeasibleSet A rhs ∧
    ∀ w ∈ standardFeasibleSet A rhs,
      (∑ j, objective j * w j) ≤ ∑ j, objective j * z j

/-- The continuous linear functional represented by a finite coefficient
vector. -/
def finiteDotContinuousLinearMap
    {Col : Type*} [Fintype Col] (c : Col → ℝ) :
    (Col → ℝ) →L[ℝ] ℝ :=
  ∑ j, c j • ContinuousLinearMap.proj j

@[simp]
theorem finiteDotContinuousLinearMap_apply
    {Col : Type*} [Fintype Col] (c z : Col → ℝ) :
    finiteDotContinuousLinearMap c z = ∑ j, c j * z j := by
  simp [finiteDotContinuousLinearMap]

/-- A standard-form nonnegative affine fiber is closed. -/
theorem isClosed_standardFeasibleSet
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ) :
    IsClosed (standardFeasibleSet A rhs) := by
  rw [show standardFeasibleSet A rhs =
      (⋂ j, {z : Col → ℝ | 0 ≤ z j}) ∩
        ⋂ i, {z : Col → ℝ | Matrix.mulVec A z i = rhs i} by
    ext z
    simp only [standardFeasibleSet, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter]
    constructor
    · rintro ⟨hz, heq⟩
      exact ⟨hz, fun i => congrFun heq i⟩
    · rintro ⟨hz, heq⟩
      exact ⟨hz, funext heq⟩]
  apply IsClosed.inter
  · exact isClosed_iInter fun j =>
      isClosed_le continuous_const (continuous_apply j)
  · exact isClosed_iInter fun i =>
      isClosed_eq (by
        change Continuous (fun z : Col → ℝ => ∑ j, A i j * z j)
        exact continuous_finsetSum _ fun j _ =>
          continuous_const.mul (continuous_apply j)) continuous_const

/-- Every attained linear optimum over a standard-form nonnegative affine
fiber is attained at an extreme point.

The feasible set need not be bounded.  The proof first passes to the exposed
optimal face, minimizes total nonnegative mass there, and applies
Krein--Milman to the resulting compact minimum-mass face. -/
theorem exists_extreme_standardOptimal_of_standardOptimal
    {Row Col : Type*}
    [Fintype Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ) (objective : Col → ℝ)
    {z : Col → ℝ}
    (hz : IsStandardOptimal A rhs objective z) :
    ∃ zExtreme : Col → ℝ,
      zExtreme ∈ (standardFeasibleSet A rhs).extremePoints ℝ ∧
        IsStandardOptimal A rhs objective zExtreme ∧
        (∑ j, objective j * zExtreme j) =
          ∑ j, objective j * z j := by
  classical
  let feasible : Set (Col → ℝ) := standardFeasibleSet A rhs
  let objectiveMap : (Col → ℝ) →L[ℝ] ℝ :=
    finiteDotContinuousLinearMap objective
  let massMap : (Col → ℝ) →L[ℝ] ℝ :=
    finiteDotContinuousLinearMap (fun _ => 1)
  let optimalFace : Set (Col → ℝ) :=
    objectiveMap.toExposed feasible
  have hzOptimalFace : z ∈ optimalFace := by
    refine ⟨hz.1, ?_⟩
    intro w hw
    simpa [objectiveMap, finiteDotContinuousLinearMap_apply] using hz.2 w hw
  have hoptimalExposed : IsExposed ℝ feasible optimalFace :=
    ContinuousLinearMap.toExposed.isExposed
  have hfeasibleClosed : IsClosed feasible := by
    exact isClosed_standardFeasibleSet A rhs
  have hoptimalClosed : IsClosed optimalFace :=
    hoptimalExposed.isClosed hfeasibleClosed
  let upper : Col → ℝ := fun _ => massMap z
  let truncated : Set (Col → ℝ) := optimalFace ∩ Set.Icc 0 upper
  have hzMassNonneg : 0 ≤ massMap z := by
    simpa [massMap, finiteDotContinuousLinearMap_apply] using
      (Finset.sum_nonneg fun j _ => hz.1.1 j)
  have hzTruncated : z ∈ truncated := by
    refine ⟨hzOptimalFace, ?_⟩
    constructor
    · exact hz.1.1
    · intro j
      change z j ≤ massMap z
      simpa [massMap, finiteDotContinuousLinearMap_apply] using
        (Finset.single_le_sum
          (fun k _ => hz.1.1 k) (Finset.mem_univ j))
  have htruncatedCompact : IsCompact truncated := by
    have hcompactBox : IsCompact (Set.Icc (0 : Col → ℝ) upper) :=
      isCompact_Icc
    simpa [truncated, Set.inter_comm] using
      hcompactBox.inter_right hoptimalClosed
  obtain ⟨m, hmTruncated, hmMin⟩ :=
    htruncatedCompact.exists_isMinOn
      ⟨z, hzTruncated⟩ massMap.continuous.continuousOn
  have hmOptimalFace : m ∈ optimalFace := hmTruncated.1
  have hmGlobalMin : ∀ w ∈ optimalFace, massMap m ≤ massMap w := by
    intro w hw
    by_cases hwMass : massMap w ≤ massMap z
    · apply hmMin
      refine ⟨hw, ?_⟩
      constructor
      · exact (hoptimalExposed.subset hw).1
      · intro j
        calc
          w j ≤ massMap w := by
            simpa [massMap, finiteDotContinuousLinearMap_apply] using
              (Finset.single_le_sum
                (fun k _ => (hoptimalExposed.subset hw).1 k)
                (Finset.mem_univ j))
          _ ≤ upper j := hwMass
    · exact (hmMin hzTruncated).trans (le_of_lt (lt_of_not_ge hwMass))
  let minimumMassFace : Set (Col → ℝ) :=
    (-massMap).toExposed optimalFace
  have hmMinimumMassFace : m ∈ minimumMassFace := by
    refine ⟨hmOptimalFace, ?_⟩
    intro w hw
    simpa using neg_le_neg (hmGlobalMin w hw)
  have hminimumMassExposed :
      IsExposed ℝ optimalFace minimumMassFace :=
    ContinuousLinearMap.toExposed.isExposed
  let minimumUpper : Col → ℝ := fun _ => massMap m
  have hminimumMassFace_subset :
      minimumMassFace ⊆ Set.Icc (0 : Col → ℝ) minimumUpper := by
    intro w hw
    have hwFeasible := hoptimalExposed.subset (hminimumMassExposed.subset hw)
    have hwMassLe : massMap w ≤ massMap m := by
      have := hw.2 m hmOptimalFace
      simpa using neg_le_neg this
    constructor
    · exact hwFeasible.1
    · intro j
      calc
        w j ≤ massMap w := by
          simpa [massMap, finiteDotContinuousLinearMap_apply] using
            (Finset.single_le_sum
              (fun k _ => hwFeasible.1 k) (Finset.mem_univ j))
        _ ≤ minimumUpper j := hwMassLe
  have hminimumMassCompact : IsCompact minimumMassFace := by
    exact isCompact_Icc.of_isClosed_subset
      (hminimumMassExposed.isClosed hoptimalClosed)
      hminimumMassFace_subset
  obtain ⟨zExtreme, hzExtremeMinimum⟩ :=
    hminimumMassCompact.extremePoints_nonempty
      ⟨m, hmMinimumMassFace⟩
  have hzExtremeFeasible :
      zExtreme ∈ feasible :=
    hoptimalExposed.subset
      (hminimumMassExposed.subset
        (extremePoints_subset hzExtremeMinimum))
  have hzExtremeOriginal :
      zExtreme ∈ feasible.extremePoints ℝ := by
    exact (hoptimalExposed.isExtreme.trans
      hminimumMassExposed.isExtreme).extremePoints_subset_extremePoints
        hzExtremeMinimum
  have hzExtremeOptimalFace :
      zExtreme ∈ optimalFace :=
    hminimumMassExposed.subset
      (extremePoints_subset hzExtremeMinimum)
  have hzExtremeOptimal :
      IsStandardOptimal A rhs objective zExtreme := by
    constructor
    · exact hzExtremeFeasible
    · intro w hw
      simpa [objectiveMap, finiteDotContinuousLinearMap_apply] using
        hzExtremeOptimalFace.2 w hw
  have hvalue :
      (∑ j, objective j * zExtreme j) =
        ∑ j, objective j * z j := by
    apply le_antisymm
    · exact hz.2 zExtreme hzExtremeFeasible
    · exact hzExtremeOptimal.2 z hz.1
  exact ⟨zExtreme, hzExtremeOriginal, hzExtremeOptimal, hvalue⟩

/-- An extreme point of a standard-form nonnegative affine fiber admits
no nonzero kernel direction supported on its positive coordinates. -/
theorem eq_zero_of_extreme_standardFeasible
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    {z d : Col → ℝ}
    (hz : z ∈ (standardFeasibleSet A rhs).extremePoints ℝ)
    (hd_supp : ∀ j, z j = 0 → d j = 0)
    (hd_kernel : Matrix.mulVec A d = 0) :
    d = 0 := by
  classical
  by_contra hd_ne
  have hCol : Nonempty Col := by
    by_contra h
    haveI : IsEmpty Col := not_nonempty_iff.mp h
    exact hd_ne (Subsingleton.elim d 0)
  letI := hCol
  obtain ⟨hz_nonnegative, hz_equation⟩ := extremePoints_subset hz
  have hbound_pos :
      ∀ j : Col,
        (0 : ℝ) <
          if z j = 0 then 1 else z j / (|d j| + 1) := by
    intro j
    split_ifs with hj
    · norm_num
    · have hzj_pos : 0 < z j :=
        lt_of_le_of_ne (hz_nonnegative j) (Ne.symm hj)
      positivity
  let ε : ℝ :=
    Finset.univ.inf' Finset.univ_nonempty
      (fun j : Col =>
        if z j = 0 then (1 : ℝ) else z j / (|d j| + 1))
  have hε_pos : 0 < ε := by
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
      fun j _ => hbound_pos j
  have hε_le :
      ∀ j : Col,
        ε ≤ if z j = 0 then (1 : ℝ)
          else z j / (|d j| + 1) := by
    intro j
    exact Finset.inf'_le
      (fun k : Col =>
        if z k = 0 then (1 : ℝ) else z k / (|d k| + 1))
      (Finset.mem_univ j)
  have hcoordinate_bound : ∀ j, ε * |d j| ≤ z j := by
    intro j
    by_cases hzj : z j = 0
    · rw [hzj, hd_supp j hzj]
      simp
    · have hbound := hε_le j
      simp only [hzj, if_false] at hbound
      have hdenom_pos : (0 : ℝ) < |d j| + 1 := by positivity
      have hfull :
          ε * (|d j| + 1) ≤ z j :=
        (le_div_iff₀ hdenom_pos).mp hbound
      nlinarith
  have habs :
      ∀ (j : Col) (σ : ℝ), σ = 1 ∨ σ = -1 →
        |σ * (ε * d j)| ≤ z j := by
    intro j σ hσ
    have hσ_abs : |σ| = 1 := by
      rcases hσ with rfl | rfl <;> norm_num
    calc
      |σ * (ε * d j)| = ε * |d j| := by
        rw [abs_mul, abs_mul, hσ_abs, one_mul, abs_of_pos hε_pos]
      _ ≤ z j := hcoordinate_bound j
  have hmem :
      ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
        (fun j => z j + σ * (ε * d j)) ∈
          standardFeasibleSet A rhs := by
    intro σ hσ
    constructor
    · intro j
      linarith [(abs_le.mp (habs j σ hσ)).1]
    · have hvector :
          (fun j => z j + σ * (ε * d j)) =
            z + (σ * ε) • d := by
        funext j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hvector, Matrix.mulVec_add, Matrix.mulVec_smul,
        hz_equation, hd_kernel]
      simp
  have hplus := hmem 1 (Or.inl rfl)
  have hminus := hmem (-1) (Or.inr rfl)
  simp only [one_mul] at hplus
  have hsegment :
      z ∈ openSegment ℝ
        (fun j => z j + ε * d j)
        (fun j => z j + (-1) * (ε * d j)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heq := hz.2 hplus hminus hsegment
  apply hd_ne
  funext j
  have hj : z j + ε * d j = z j := congrFun heq j
  rcases mul_eq_zero.mp (show ε * d j = 0 by linarith) with hε | hd
  · exact False.elim (hε_pos.ne' hε)
  · exact hd

/-- The columns carrying the positive support of an extreme standard-form
feasible point are linearly independent. -/
theorem linearIndependent_supportColumns_of_extreme_standardFeasible
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    {z : Col → ℝ}
    (hz : z ∈ (standardFeasibleSet A rhs).extremePoints ℝ) :
    LinearIndependent ℝ
      (fun j : {j : Col // z j ≠ 0} => A.col j.1) := by
  classical
  apply Fintype.linearIndependent_iffₛ.mpr
  intro f g hfg j
  let d : Col → ℝ :=
    ∑ k : {k : Col // z k ≠ 0},
      (f k - g k) • Pi.single k.1 1
  have hd_supp : ∀ k, z k = 0 → d k = 0 := by
    intro k hk
    simp only [d, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hne : k ≠ i.1 := by
      intro hki
      apply i.property
      rw [← hki]
      exact hk
    rw [if_neg hne]
    simp
  have hd_kernel : Matrix.mulVec A d = 0 := by
    have hcombination :
        (∑ k : {k : Col // z k ≠ 0},
            (f k - g k) • A.col k.1) = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, hfg, sub_self]
    have hsingle :
        ∀ k : {k : Col // z k ≠ 0},
          Matrix.mulVec A (Pi.single k.1 1) = A.col k.1 := by
      intro k
      exact Matrix.mulVec_single_one A k.1
    calc
      Matrix.mulVec A d =
          ∑ k : {k : Col // z k ≠ 0},
            (f k - g k) •
              Matrix.mulVec A (Pi.single k.1 1) := by
        change A.mulVecLin d = _
        simp [d]
      _ = ∑ k : {k : Col // z k ≠ 0},
            (f k - g k) • A.col k.1 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hsingle k]
      _ = 0 := hcombination
  have hd_zero :=
    eq_zero_of_extreme_standardFeasible
      A rhs hz hd_supp hd_kernel
  have hj := congrFun hd_zero j.1
  have hd_eval : d j.1 = f j - g j := by
    simp only [d, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      have hne : j.1 ≠ k.1 := by
        intro heq
        apply hkj
        exact Subtype.ext heq.symm
      rw [if_neg hne]
      simp
    · simp
  rw [hd_eval] at hj
  exact sub_eq_zero.mp hj

/-- The Gram matrix of the positive support columns of an extreme feasible
point is nonsingular. -/
theorem det_supportGram_ne_zero_of_extreme_standardFeasible
    {Row Col : Type*} [Fintype Row] [Fintype Col] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    {z : Col → ℝ}
    (hz : z ∈ (standardFeasibleSet A rhs).extremePoints ℝ) :
    let C : Matrix Row {j : Col // z j ≠ 0} ℝ :=
      A.submatrix id Subtype.val
    (C.transpose * C).det ≠ 0 := by
  classical
  dsimp only
  let C : Matrix Row {j : Col // z j ≠ 0} ℝ :=
    A.submatrix id Subtype.val
  have hcolumns : LinearIndependent ℝ C.col := by
    exact linearIndependent_supportColumns_of_extreme_standardFeasible
      A rhs hz
  have hinjective : Function.Injective C.mulVec :=
    Matrix.mulVec_injective_iff.mpr hcolumns
  have hker : LinearMap.ker C.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinjective
  have hgramKer :
      LinearMap.ker (C.transpose * C).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact hker
  have hgramInjective :
      Function.Injective (C.transpose * C).mulVec :=
    LinearMap.ker_eq_bot.mp hgramKer
  have hgramUnit : IsUnit (C.transpose * C) :=
    Matrix.mulVec_injective_iff_isUnit.mp hgramInjective
  exact (hgramUnit.map Matrix.detMonoidHom).ne_zero

/-- Matrix formed by the columns in a selected support. -/
def supportColumnMatrix
    {Row Col : Type*} [DecidableEq Col]
    (A : Matrix Row Col ℝ) (support : Finset Col) :
    Matrix Row support ℝ :=
  A.submatrix id Subtype.val

/-- Gram matrix attached to a selected finite support. -/
def supportGram
    {Row Col : Type*} [Fintype Row] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (support : Finset Col) :
    Matrix support support ℝ :=
  let C := supportColumnMatrix A support
  C.transpose * C

/-- Right-hand side of the support Gram system. -/
def supportGramRhs
    {Row Col : Type*} [Fintype Row] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    (support : Finset Col) : support → ℝ :=
  Matrix.mulVec (supportColumnMatrix A support).transpose rhs

/-- Cramer coordinate associated with one selected support. -/
def supportCramerCoordinate
    {Row Col : Type*} [Fintype Row] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    (support : Finset Col) (j : support) : ℝ :=
  Matrix.cramer (supportGram A support)
      (supportGramRhs A rhs support) j /
    (supportGram A support).det

/-- Extend the Cramer coordinates of one support by zero outside it. -/
def supportCramerVector
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    (support : Finset Col) : Col → ℝ :=
  fun j =>
    if hj : j ∈ support then
      supportCramerCoordinate A rhs support ⟨j, hj⟩
    else 0

/-- The finite positive support of a nonnegative coefficient vector. -/
def positiveSupport
    {Col : Type*} [Fintype Col] (z : Col → ℝ) : Finset Col :=
  Finset.univ.filter fun j => z j ≠ 0

theorem sum_positiveSupport
    {Col E : Type*} [Fintype Col] [AddCommMonoid E]
    (z : Col → ℝ) (f : Col → E)
    (hzero : ∀ j, z j = 0 → f j = 0) :
    (∑ j : positiveSupport z, f j.1) = ∑ j, f j := by
  classical
  rw [← Finset.sum_subtype (positiveSupport z)
    (fun _ => Iff.rfl) f]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  apply hzero j
  simpa [positiveSupport] using hj

/-- The columns in the finite positive-support representation of an extreme
point are linearly independent. -/
theorem linearIndependent_positiveSupportColumns_of_extreme
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    {z : Col → ℝ}
    (hz : z ∈ (standardFeasibleSet A rhs).extremePoints ℝ) :
    LinearIndependent ℝ
      (fun j : positiveSupport z => A.col j.1) := by
  classical
  let e : positiveSupport z ≃ {j : Col // z j ≠ 0} :=
    Equiv.subtypeEquivRight fun j => by
      simp [positiveSupport]
  have hsource :=
    linearIndependent_supportColumns_of_extreme_standardFeasible
      A rhs hz
  have hcomp :
      (fun j : positiveSupport z => A.col j.1) =
        (fun j : {j : Col // z j ≠ 0} => A.col j.1) ∘ e := rfl
  rw [hcomp, linearIndependent_equiv]
  exact hsource

/-- Nonsingularity of the Gram system for an arbitrary linearly independent
selected column support. -/
theorem det_supportGram_ne_zero_of_linearIndependent
    {Row Col : Type*} [Fintype Row] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (support : Finset Col)
    (hindependent :
      LinearIndependent ℝ
        (fun j : support => A.col j.1)) :
    (supportGram A support).det ≠ 0 := by
  let C := supportColumnMatrix A support
  have hcolumns : LinearIndependent ℝ C.col := hindependent
  have hinjective : Function.Injective C.mulVec :=
    Matrix.mulVec_injective_iff.mpr hcolumns
  have hker : LinearMap.ker C.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinjective
  have hgramKer :
      LinearMap.ker (C.transpose * C).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact hker
  have hgramInjective :
      Function.Injective (C.transpose * C).mulVec :=
    LinearMap.ker_eq_bot.mp hgramKer
  have hgramUnit : IsUnit (C.transpose * C) :=
    Matrix.mulVec_injective_iff_isUnit.mp hgramInjective
  exact (hgramUnit.map Matrix.detMonoidHom).ne_zero

/-- At an extreme feasible point, the Cramer coordinates of its positive
support Gram system recover its actual positive coordinates exactly. -/
theorem supportCramerCoordinate_eq_of_extreme
    {Row Col : Type*}
    [Fintype Row] [Fintype Col] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    {z : Col → ℝ}
    (hz : z ∈ (standardFeasibleSet A rhs).extremePoints ℝ)
    (j : positiveSupport z) :
    supportCramerCoordinate A rhs (positiveSupport z) j = z j.1 := by
  classical
  let support := positiveSupport z
  let C := supportColumnMatrix A support
  let restricted : support → ℝ := fun k => z k.1
  have hindependent :
      LinearIndependent ℝ (fun k : support => A.col k.1) := by
    exact linearIndependent_positiveSupportColumns_of_extreme
      A rhs hz
  have hdet : (supportGram A support).det ≠ 0 :=
    det_supportGram_ne_zero_of_linearIndependent
      A support hindependent
  have hCrestricted : Matrix.mulVec C restricted = rhs := by
    obtain ⟨_, hzEquation⟩ := extremePoints_subset hz
    rw [← hzEquation]
    ext i
    simp only [C, supportColumnMatrix, Matrix.mulVec,
      dotProduct, Matrix.submatrix_apply, id_eq, restricted]
    exact sum_positiveSupport z
      (fun k => A i k * z k) (fun k hk => by simp [hk])
  have hrestrictedEquation :
      Matrix.mulVec (supportGram A support) restricted =
        supportGramRhs A rhs support := by
    rw [supportGram, supportGramRhs, ← Matrix.mulVec_mulVec,
      hCrestricted]
  have hcEquation :
      Matrix.mulVec (supportGram A support)
          (fun k =>
            Matrix.cramer (supportGram A support)
                (supportGramRhs A rhs support) k /
              (supportGram A support).det) =
        supportGramRhs A rhs support :=
    matrix_mulVec_cramer_div_det
      (supportGram A support) (supportGramRhs A rhs support) hdet
  have hunit : IsUnit (supportGram A support) :=
    (supportGram A support).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr hdet)
  have hinjective :
      Function.Injective (supportGram A support).mulVec :=
    Matrix.mulVec_injective_of_isUnit hunit
  have heq := hinjective (hcEquation.trans hrestrictedEquation.symm)
  exact congrFun heq j

/-- The full zero-extended Cramer vector of an extreme feasible point's
positive support is exactly that point.  The support may be empty, and no
positivity is required of any distinguished mass coordinate. -/
theorem supportCramerVector_eq_of_extreme
    {Row Col : Type*}
    [Fintype Row] [Fintype Col] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    {z : Col → ℝ}
    (hz : z ∈ (standardFeasibleSet A rhs).extremePoints ℝ) :
    supportCramerVector A rhs (positiveSupport z) = z := by
  funext j
  by_cases hj : j ∈ positiveSupport z
  · rw [supportCramerVector, dif_pos hj]
    exact supportCramerCoordinate_eq_of_extreme A rhs hz ⟨j, hj⟩
  · rw [supportCramerVector, dif_neg hj]
    have hzj : z j = 0 := by
      simpa [positiveSupport] using hj
    exact hzj.symm

/-- Static basic-feasible-solution coverage: every extreme optimal point is
represented exactly by the Cramer system of one nonsingular support Gram
matrix, and that candidate attains the full standard-form optimum.

The support can have any cardinality, including zero.  Variables absent from
the normalizing mass functional are ordinary columns and are covered without
a separate nondegeneracy assumption. -/
theorem exists_supportCramerBasis_of_extreme_optimal
    {Row Col : Type*}
    [Fintype Row] [Fintype Col] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    (objective : Col → ℝ) {z : Col → ℝ}
    (hzExtreme :
      z ∈ (standardFeasibleSet A rhs).extremePoints ℝ)
    (hzOptimal : IsStandardOptimal A rhs objective z) :
    ∃ support : Finset Col,
      (supportGram A support).det ≠ 0 ∧
        supportCramerVector A rhs support = z ∧
        IsStandardOptimal A rhs objective
          (supportCramerVector A rhs support) := by
  let support := positiveSupport z
  have hindependent :
      LinearIndependent ℝ
        (fun j : support => A.col j.1) := by
    exact linearIndependent_positiveSupportColumns_of_extreme
      A rhs hzExtreme
  have hdet : (supportGram A support).det ≠ 0 :=
    det_supportGram_ne_zero_of_linearIndependent
      A support hindependent
  have heq : supportCramerVector A rhs support = z :=
    supportCramerVector_eq_of_extreme A rhs hzExtreme
  exact ⟨support, hdet, heq, heq.symm ▸ hzOptimal⟩

/-- Add a normalizing mass row to a homogeneous Farkas balance matrix. -/
def normalizedFarkasMatrix
    {Row Col : Type*}
    (balance : Matrix Row Col ℝ) (mass : Col → ℝ) :
    Matrix (Sum Row Unit) Col ℝ
  | Sum.inl i, j => balance i j
  | Sum.inr _, j => mass j

/-- Right-hand side for a normalized homogeneous Farkas certificate. -/
def normalizedFarkasRhs
    {Row : Type*} : Sum Row Unit → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- Nonnegative normalized Farkas certificates. -/
def normalizedFarkasCertificateSet
    {Row Col : Type*} [Fintype Col]
    (balance : Matrix Row Col ℝ) (mass : Col → ℝ) :
    Set (Col → ℝ) :=
  standardFeasibleSet
    (normalizedFarkasMatrix balance mass)
    normalizedFarkasRhs

/-- Objective numerator of a support Cramer candidate. -/
def supportObjectiveNumerator
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    (objective : Col → ℝ) (support : Finset Col) : ℝ :=
  ∑ j : support,
    objective j.1 *
      Matrix.cramer (supportGram A support)
        (supportGramRhs A rhs support) j

/-- Cleared coordinate inequality for a support Cramer candidate. -/
def supportCoordinateNumerator
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    (support : Finset Col) (j : Col) : ℝ :=
  if hj : j ∈ support then
    Matrix.cramer (supportGram A support)
        (supportGramRhs A rhs support) ⟨j, hj⟩ *
      (supportGram A support).det
  else 0

/-- Cleared affine-equation residual for a support Cramer candidate. -/
def supportEquationResidual
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    (support : Finset Col) (i : Row) : ℝ :=
  (∑ j : support,
      A i j.1 *
        Matrix.cramer (supportGram A support)
          (supportGramRhs A rhs support) j) -
    rhs i * (supportGram A support).det

/-- The quotient of the support objective numerator by the Gram
determinant is the objective of the zero-extended Cramer vector. -/
theorem supportObjectiveNumerator_div_det
    {Row Col : Type*}
    [Fintype Row] [Fintype Col] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    (objective : Col → ℝ) (support : Finset Col) :
    supportObjectiveNumerator A rhs objective support /
        (supportGram A support).det =
      ∑ j, objective j * supportCramerVector A rhs support j := by
  classical
  rw [supportObjectiveNumerator, Finset.sum_div]
  have hsupport :
      (∑ j : support,
          objective j.1 *
            supportCramerVector A rhs support j.1) =
        ∑ j, objective j *
          supportCramerVector A rhs support j := by
    rw [← Finset.sum_subtype support (fun _ => Iff.rfl)
      (fun j => objective j *
        supportCramerVector A rhs support j)]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    simp [supportCramerVector, hj]
  rw [← hsupport]
  apply Finset.sum_congr rfl
  intro j _
  simp [supportCramerVector, j.property,
    supportCramerCoordinate]
  ring

/-- Cleared coordinate and affine-equation atoms characterize feasibility of
a nonsingular support Cramer candidate. -/
theorem supportCramer_feasible_iff_atoms
    {Row Col : Type*}
    [Fintype Row] [Fintype Col] [DecidableEq Col]
    (A : Matrix Row Col ℝ) (rhs : Row → ℝ)
    (support : Finset Col)
    (hdet : (supportGram A support).det ≠ 0) :
    supportCramerVector A rhs support ∈ standardFeasibleSet A rhs ↔
      (∀ j, 0 ≤ supportCoordinateNumerator A rhs support j) ∧
        ∀ i, supportEquationResidual A rhs support i = 0 := by
  classical
  constructor
  · rintro ⟨hnonnegative, hequation⟩
    constructor
    · intro j
      by_cases hj : j ∈ support
      · have hcoord := hnonnegative j
        simp only [supportCramerVector, dif_pos hj,
          supportCramerCoordinate] at hcoord
        rw [supportCoordinateNumerator, dif_pos hj]
        exact (cramerBasisCoordinate_nonneg_iff
          (fun _ => supportGram A support)
          (fun _ => supportGramRhs A rhs support)
          ⟨j, hj⟩ 0 hdet).mp hcoord
      · simp [supportCoordinateNumerator, hj]
    · intro i
      have hi := congrFun hequation i
      simp only [Matrix.mulVec, dotProduct] at hi
      have hsupport :
          (∑ x : support,
              A i x.1 *
                supportCramerVector A rhs support x.1) =
            ∑ x,
              A i x * supportCramerVector A rhs support x := by
        rw [← Finset.sum_subtype support (fun _ => Iff.rfl)
          (fun x =>
            A i x * supportCramerVector A rhs support x)]
        apply Finset.sum_subset (Finset.subset_univ _)
        intro x _ hx
        simp [supportCramerVector, hx]
      rw [← hsupport] at hi
      simp only [univ_eq_attach, supportCramerVector, SetLike.coe_mem, ↓reduceDIte,
        supportCramerCoordinate, Subtype.coe_eta] at hi
      have hdiv :
          (∑ x : support,
              A i x.1 *
                Matrix.cramer (supportGram A support)
                  (supportGramRhs A rhs support) x) /
                (supportGram A support).det =
            rhs i := by
        rw [Finset.sum_div]
        simpa only [Finset.univ_eq_attach, mul_div_assoc] using hi
      rw [supportEquationResidual]
      exact sub_eq_zero.mpr ((div_eq_iff hdet).mp hdiv)
  · rintro ⟨hnonnegative, hequation⟩
    constructor
    · intro j
      by_cases hj : j ∈ support
      · have hcoord := hnonnegative j
        rw [supportCoordinateNumerator, dif_pos hj] at hcoord
        simp only [supportCramerVector, dif_pos hj,
          supportCramerCoordinate]
        exact (cramerBasisCoordinate_nonneg_iff
          (fun _ => supportGram A support)
          (fun _ => supportGramRhs A rhs support)
          ⟨j, hj⟩ 0 hdet).mpr hcoord
      · simp [supportCramerVector, hj]
    · funext i
      have hi := hequation i
      simp only [Matrix.mulVec, dotProduct]
      have hsupport :
          (∑ x : support,
              A i x.1 *
                supportCramerVector A rhs support x.1) =
            ∑ x,
              A i x * supportCramerVector A rhs support x := by
        rw [← Finset.sum_subtype support (fun _ => Iff.rfl)
          (fun x =>
            A i x * supportCramerVector A rhs support x)]
        apply Finset.sum_subset (Finset.subset_univ _)
        intro x _ hx
        simp [supportCramerVector, hx]
      rw [← hsupport]
      simp only [univ_eq_attach, supportCramerVector, SetLike.coe_mem, ↓reduceDIte,
        supportCramerCoordinate, Subtype.coe_eta]
      have hcleared :
          (∑ x : support,
              A i x.1 *
                Matrix.cramer (supportGram A support)
                  (supportGramRhs A rhs support) x) =
            rhs i * (supportGram A support).det := by
        exact sub_eq_zero.mp (by
          simpa only [supportEquationResidual] using hi)
      have hdiv :
          (∑ x : support,
              A i x.1 *
                Matrix.cramer (supportGram A support)
                  (supportGramRhs A rhs support) x) /
                (supportGram A support).det =
            rhs i :=
        (div_eq_iff hdet).mpr hcleared
      rw [Finset.sum_div] at hdiv
      simpa only [Finset.univ_eq_attach, mul_div_assoc] using hdiv

/-- Moving support objective numerator. -/
def parametricSupportObjectiveNumerator
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : ℝ → Matrix Row Col ℝ) (rhs : ℝ → Row → ℝ)
    (objective : ℝ → Col → ℝ)
    (support : Finset Col) (x : ℝ) : ℝ :=
  supportObjectiveNumerator (A x) (rhs x) (objective x) support

/-- Moving support Gram determinant. -/
def parametricSupportDeterminant
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : ℝ → Matrix Row Col ℝ)
    (support : Finset Col) (x : ℝ) : ℝ :=
  (supportGram (A x) support).det

/-- Moving cleared coordinate atom. -/
def parametricSupportCoordinateNumerator
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : ℝ → Matrix Row Col ℝ) (rhs : ℝ → Row → ℝ)
    (support : Finset Col) (j : Col) (x : ℝ) : ℝ :=
  supportCoordinateNumerator (A x) (rhs x) support j

/-- Moving cleared affine-equation atom. -/
def parametricSupportEquationResidual
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : ℝ → Matrix Row Col ℝ) (rhs : ℝ → Row → ℝ)
    (support : Finset Col) (i : Row) (x : ℝ) : ℝ :=
  supportEquationResidual (A x) (rhs x) support i

theorem analyticAt_parametricSupportGram_entry
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : ℝ → Matrix Row Col ℝ) (support : Finset Col)
    {x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun x => A x i j) x₀)
    (i j : support) :
    AnalyticAt ℝ (fun x => supportGram (A x) support i j) x₀ := by
  simp only [supportGram, supportColumnMatrix,
    Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, id_eq]
  fun_prop

theorem analyticAt_parametricSupportGramRhs
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : ℝ → Matrix Row Col ℝ) (rhs : ℝ → Row → ℝ)
    (support : Finset Col) {x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun x => A x i j) x₀)
    (hrhs : ∀ i, AnalyticAt ℝ (fun x => rhs x i) x₀)
    (j : support) :
    AnalyticAt ℝ
      (fun x => supportGramRhs (A x) (rhs x) support j) x₀ := by
  simp only [supportGramRhs, supportColumnMatrix,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.submatrix_apply, id_eq]
  fun_prop

theorem analyticAt_parametricSupportObjectiveNumerator
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : ℝ → Matrix Row Col ℝ) (rhs : ℝ → Row → ℝ)
    (objective : ℝ → Col → ℝ) (support : Finset Col)
    {x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun x => A x i j) x₀)
    (hrhs : ∀ i, AnalyticAt ℝ (fun x => rhs x i) x₀)
    (hobjective : ∀ j,
      AnalyticAt ℝ (fun x => objective x j) x₀) :
    AnalyticAt ℝ
      (parametricSupportObjectiveNumerator
        A rhs objective support) x₀ := by
  classical
  change
    AnalyticAt ℝ
      (fun x =>
        ∑ j : support,
          objective x j.1 *
            Matrix.cramer (supportGram (A x) support)
              (supportGramRhs (A x) (rhs x) support) j) x₀
  apply Finset.univ.analyticAt_fun_sum
  intro j _
  exact (hobjective j.1).mul
    (analyticAt_matrix_cramer_apply
      (fun x => supportGram (A x) support)
      (fun x => supportGramRhs (A x) (rhs x) support)
      (analyticAt_parametricSupportGram_entry
        A support hA)
      (analyticAt_parametricSupportGramRhs
        A rhs support hA hrhs) j)

theorem analyticAt_parametricSupportDeterminant
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : ℝ → Matrix Row Col ℝ) (support : Finset Col)
    {x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun x => A x i j) x₀) :
    AnalyticAt ℝ
      (parametricSupportDeterminant A support) x₀ := by
  exact analyticAt_matrix_det
    (fun x => supportGram (A x) support)
    (analyticAt_parametricSupportGram_entry A support hA)

theorem analyticAt_parametricSupportCoordinateNumerator
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : ℝ → Matrix Row Col ℝ) (rhs : ℝ → Row → ℝ)
    (support : Finset Col) (j : Col) {x₀ : ℝ}
    (hA : ∀ i k, AnalyticAt ℝ (fun x => A x i k) x₀)
    (hrhs : ∀ i, AnalyticAt ℝ (fun x => rhs x i) x₀) :
    AnalyticAt ℝ
      (parametricSupportCoordinateNumerator
        A rhs support j) x₀ := by
  change
    AnalyticAt ℝ
      (fun x =>
        if hj : j ∈ support then
          Matrix.cramer (supportGram (A x) support)
              (supportGramRhs (A x) (rhs x) support) ⟨j, hj⟩ *
            (supportGram (A x) support).det
        else 0) x₀
  by_cases hj : j ∈ support
  · simp only [dif_pos hj]
    exact
      (analyticAt_matrix_cramer_apply
        (fun x => supportGram (A x) support)
        (fun x => supportGramRhs (A x) (rhs x) support)
        (analyticAt_parametricSupportGram_entry A support hA)
        (analyticAt_parametricSupportGramRhs
          A rhs support hA hrhs) ⟨j, hj⟩).mul
        (analyticAt_parametricSupportDeterminant
          A support hA)
  · simp only [dif_neg hj]
    exact
        (analyticAt_const :
          AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) x₀)

theorem analyticAt_parametricSupportEquationResidual
    {Row Col : Type*}
    [Fintype Row] [DecidableEq Col]
    (A : ℝ → Matrix Row Col ℝ) (rhs : ℝ → Row → ℝ)
    (support : Finset Col) (i : Row) {x₀ : ℝ}
    (hA : ∀ k j, AnalyticAt ℝ (fun x => A x k j) x₀)
    (hrhs : ∀ k, AnalyticAt ℝ (fun x => rhs x k) x₀) :
    AnalyticAt ℝ
      (parametricSupportEquationResidual
        A rhs support i) x₀ := by
  classical
  change
    AnalyticAt ℝ
      (fun x =>
        (∑ j : support,
            A x i j.1 *
              Matrix.cramer (supportGram (A x) support)
                (supportGramRhs (A x) (rhs x) support) j) -
          rhs x i * (supportGram (A x) support).det) x₀
  apply AnalyticAt.sub
  · apply Finset.univ.analyticAt_fun_sum
    intro j _
    exact (hA i j.1).mul
      (analyticAt_matrix_cramer_apply
        (fun x => supportGram (A x) support)
        (fun x => supportGramRhs (A x) (rhs x) support)
        (analyticAt_parametricSupportGram_entry A support hA)
        (analyticAt_parametricSupportGramRhs
          A rhs support hA hrhs) j)
  · exact (hrhs i).mul
      (analyticAt_parametricSupportDeterminant
        A support hA)

/-- Full moving basic-support closure.  If an analytic target value is
attained by an extreme optimizer of each nearby standard-form problem, one
fixed support Cramer candidate is eventually feasible and attains that full
optimum.

Singular supports are harmless: their zero determinant germ is discarded by
the finite analytic constraint stabilization.  Supports of every cardinality
are included, so empty and degenerate basic solutions are covered. -/
theorem exists_fixed_eventual_optimal_supportCramer
    {Row Col : Type*}
    [Fintype Row] [Fintype Col] [DecidableEq Col]
    (A : ℝ → Matrix Row Col ℝ) (rhs : ℝ → Row → ℝ)
    (objective : ℝ → Col → ℝ) (target : ℝ → ℝ)
    {x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun x => A x i j) x₀)
    (hrhs : ∀ i, AnalyticAt ℝ (fun x => rhs x i) x₀)
    (hobjective : ∀ j,
      AnalyticAt ℝ (fun x => objective x j) x₀)
    (htarget : AnalyticAt ℝ target x₀)
    (hextreme :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        ∃ z : Col → ℝ,
          z ∈ (standardFeasibleSet (A x) (rhs x)).extremePoints ℝ ∧
          IsStandardOptimal (A x) (rhs x) (objective x) z ∧
          (∑ j, objective x j * z j) = target x) :
    ∃ support : Finset Col,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        supportCramerVector (A x) (rhs x) support ∈
            standardFeasibleSet (A x) (rhs x) ∧
          IsStandardOptimal (A x) (rhs x) (objective x)
            (supportCramerVector (A x) (rhs x) support) ∧
          (∑ j, objective x j *
              supportCramerVector (A x) (rhs x) support j) =
            target x := by
  let num : Finset Col → ℝ → ℝ :=
    fun support =>
      parametricSupportObjectiveNumerator
        A rhs objective support
  let den : Finset Col → ℝ → ℝ :=
    fun support => parametricSupportDeterminant A support
  let inequality : Finset Col → Col → ℝ → ℝ :=
    fun support j =>
      parametricSupportCoordinateNumerator
        A rhs support j
  let equality : Finset Col → Row → ℝ → ℝ :=
    fun support i =>
      parametricSupportEquationResidual
        A rhs support i
  have hnum : ∀ support, AnalyticAt ℝ (num support) x₀ :=
    fun support =>
      analyticAt_parametricSupportObjectiveNumerator
        A rhs objective support hA hrhs hobjective
  have hden : ∀ support, AnalyticAt ℝ (den support) x₀ :=
    fun support =>
      analyticAt_parametricSupportDeterminant A support hA
  have hinequality : ∀ support j,
      AnalyticAt ℝ (inequality support j) x₀ :=
    fun support j =>
      analyticAt_parametricSupportCoordinateNumerator
        A rhs support j hA hrhs
  have hequality : ∀ support i,
      AnalyticAt ℝ (equality support i) x₀ :=
    fun support i =>
      analyticAt_parametricSupportEquationResidual
        A rhs support i hA hrhs
  have hcover :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        ∃ support,
          (∀ j, 0 ≤ inequality support j x) ∧
          (∀ i, equality support i x = 0) ∧
          den support x ≠ 0 ∧
          num support x / den support x = target x := by
    filter_upwards [hextreme] with x hx
    obtain ⟨z, hzExtreme, hzOptimal, hzValue⟩ := hx
    obtain ⟨support, hdet, heq, hcandidateOptimal⟩ :=
      exists_supportCramerBasis_of_extreme_optimal
        (A x) (rhs x) (objective x) hzExtreme hzOptimal
    have hatoms :=
      (supportCramer_feasible_iff_atoms
        (A x) (rhs x) support hdet).mp
        hcandidateOptimal.1
    refine ⟨support, ?_, ?_, hdet, ?_⟩
    · simpa [inequality,
        parametricSupportCoordinateNumerator] using hatoms.1
    · simpa [equality,
        parametricSupportEquationResidual] using hatoms.2
    · calc
        num support x / den support x =
            ∑ j, objective x j *
              supportCramerVector (A x) (rhs x) support j := by
          exact supportObjectiveNumerator_div_det
            (A x) (rhs x) (objective x) support
        _ = ∑ j, objective x j * z j := by rw [heq]
        _ = target x := hzValue
  obtain ⟨support, hsupport⟩ :=
    exists_fixed_eventual_feasible_analytic_quotient_eq
      num den target inequality equality
      hnum hden htarget hinequality hequality hcover
  refine ⟨support, ?_⟩
  filter_upwards [hsupport, hextreme] with x hs hx
  obtain ⟨hineq, heqAtoms, hdet, hvalue⟩ := hs
  obtain ⟨z, _hzExtreme, hzOptimal, hzValue⟩ := hx
  have hcandidateFeasible :
      supportCramerVector (A x) (rhs x) support ∈
        standardFeasibleSet (A x) (rhs x) := by
    apply (supportCramer_feasible_iff_atoms
      (A x) (rhs x) support hdet).mpr
    constructor
    · simpa [inequality,
        parametricSupportCoordinateNumerator] using hineq
    · simpa [equality,
        parametricSupportEquationResidual] using heqAtoms
  have hcandidateValue :
      (∑ j, objective x j *
          supportCramerVector (A x) (rhs x) support j) =
        target x := by
    rw [← hvalue]
    exact (supportObjectiveNumerator_div_det
      (A x) (rhs x) (objective x) support).symm
  have hcandidateOptimal :
      IsStandardOptimal (A x) (rhs x) (objective x)
        (supportCramerVector (A x) (rhs x) support) := by
    constructor
    · exact hcandidateFeasible
    · intro w hw
      calc
        (∑ j, objective x j * w j) ≤
            ∑ j, objective x j * z j :=
          hzOptimal.2 w hw
        _ = target x := hzValue
        _ = ∑ j, objective x j *
            supportCramerVector (A x) (rhs x) support j :=
          hcandidateValue.symm
  exact ⟨hcandidateFeasible, hcandidateOptimal, hcandidateValue⟩

/-- Full moving basic-support closure from mere attained optimality.

The static extreme-optimizer theorem discharges the only convex-geometric
premise of `exists_fixed_eventual_optimal_supportCramer`: the caller need
only provide an attained optimum with the analytic target value at each
nearby parameter. -/
theorem exists_fixed_eventual_optimal_supportCramer_of_attained
    {Row Col : Type*}
    [Fintype Row] [Fintype Col] [DecidableEq Col]
    (A : ℝ → Matrix Row Col ℝ) (rhs : ℝ → Row → ℝ)
    (objective : ℝ → Col → ℝ) (target : ℝ → ℝ)
    {x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun x => A x i j) x₀)
    (hrhs : ∀ i, AnalyticAt ℝ (fun x => rhs x i) x₀)
    (hobjective : ∀ j,
      AnalyticAt ℝ (fun x => objective x j) x₀)
    (htarget : AnalyticAt ℝ target x₀)
    (hattained :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        ∃ z : Col → ℝ,
          IsStandardOptimal (A x) (rhs x) (objective x) z ∧
          (∑ j, objective x j * z j) = target x) :
    ∃ support : Finset Col,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        supportCramerVector (A x) (rhs x) support ∈
            standardFeasibleSet (A x) (rhs x) ∧
          IsStandardOptimal (A x) (rhs x) (objective x)
            (supportCramerVector (A x) (rhs x) support) ∧
          (∑ j, objective x j *
              supportCramerVector (A x) (rhs x) support j) =
            target x := by
  have hextreme :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        ∃ z : Col → ℝ,
          z ∈ (standardFeasibleSet (A x) (rhs x)).extremePoints ℝ ∧
          IsStandardOptimal (A x) (rhs x) (objective x) z ∧
          (∑ j, objective x j * z j) = target x := by
    filter_upwards [hattained] with x hx
    obtain ⟨z, hzOptimal, hzValue⟩ := hx
    obtain ⟨zExtreme, hzExtreme, hzExtremeOptimal, hsameValue⟩ :=
      exists_extreme_standardOptimal_of_standardOptimal
        (A x) (rhs x) (objective x) hzOptimal
    exact ⟨zExtreme, hzExtreme, hzExtremeOptimal,
      hsameValue.trans hzValue⟩
  exact exists_fixed_eventual_optimal_supportCramer
    A rhs objective target hA hrhs hobjective htarget hextreme

/-- Basic-support coverage specialized to a normalized Farkas polyhedron.
In particular, columns with zero mass are allowed in the selected basis. -/
theorem exists_supportCramerBasis_of_extreme_optimal_normalizedFarkas
    {Row Col : Type*}
    [Fintype Row] [Fintype Col] [DecidableEq Col]
    (balance : Matrix Row Col ℝ) (mass objective : Col → ℝ)
    {z : Col → ℝ}
    (hzExtreme :
      z ∈ (normalizedFarkasCertificateSet balance mass).extremePoints ℝ)
    (hzOptimal :
      IsStandardOptimal
        (normalizedFarkasMatrix balance mass)
        normalizedFarkasRhs objective z) :
    ∃ support : Finset Col,
      (supportGram
        (normalizedFarkasMatrix balance mass) support).det ≠ 0 ∧
      supportCramerVector
          (normalizedFarkasMatrix balance mass)
          normalizedFarkasRhs support = z ∧
      IsStandardOptimal
        (normalizedFarkasMatrix balance mass)
        normalizedFarkasRhs objective
        (supportCramerVector
          (normalizedFarkasMatrix balance mass)
          normalizedFarkasRhs support) := by
  exact exists_supportCramerBasis_of_extreme_optimal
    (normalizedFarkasMatrix balance mass)
    normalizedFarkasRhs objective hzExtreme hzOptimal

/-- Parametric normalized-Farkas closure.  Analytic balance, mass, and
objective data admit one fixed eventual support whenever the normalized
problem has an extreme optimizer with analytic optimal value at every
nearby positive parameter.

No hypothesis is imposed on the signs or zero set of `mass`: columns with
zero normalizing mass remain available to the fixed support.  A degenerate
basic solution is represented by its positive support, so zero basic
coordinates do not require a separate case. -/
theorem exists_fixed_eventual_optimal_normalizedFarkas_supportCramer
    {Row Col : Type*}
    [Fintype Row] [Fintype Col] [DecidableEq Col]
    (balance : ℝ → Matrix Row Col ℝ)
    (mass objective : ℝ → Col → ℝ)
    (target : ℝ → ℝ) {x₀ : ℝ}
    (hbalance :
      ∀ i j, AnalyticAt ℝ (fun x => balance x i j) x₀)
    (hmass :
      ∀ j, AnalyticAt ℝ (fun x => mass x j) x₀)
    (hobjective :
      ∀ j, AnalyticAt ℝ (fun x => objective x j) x₀)
    (htarget : AnalyticAt ℝ target x₀)
    (hextreme :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        ∃ z : Col → ℝ,
          z ∈
            (normalizedFarkasCertificateSet
              (balance x) (mass x)).extremePoints ℝ ∧
          IsStandardOptimal
              (normalizedFarkasMatrix (balance x) (mass x))
              normalizedFarkasRhs (objective x) z ∧
          (∑ j, objective x j * z j) = target x) :
    ∃ support : Finset Col,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        supportCramerVector
              (normalizedFarkasMatrix (balance x) (mass x))
              normalizedFarkasRhs support ∈
            normalizedFarkasCertificateSet
              (balance x) (mass x) ∧
          IsStandardOptimal
              (normalizedFarkasMatrix (balance x) (mass x))
              normalizedFarkasRhs (objective x)
              (supportCramerVector
                (normalizedFarkasMatrix (balance x) (mass x))
                normalizedFarkasRhs support) ∧
          (∑ j, objective x j *
              supportCramerVector
                (normalizedFarkasMatrix (balance x) (mass x))
                normalizedFarkasRhs support j) =
            target x := by
  let A : ℝ → Matrix (Sum Row Unit) Col ℝ :=
    fun x => normalizedFarkasMatrix (balance x) (mass x)
  let rhs : ℝ → Sum Row Unit → ℝ :=
    fun _ => normalizedFarkasRhs
  have hA :
      ∀ i j, AnalyticAt ℝ (fun x => A x i j) x₀ := by
    intro i j
    cases i with
    | inl i =>
        exact hbalance i j
    | inr _ =>
        exact hmass j
  have hrhs :
      ∀ i, AnalyticAt ℝ (fun x => rhs x i) x₀ := by
    intro i
    exact analyticAt_const
  have hextreme' :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        ∃ z : Col → ℝ,
          z ∈ (standardFeasibleSet (A x) (rhs x)).extremePoints ℝ ∧
          IsStandardOptimal (A x) (rhs x) (objective x) z ∧
          (∑ j, objective x j * z j) = target x := by
    simpa [A, rhs, normalizedFarkasCertificateSet] using hextreme
  simpa [A, rhs, normalizedFarkasCertificateSet] using
    (exists_fixed_eventual_optimal_supportCramer
      A rhs objective target hA hrhs hobjective htarget hextreme')

/-- Parametric normalized-Farkas closure from attained optimality.

This is the premise-minimal analytic optimizer bridge: attainment and an
analytic optimal value produce one fixed eventual Cramer support. -/
theorem
    exists_fixed_eventual_optimal_normalizedFarkas_supportCramer_of_attained
    {Row Col : Type*}
    [Fintype Row] [Fintype Col] [DecidableEq Col]
    (balance : ℝ → Matrix Row Col ℝ)
    (mass objective : ℝ → Col → ℝ)
    (target : ℝ → ℝ) {x₀ : ℝ}
    (hbalance :
      ∀ i j, AnalyticAt ℝ (fun x => balance x i j) x₀)
    (hmass :
      ∀ j, AnalyticAt ℝ (fun x => mass x j) x₀)
    (hobjective :
      ∀ j, AnalyticAt ℝ (fun x => objective x j) x₀)
    (htarget : AnalyticAt ℝ target x₀)
    (hattained :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        ∃ z : Col → ℝ,
          IsStandardOptimal
              (normalizedFarkasMatrix (balance x) (mass x))
              normalizedFarkasRhs (objective x) z ∧
          (∑ j, objective x j * z j) = target x) :
    ∃ support : Finset Col,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        supportCramerVector
              (normalizedFarkasMatrix (balance x) (mass x))
              normalizedFarkasRhs support ∈
            normalizedFarkasCertificateSet
              (balance x) (mass x) ∧
          IsStandardOptimal
              (normalizedFarkasMatrix (balance x) (mass x))
              normalizedFarkasRhs (objective x)
              (supportCramerVector
                (normalizedFarkasMatrix (balance x) (mass x))
                normalizedFarkasRhs support) ∧
          (∑ j, objective x j *
              supportCramerVector
                (normalizedFarkasMatrix (balance x) (mass x))
                normalizedFarkasRhs support j) =
            target x := by
  let A : ℝ → Matrix (Sum Row Unit) Col ℝ := fun x =>
    normalizedFarkasMatrix (balance x) (mass x)
  let rhs : ℝ → Sum Row Unit → ℝ := fun _ => normalizedFarkasRhs
  have hA :
      ∀ i j, AnalyticAt ℝ (fun x => A x i j) x₀ := by
    intro i j
    cases i with
    | inl i => exact hbalance i j
    | inr _ => exact hmass j
  have hrhs :
      ∀ i, AnalyticAt ℝ (fun x => rhs x i) x₀ := by
    intro i
    exact analyticAt_const
  have hattained' :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        ∃ z : Col → ℝ,
          IsStandardOptimal (A x) (rhs x) (objective x) z ∧
          (∑ j, objective x j * z j) = target x := by
    simpa [A, rhs] using hattained
  simpa [A, rhs, normalizedFarkasCertificateSet] using
    (exists_fixed_eventual_optimal_supportCramer_of_attained
      A rhs objective target hA hrhs hobjective htarget hattained')

end
end LinearAlgebra
end Math
