/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Coupling
import Math.ProbabilityMassFunction.TotalVariation

/-!
# Maximal Couplings of Finite PMFs

This file gives the explicit overlap/residual construction of a maximal
coupling.  Its mismatch probability is exactly the total-variation distance.
It also provides the disintegration lift used to turn a coupling of a
pushforward law into a coupling of the original law.
-/

set_option autoImplicit false

namespace Math
namespace Probability

open scoped BigOperators

variable {Ω S R : Type*}

section Maximal

variable [Fintype Ω]
noncomputable local instance : DecidableEq Ω := Classical.decEq Ω

private noncomputable def overlapReal (μ ν : PMF Ω) (ω : Ω) : ℝ :=
  min (μ ω).toReal (ν ω).toReal

private noncomputable def leftResidual (μ ν : PMF Ω) (ω : Ω) : ℝ :=
  (μ ω).toReal - overlapReal μ ν ω

private noncomputable def rightResidual (μ ν : PMF Ω) (ω : Ω) : ℝ :=
  (ν ω).toReal - overlapReal μ ν ω

omit [Fintype Ω] in
private theorem overlapReal_nonneg (μ ν : PMF Ω) (ω : Ω) :
    0 ≤ overlapReal μ ν ω :=
  le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg

omit [Fintype Ω] in
private theorem leftResidual_nonneg (μ ν : PMF Ω) (ω : Ω) :
    0 ≤ leftResidual μ ν ω :=
  sub_nonneg.mpr (min_le_left _ _)

omit [Fintype Ω] in
private theorem rightResidual_nonneg (μ ν : PMF Ω) (ω : Ω) :
    0 ≤ rightResidual μ ν ω :=
  sub_nonneg.mpr (min_le_right _ _)

private theorem leftResidual_sum (μ ν : PMF Ω) :
    ∑ ω, leftResidual μ ν ω = pmfTV μ ν := by
  unfold leftResidual overlapReal pmfTV pmfPositiveVariation
  apply Finset.sum_congr rfl
  intro ω _
  rcases le_total (μ ω).toReal (ν ω).toReal with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]

private theorem rightResidual_sum (μ ν : PMF Ω) :
    ∑ ω, rightResidual μ ν ω = pmfTV μ ν := by
  rw [pmfTV_symm μ ν]
  unfold rightResidual overlapReal pmfTV pmfPositiveVariation
  apply Finset.sum_congr rfl
  intro ω _
  rcases le_total (ν ω).toReal (μ ω).toReal with h | h
  · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]

private theorem overlapReal_sum_add_pmfTV (μ ν : PMF Ω) :
    (∑ ω, overlapReal μ ν ω) + pmfTV μ ν = 1 := by
  have h := leftResidual_sum μ ν
  unfold leftResidual at h
  rw [Finset.sum_sub_distrib, pmf_toReal_sum_one] at h
  linarith

omit [Fintype Ω] in
private theorem residual_mul_same (μ ν : PMF Ω) (ω : Ω) :
    leftResidual μ ν ω * rightResidual μ ν ω = 0 := by
  rcases le_total (μ ω).toReal (ν ω).toReal with h | h
  · simp [leftResidual, rightResidual, overlapReal, min_eq_left h]
  · simp [leftResidual, rightResidual, overlapReal, min_eq_right h]

private theorem sum_div_const (f : Ω → ℝ) (d : ℝ) :
    ∑ x, f x / d = (∑ x, f x) / d := by
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]

private theorem sum_sum_div_const (f : Ω → Ω → ℝ) (d : ℝ) :
    ∑ x, ∑ y, f x y / d = (∑ x, ∑ y, f x y) / d := by
  rw [show
      (∑ x, ∑ y, f x y / d) =
        ∑ x, (∑ y, f x y) / d by
      apply Finset.sum_congr rfl
      intro x _
      exact sum_div_const (f x) d]
  exact sum_div_const (fun x => ∑ y, f x y) d

private theorem residualProduct_sum (μ ν : PMF Ω) :
    ∑ x, ∑ y, leftResidual μ ν x * rightResidual μ ν y =
      pmfTV μ ν * pmfTV μ ν := by
  calc
    ∑ x, ∑ y, leftResidual μ ν x * rightResidual μ ν y =
        (∑ x, leftResidual μ ν x) *
          (∑ y, rightResidual μ ν y) :=
      (Fintype.sum_mul_sum (leftResidual μ ν) (rightResidual μ ν)).symm
    _ = pmfTV μ ν * pmfTV μ ν := by
      rw [leftResidual_sum, rightResidual_sum]

private noncomputable def maximalCouplingWeight
    (μ ν : PMF Ω) (p : Ω × Ω) : ℝ :=
  (if p.1 = p.2 then overlapReal μ ν p.1 else 0) +
    leftResidual μ ν p.1 * rightResidual μ ν p.2 / pmfTV μ ν

private theorem maximalCouplingWeight_nonneg (μ ν : PMF Ω) (p : Ω × Ω) :
    0 ≤ maximalCouplingWeight μ ν p := by
  apply add_nonneg
  · split_ifs
    · exact overlapReal_nonneg μ ν p.1
    · exact le_rfl
  · exact div_nonneg
      (mul_nonneg (leftResidual_nonneg μ ν p.1)
        (rightResidual_nonneg μ ν p.2))
      (pmfTV_nonneg μ ν)

private theorem maximalCouplingWeight_sum (μ ν : PMF Ω) :
    ∑ p : Ω × Ω, maximalCouplingWeight μ ν p = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [maximalCouplingWeight, Finset.sum_add_distrib]
  have hdiag :
      ∑ x : Ω, ∑ y : Ω, (if x = y then overlapReal μ ν x else 0) =
        ∑ x : Ω, overlapReal μ ν x := by
    apply Finset.sum_congr rfl
    intro x _
    simp
  have hres :
      ∑ x : Ω, ∑ y : Ω,
          leftResidual μ ν x * rightResidual μ ν y / pmfTV μ ν =
        pmfTV μ ν * pmfTV μ ν / pmfTV μ ν := by
    rw [sum_sum_div_const, residualProduct_sum]
  rw [hdiag, hres]
  by_cases htv : pmfTV μ ν = 0
  · rw [htv]
    norm_num
    simpa [htv] using overlapReal_sum_add_pmfTV μ ν
  · rw [mul_div_cancel_left₀ _ htv]
    exact overlapReal_sum_add_pmfTV μ ν

private noncomputable def maximalCouplingMass
    (μ ν : PMF Ω) (p : Ω × Ω) : ENNReal :=
  ENNReal.ofReal (maximalCouplingWeight μ ν p)

private theorem maximalCouplingMass_sum (μ ν : PMF Ω) :
    ∑ p : Ω × Ω, maximalCouplingMass μ ν p = 1 := by
  apply (ENNReal.toReal_eq_one_iff _).mp
  rw [ENNReal.toReal_sum]
  · simp_rw [maximalCouplingMass,
      ENNReal.toReal_ofReal (maximalCouplingWeight_nonneg μ ν _)]
    exact maximalCouplingWeight_sum μ ν
  · intro p _
    exact ENNReal.ofReal_ne_top

/-- The overlap/residual maximal coupling of two PMFs on a finite type. -/
noncomputable def maximalCoupling (μ ν : PMF Ω) : PMF (Ω × Ω) :=
  PMF.ofFintype (maximalCouplingMass μ ν) (maximalCouplingMass_sum μ ν)

private theorem leftResidual_eq_zero_of_pmfTV_eq_zero
    (μ ν : PMF Ω) (htv : pmfTV μ ν = 0) (ω : Ω) :
    leftResidual μ ν ω = 0 := by
  have hsum : ∑ x, leftResidual μ ν x = 0 := by
    rw [leftResidual_sum, htv]
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => leftResidual_nonneg μ ν x)).mp hsum ω (Finset.mem_univ ω)

private theorem rightResidual_eq_zero_of_pmfTV_eq_zero
    (μ ν : PMF Ω) (htv : pmfTV μ ν = 0) (ω : Ω) :
    rightResidual μ ν ω = 0 := by
  have hsum : ∑ x, rightResidual μ ν x = 0 := by
    rw [rightResidual_sum, htv]
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => rightResidual_nonneg μ ν x)).mp hsum ω (Finset.mem_univ ω)

private theorem maximalCouplingWeight_row (μ ν : PMF Ω) (x : Ω) :
    ∑ y, maximalCouplingWeight μ ν (x, y) = (μ x).toReal := by
  classical
  simp only [maximalCouplingWeight, Finset.sum_add_distrib]
  rw [sum_div_const]
  have hres :
      ∑ y : Ω, leftResidual μ ν x * rightResidual μ ν y =
        leftResidual μ ν x * pmfTV μ ν := by
    calc
      ∑ y : Ω, leftResidual μ ν x * rightResidual μ ν y =
          leftResidual μ ν x * ∑ y : Ω, rightResidual μ ν y :=
        (Finset.mul_sum Finset.univ (rightResidual μ ν)
          (leftResidual μ ν x)).symm
      _ = leftResidual μ ν x * pmfTV μ ν := by
        rw [rightResidual_sum]
  rw [hres]
  have hdiag :
      ∑ y : Ω, (if x = y then overlapReal μ ν x else 0) =
        overlapReal μ ν x := by
    simp
  rw [hdiag]
  by_cases htv : pmfTV μ ν = 0
  · have hx := leftResidual_eq_zero_of_pmfTV_eq_zero μ ν htv x
    rw [htv, hx]
    simp
    unfold leftResidual at hx
    linarith
  · rw [mul_div_cancel_right₀ _ htv]
    unfold leftResidual
    ring

private theorem maximalCouplingWeight_col (μ ν : PMF Ω) (y : Ω) :
    ∑ x, maximalCouplingWeight μ ν (x, y) = (ν y).toReal := by
  classical
  simp only [maximalCouplingWeight, Finset.sum_add_distrib]
  rw [sum_div_const]
  have hres :
      ∑ x : Ω, leftResidual μ ν x * rightResidual μ ν y =
        pmfTV μ ν * rightResidual μ ν y := by
    calc
      ∑ x : Ω, leftResidual μ ν x * rightResidual μ ν y =
          (∑ x : Ω, leftResidual μ ν x) * rightResidual μ ν y :=
        (Finset.sum_mul Finset.univ (leftResidual μ ν)
          (rightResidual μ ν y)).symm
      _ = pmfTV μ ν * rightResidual μ ν y := by
        rw [leftResidual_sum]
  rw [hres]
  have hdiag :
      ∑ x : Ω, (if x = y then overlapReal μ ν x else 0) =
        overlapReal μ ν y := by
    simp
  rw [hdiag]
  by_cases htv : pmfTV μ ν = 0
  · have hy := rightResidual_eq_zero_of_pmfTV_eq_zero μ ν htv y
    rw [htv, hy]
    simp
    unfold rightResidual at hy
    linarith
  · rw [mul_div_cancel_left₀ _ htv]
    unfold rightResidual
    ring

private theorem maximalCouplingMass_row (μ ν : PMF Ω) (x : Ω) :
    ∑ y, maximalCouplingMass μ ν (x, y) = μ x := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.sum_ne_top.mpr fun y _ => ENNReal.ofReal_ne_top)
    (PMF.apply_ne_top μ x)).mp
  rw [ENNReal.toReal_sum]
  · calc
      ∑ y, (maximalCouplingMass μ ν (x, y)).toReal =
          ∑ y, maximalCouplingWeight μ ν (x, y) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [maximalCouplingMass,
          ENNReal.toReal_ofReal (maximalCouplingWeight_nonneg μ ν (x, y))]
      _ = (μ x).toReal := maximalCouplingWeight_row μ ν x
  · intro y _
    exact ENNReal.ofReal_ne_top

private theorem maximalCouplingMass_col (μ ν : PMF Ω) (y : Ω) :
    ∑ x, maximalCouplingMass μ ν (x, y) = ν y := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.sum_ne_top.mpr fun x _ => ENNReal.ofReal_ne_top)
    (PMF.apply_ne_top ν y)).mp
  rw [ENNReal.toReal_sum]
  · calc
      ∑ x, (maximalCouplingMass μ ν (x, y)).toReal =
          ∑ x, maximalCouplingWeight μ ν (x, y) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [maximalCouplingMass,
          ENNReal.toReal_ofReal (maximalCouplingWeight_nonneg μ ν (x, y))]
      _ = (ν y).toReal := maximalCouplingWeight_col μ ν y
  · intro x _
    exact ENNReal.ofReal_ne_top

theorem maximalCoupling_map_fst (μ ν : PMF Ω) :
    (maximalCoupling μ ν).map Prod.fst = μ := by
  classical
  ext x
  rw [PMF.map_apply, tsum_fintype]
  rw [Fintype.sum_prod_type]
  simp only [maximalCoupling, PMF.ofFintype_apply]
  simpa only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] using
    maximalCouplingMass_row μ ν x

theorem maximalCoupling_map_snd (μ ν : PMF Ω) :
    (maximalCoupling μ ν).map Prod.snd = ν := by
  classical
  ext y
  rw [PMF.map_apply, tsum_fintype]
  rw [Fintype.sum_prod_type]
  simp only [maximalCoupling, PMF.ofFintype_apply]
  simpa only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] using
    maximalCouplingMass_col μ ν y

/-- Real probability of the event that a pair-valued PMF has unequal
coordinates. -/
noncomputable def mismatchProbability (ξ : PMF (Ω × Ω)) : ℝ :=
  expect ξ fun p => if p.1 ≠ p.2 then 1 else 0

theorem maximalCoupling_mismatchProbability (μ ν : PMF Ω) :
    mismatchProbability (maximalCoupling μ ν) = pmfTV μ ν := by
  classical
  rw [mismatchProbability, expect_eq_sum]
  simp only [maximalCoupling, PMF.ofFintype_apply, maximalCouplingMass,
    ENNReal.toReal_ofReal (maximalCouplingWeight_nonneg μ ν _)]
  rw [Fintype.sum_prod_type]
  have hpoint (x y : Ω) :
      maximalCouplingWeight μ ν (x, y) *
          (if x ≠ y then 1 else 0) =
        leftResidual μ ν x * rightResidual μ ν y / pmfTV μ ν := by
    by_cases hxy : x = y
    · subst hxy
      simp [residual_mul_same]
    · unfold maximalCouplingWeight
      simp [hxy]
  simp_rw [hpoint]
  rw [sum_sum_div_const, residualProduct_sum]
  by_cases htv : pmfTV μ ν = 0
  · simp [htv]
  · exact mul_div_cancel_left₀ _ htv

/-- A maximal coupling packaged with its two marginal identities and exact
mismatch probability. -/
theorem exists_maximalCoupling (μ ν : PMF Ω) :
    ∃ ξ : PMF (Ω × Ω),
      ξ.map Prod.fst = μ ∧
      ξ.map Prod.snd = ν ∧
      mismatchProbability ξ = pmfTV μ ν :=
  ⟨maximalCoupling μ ν, maximalCoupling_map_fst μ ν,
    maximalCoupling_map_snd μ ν, maximalCoupling_mismatchProbability μ ν⟩

end Maximal

section FiberLift

variable [Finite S] [Finite R]
noncomputable local instance : DecidableEq R := Classical.decEq R

/-- Lift a joint law of `(π s, r)` to a joint law of `(s, r)` by
disintegrating `q` over the first coordinate. -/
noncomputable def fiberLift
    (q : PMF S) (π : S → R) (ξ : PMF (R × R)) : PMF (S × R) :=
  ξ.bind fun p =>
    (ProbabilityMassFunction.condOn q π p.1).map fun s => (s, p.2)

theorem fiberLift_map_fst
    (q : PMF S) (π : S → R) (ξ : PMF (R × R))
    (hfst : ξ.map Prod.fst = q.map π) :
    (fiberLift q π ξ).map Prod.fst = q := by
  rw [fiberLift, PMF.map_bind]
  have hkernel (p : R × R) :
      ((ProbabilityMassFunction.condOn q π p.1).map fun s => (s, p.2)).map
          Prod.fst =
        ProbabilityMassFunction.condOn q π p.1 := by
    rw [PMF.map_comp]
    change (ProbabilityMassFunction.condOn q π p.1).map id =
      ProbabilityMassFunction.condOn q π p.1
    exact PMF.map_id _
  conv_lhs =>
    enter [2, p]
    rw [hkernel p]
  calc
    ξ.bind (fun p => ProbabilityMassFunction.condOn q π p.1) =
        (ξ.map Prod.fst).bind
          (fun r => ProbabilityMassFunction.condOn q π r) := by
      rw [PMF.bind_map]
      rfl
    _ = (q.map π).bind
          (fun r => ProbabilityMassFunction.condOn q π r) := by
      rw [hfst]
    _ = q := by
      simpa [ProbabilityMassFunction.pushforward] using
        (ProbabilityMassFunction.bind_pushforward_condOn_pure q π).symm

omit [Finite S] [Finite R] in
theorem fiberLift_map_snd
    (q : PMF S) (π : S → R) (ξ : PMF (R × R)) (k : PMF R)
    (hsnd : ξ.map Prod.snd = k) :
    (fiberLift q π ξ).map Prod.snd = k := by
  rw [fiberLift, PMF.map_bind]
  have hkernel (p : R × R) :
      ((ProbabilityMassFunction.condOn q π p.1).map fun s => (s, p.2)).map
          Prod.snd =
        PMF.pure p.2 := by
    rw [PMF.map_comp]
    change
      (ProbabilityMassFunction.condOn q π p.1).map
          (Function.const S p.2) =
        PMF.pure p.2
    exact PMF.map_const _ _
  conv_lhs =>
    enter [2, p]
    rw [hkernel p]
  calc
    ξ.bind (fun p => PMF.pure p.2) = ξ.map Prod.snd := by
      exact PMF.bind_pure_comp Prod.snd ξ
    _ = k := hsnd

/-- Mismatch probability after comparing the second coordinate to a
projection of the first. -/
noncomputable def projectionMismatchProbability
    (π : S → R) (ζ : PMF (S × R)) : ℝ :=
  expect ζ fun p => if π p.1 ≠ p.2 then 1 else 0

/-- Disintegration preserves the mismatch event: conditionally on the first
coordinate `r` of `ξ`, the lifted state lies in the fiber `π ⁻¹' {r}`. -/
theorem projectionMismatchProbability_fiberLift
    (q : PMF S) (π : S → R) (ξ : PMF (R × R))
    (hfst : ξ.map Prod.fst = q.map π) :
    projectionMismatchProbability π (fiberLift q π ξ) =
      mismatchProbability ξ := by
  classical
  rw [projectionMismatchProbability, fiberLift, expect_bind]
  have hinner (p : R × R) (hp : p ∈ ξ.support) :
      expect
          ((ProbabilityMassFunction.condOn q π p.1).map fun s => (s, p.2))
          (fun z => if π z.1 ≠ z.2 then 1 else 0) =
        (if p.1 ≠ p.2 then 1 else 0) := by
    have hp₁ : p.1 ∈ (ξ.map Prod.fst).support := by
      rw [PMF.support_map]
      exact ⟨p, hp, rfl⟩
    have hp₁q : p.1 ∈ (q.map π).support := by
      rw [← hfst]
      exact hp₁
    have hp₁ne : q.map π p.1 ≠ 0 := by
      change q.map π p.1 ≠ 0 at hp₁q
      exact hp₁q
    rw [expect_map]
    calc
      expect (ProbabilityMassFunction.condOn q π p.1)
          (fun s => if π s ≠ p.2 then 1 else 0) =
          expect (ProbabilityMassFunction.condOn q π p.1)
            (fun _ => if p.1 ≠ p.2 then 1 else 0) := by
        apply ProbabilityMassFunction.expect_congr_on_support
        intro s hs
        rw [ProbabilityMassFunction.condOn_support_project
          q π p.1 hp₁ne hs]
      _ = (if p.1 ≠ p.2 then 1 else 0) := by
        rw [expect_const]
  calc
    expect ξ
        (fun p =>
          expect
            ((ProbabilityMassFunction.condOn q π p.1).map
              fun s => (s, p.2))
            (fun z => if π z.1 ≠ z.2 then 1 else 0)) =
        expect ξ (fun p => if p.1 ≠ p.2 then 1 else 0) := by
      apply ProbabilityMassFunction.expect_congr_on_support
      exact hinner
    _ = mismatchProbability ξ := rfl

end FiberLift

section MaximalFiber

variable [Finite S] [Fintype R]
noncomputable local instance : DecidableEq R := Classical.decEq R

/-- Lift the canonical maximal coupling of `q.map π` and `k` back to `S × R`. -/
noncomputable def maximalFiberCoupling
    (q : PMF S) (π : S → R) (k : PMF R) : PMF (S × R) :=
  fiberLift q π (maximalCoupling (q.map π) k)

theorem maximalFiberCoupling_map_fst
    (q : PMF S) (π : S → R) (k : PMF R) :
    (maximalFiberCoupling q π k).map Prod.fst = q :=
  fiberLift_map_fst q π (maximalCoupling (q.map π) k)
    (maximalCoupling_map_fst (q.map π) k)

omit [Finite S] in
theorem maximalFiberCoupling_map_snd
    (q : PMF S) (π : S → R) (k : PMF R) :
    (maximalFiberCoupling q π k).map Prod.snd = k :=
  fiberLift_map_snd q π (maximalCoupling (q.map π) k)
    k (maximalCoupling_map_snd (q.map π) k)

theorem maximalFiberCoupling_mismatchProbability
    (q : PMF S) (π : S → R) (k : PMF R) :
    projectionMismatchProbability π (maximalFiberCoupling q π k) =
      pmfTV (q.map π) k := by
  rw [maximalFiberCoupling,
    projectionMismatchProbability_fiberLift q π
      (maximalCoupling (q.map π) k)
      (maximalCoupling_map_fst (q.map π) k),
    maximalCoupling_mismatchProbability]

/-- Existence form of the projected maximal-coupling construction. -/
theorem exists_maximalFiberCoupling
    (q : PMF S) (π : S → R) (k : PMF R) :
    ∃ ζ : PMF (S × R),
      ζ.map Prod.fst = q ∧
      ζ.map Prod.snd = k ∧
      projectionMismatchProbability π ζ = pmfTV (q.map π) k :=
  ⟨maximalFiberCoupling q π k, maximalFiberCoupling_map_fst q π k,
    maximalFiberCoupling_map_snd q π k,
    maximalFiberCoupling_mismatchProbability q π k⟩

end MaximalFiber

end Probability
end Math
