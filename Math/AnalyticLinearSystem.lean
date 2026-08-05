/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.NormalizedFarkasBasis

/-!
# Analytic selectors for finite linear systems

An eventually solvable finite analytic linear system need not admit a
bounded analytic solution at the endpoint. This file supplies the exact
replacement: after multiplying by one common power of the parameter, a
solution can be selected analytically.

The proof homogenizes `A x = b` by adjoining a scale coordinate, doubles
all signed coordinates into positive and negative orientations, and then
uses the fixed-support Cramer selector for normalized Farkas systems.
-/

open Filter Finset Set

namespace Math
namespace LinearAlgebra

noncomputable section

/-- Homogenize `A x = b` as `[A | -b] (x, τ) = 0`. -/
def linearSolutionBalance
    {Row Col : Type*}
    (A : Matrix Row Col ℝ) (b : Row → ℝ) :
    Matrix Row (Sum Col Unit) ℝ
  | i, Sum.inl j => A i j
  | i, Sum.inr _ => -b i

/-- The normalizing functional selecting the homogenizing coordinate. -/
def linearSolutionMass
    {Col : Type*} : Sum Col Unit → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- Evaluation of the homogenized balance separates into its affine parts. -/
theorem linearSolutionBalance_mulVec
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col ℝ) (b : Row → ℝ)
    (y : Sum Col Unit → ℝ) (i : Row) :
    Matrix.mulVec (linearSolutionBalance A b) y i =
      Matrix.mulVec A (fun j => y (Sum.inl j)) i -
        b i * y (Sum.inr PUnit.unit) := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sum_type]
  simp [linearSolutionBalance]
  ring

/-- The homogenizing mass is exactly the last coordinate. -/
theorem linearSolutionMass_dotProduct
    {Col : Type*} [Fintype Col]
    (y : Sum Col Unit → ℝ) :
    (∑ j, linearSolutionMass j * y j) =
      y (Sum.inr PUnit.unit) := by
  classical
  rw [Fintype.sum_sum_type]
  simp [linearSolutionMass]

/-- Embed an affine solution with homogenizing coordinate one. -/
def homogenizedLinearSolution
    {Col : Type*} (x : Col → ℝ) :
    Sum Col Unit → ℝ
  | Sum.inl j => x j
  | Sum.inr _ => 1

/-- A solution of `A x = b` gives a signed normalized homogeneous solution. -/
theorem homogenizedLinearSolution_properties
    {Row Col : Type*} [Fintype Col]
    (A : Matrix Row Col ℝ) (b : Row → ℝ)
    (x : Col → ℝ) (hx : Matrix.mulVec A x = b) :
    Matrix.mulVec
          (linearSolutionBalance A b)
          (homogenizedLinearSolution x) = 0 ∧
      (∑ j,
          linearSolutionMass j *
            homogenizedLinearSolution x j) = 1 := by
  constructor
  · funext i
    rw [linearSolutionBalance_mulVec]
    simp only [homogenizedLinearSolution, mul_one]
    exact sub_eq_zero.mpr (congrFun hx i)
  · rw [linearSolutionMass_dotProduct]
    rfl

/-- Eventual solvability of a finite analytic linear system admits an
analytic solution after clearing one common endpoint pole.

The returned vector solves the scaled equation
`A(t) x(t) = (t - t₀)^p b(t)` on a punctured right neighborhood. If its
analytic order is at least `p`, the common power can be divided out and one
gets a bounded analytic solution of the original system. Otherwise its
first nonzero coefficient is a nontrivial vector in `ker A(t₀)`. -/
theorem exists_analytic_scaled_eventual_linearSolution
    {Row Col : Type*}
    [Finite Row] [Fintype Col]
    (A : ℝ → Matrix Row Col ℝ)
    (b : ℝ → Row → ℝ) {x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) x₀)
    (hb : ∀ i, AnalyticAt ℝ (fun t => b t i) x₀)
    (hfeasible :
      ∀ᶠ t in nhdsWithin x₀ (Ioi x₀),
        ∃ x : Col → ℝ, Matrix.mulVec (A t) x = b t) :
    ∃ (poleOrder : ℕ) (scaledSolution : ℝ → Col → ℝ),
      AnalyticAt ℝ scaledSolution x₀ ∧
        ∀ᶠ t in nhdsWithin x₀ (Ioi x₀),
          Matrix.mulVec (A t) (scaledSolution t) =
            (t - x₀) ^ poleOrder • b t := by
  classical
  letI := Fintype.ofFinite Row
  let balance : ℝ → Matrix Row (Sum Col Unit) ℝ := fun t =>
    linearSolutionBalance (A t) (b t)
  let mass : ℝ → Sum Col Unit → ℝ := fun _ =>
    linearSolutionMass
  have hbalance :
      ∀ i j, AnalyticAt ℝ (fun t => balance t i j) x₀ := by
    intro i j
    cases j with
    | inl j =>
        exact hA i j
    | inr _ =>
        change AnalyticAt ℝ (fun t => -b t i) x₀
        convert (hb i).neg using 1
        funext t
        rfl
  have hmass :
      ∀ j, AnalyticAt ℝ (fun t => mass t j) x₀ := by
    intro j
    exact analyticAt_const
  have horientedBalance :
      ∀ i j,
        AnalyticAt ℝ
          (fun t => orientedFarkasBalance (balance t) i j) x₀ := by
    rintro i ⟨j, positive⟩
    exact analyticAt_const.mul (hbalance i j)
  have horientedMass :
      ∀ j,
        AnalyticAt ℝ
          (fun t => orientedFarkasMass (mass t) j) x₀ := by
    rintro ⟨j, positive⟩
    simpa only [orientedFarkasMass, mass] using
      (analyticAt_const :
        AnalyticAt ℝ
          (fun _ : ℝ =>
            farkasOrientation positive * linearSolutionMass j) x₀)
  have horientedFeasible :
      ∀ᶠ t in nhdsWithin x₀ (Ioi x₀),
        (normalizedFarkasCertificateSet
          (orientedFarkasBalance (balance t))
          (orientedFarkasMass (mass t))).Nonempty := by
    filter_upwards [hfeasible] with t ht
    obtain ⟨x, hx⟩ := ht
    let y : Sum Col Unit → ℝ := homogenizedLinearSolution x
    have hy :=
      homogenizedLinearSolution_properties (A t) (b t) x hx
    exact
      ⟨signedFarkasToOriented y,
        signedFarkasToOriented_mem_normalizedFarkasCertificateSet
          (balance t) (mass t) y
          (by simpa only [balance] using hy.1)
          (by simpa only [mass] using hy.2)⟩
  obtain ⟨support, poleOrder, scaled, hscaled, hcertificate⟩ :=
    exists_analytic_scaled_eventual_feasible_normalizedFarkasCertificate
      (fun t => orientedFarkasBalance (balance t))
      (fun t => orientedFarkasMass (mass t))
      horientedBalance horientedMass horientedFeasible
  let signed : ℝ → Sum Col Unit → ℝ := fun t =>
    orientedFarkasToSigned (scaled t)
  let scaledSolution : ℝ → Col → ℝ := fun t j =>
    signed t (Sum.inl j)
  have hsolution : AnalyticAt ℝ scaledSolution x₀ := by
    rw [analyticAt_pi_iff]
    intro j
    exact
      ((analyticAt_pi_iff.mp hscaled (Sum.inl j, true)).sub
        (analyticAt_pi_iff.mp hscaled (Sum.inl j, false)))
  refine ⟨poleOrder, scaledSolution, hsolution, ?_⟩
  filter_upwards [hcertificate] with t ht
  let z :=
    supportCramerVector
      (normalizedFarkasMatrix
        (orientedFarkasBalance (balance t))
        (orientedFarkasMass (mass t)))
      normalizedFarkasRhs support
  have hz :
      Matrix.mulVec (balance t) (orientedFarkasToSigned z) = 0 ∧
        (∑ j,
            mass t j * orientedFarkasToSigned z j) = 1 :=
    normalizedFarkasCertificateSet_oriented_toSigned
      (balance t) (mass t) ht.2
  have hsigned_eq :
      signed t =
        (t - x₀) ^ poleOrder • orientedFarkasToSigned z := by
    funext j
    have hpositive := congrFun ht.1 (j, true)
    have hnegative := congrFun ht.1 (j, false)
    change
      scaled t (j, true) - scaled t (j, false) =
        (t - x₀) ^ poleOrder *
          (z (j, true) - z (j, false))
    change
      (t - x₀) ^ poleOrder * z (j, true) =
        scaled t (j, true) at hpositive
    change
      (t - x₀) ^ poleOrder * z (j, false) =
        scaled t (j, false) at hnegative
    rw [← hpositive, ← hnegative]
    ring
  have hsignedBalance :
      Matrix.mulVec (balance t) (signed t) = 0 := by
    rw [hsigned_eq, Matrix.mulVec_smul, hz.1, smul_zero]
  have hzScale :
      orientedFarkasToSigned z (Sum.inr PUnit.unit) = 1 := by
    simpa only [mass, linearSolutionMass_dotProduct] using hz.2
  have hsignedScale :
      signed t (Sum.inr PUnit.unit) = (t - x₀) ^ poleOrder := by
    rw [hsigned_eq]
    simp [hzScale]
  funext i
  have hi := congrFun hsignedBalance i
  rw [show balance t = linearSolutionBalance (A t) (b t) by rfl,
    linearSolutionBalance_mulVec] at hi
  change
    Matrix.mulVec (A t) (scaledSolution t) i =
      ((t - x₀) ^ poleOrder • b t) i
  change
    Matrix.mulVec (A t) (scaledSolution t) i -
        b t i * signed t (Sum.inr PUnit.unit) = 0 at hi
  rw [hsignedScale] at hi
  simpa [Pi.smul_apply, mul_comm] using sub_eq_zero.mp hi

/-- A pole-cleared analytic solution whose first nonzero term occurs below
the clearing power. Its leading coefficient is necessarily a nonzero
vector in the endpoint kernel. -/
structure AnalyticLinearKernelJet
    {Row Col : Type*} [Fintype Col]
    (A : ℝ → Matrix Row Col ℝ) (x₀ : ℝ)
    (poleOrder : ℕ) (scaledSolution : ℝ → Col → ℝ) where
  order : ℕ
  order_lt_poleOrder : order < poleOrder
  factor : ℝ → Col → ℝ
  analytic_factor : AnalyticAt ℝ factor x₀
  leading_ne_zero : factor x₀ ≠ 0
  scaledSolution_eq :
    ∀ᶠ t in nhds x₀,
      scaledSolution t = (t - x₀) ^ order • factor t
  endpoint_kernel :
    Matrix.mulVec (A x₀) (factor x₀) = 0

/-- A pole-cleared analytic solution either divides by the whole clearing
power, giving a bounded analytic solution of the original system, or has a
nonzero lower-order leading coefficient in the endpoint kernel. -/
theorem analytic_scaled_linearSolution_factor_or_kernelJet
    {Row Col : Type*}
    [Finite Row] [Fintype Col]
    (A : ℝ → Matrix Row Col ℝ)
    (b : ℝ → Row → ℝ) {x₀ : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) x₀)
    (hb : ∀ i, AnalyticAt ℝ (fun t => b t i) x₀)
    (poleOrder : ℕ) (scaledSolution : ℝ → Col → ℝ)
    (hscaled : AnalyticAt ℝ scaledSolution x₀)
    (hequation :
      ∀ᶠ t in nhdsWithin x₀ (Ioi x₀),
        Matrix.mulVec (A t) (scaledSolution t) =
          (t - x₀) ^ poleOrder • b t) :
    (∃ factor : ℝ → Col → ℝ,
      AnalyticAt ℝ factor x₀ ∧
        (∀ᶠ t in nhds x₀,
          scaledSolution t =
            (t - x₀) ^ poleOrder • factor t) ∧
        ∀ᶠ t in nhdsWithin x₀ (Ioi x₀),
          Matrix.mulVec (A t) (factor t) = b t) ∨
      Nonempty
        (AnalyticLinearKernelJet
          A x₀ poleOrder scaledSolution) := by
  classical
  letI := Fintype.ofFinite Row
  by_cases horder :
      (poleOrder : ℕ∞) ≤ analyticOrderAt scaledSolution x₀
  · left
    obtain ⟨factor, hfactor, hscaled_eq⟩ :=
      (natCast_le_analyticOrderAt hscaled).mp horder
    refine ⟨factor, hfactor, hscaled_eq, ?_⟩
    filter_upwards [hequation,
      hscaled_eq.filter_mono inf_le_left,
      (self_mem_nhdsWithin :
        ∀ᶠ t in nhdsWithin x₀ (Ioi x₀), t ∈ Ioi x₀)] with
        t heq hfactorEq ht
    have htne : t - x₀ ≠ 0 := sub_ne_zero.mpr ht.ne'
    rw [hfactorEq, Matrix.mulVec_smul] at heq
    funext i
    have hi := congrFun heq i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    exact mul_left_cancel₀ (pow_ne_zero poleOrder htne) hi
  · right
    have hlt :
        analyticOrderAt scaledSolution x₀ <
          (poleOrder : ℕ∞) :=
      lt_of_not_ge horder
    have hneTop :
        analyticOrderAt scaledSolution x₀ ≠ ⊤ :=
      ne_top_of_lt hlt
    obtain ⟨factor, hfactor, hfactorZero, hscaled_eq⟩ :=
      hscaled.analyticOrderAt_ne_top.mp hneTop
    let order := analyticOrderNatAt scaledSolution x₀
    have horderCast :
        (order : ℕ∞) =
          analyticOrderAt scaledSolution x₀ :=
      Nat.cast_analyticOrderNatAt hneTop
    have horderLt : order < poleOrder := by
      exact_mod_cast horderCast.symm ▸ hlt
    have hresidualAnalytic :
        AnalyticAt ℝ
          (fun t => Matrix.mulVec (A t) (factor t)) x₀ := by
      rw [analyticAt_pi_iff]
      intro i
      change
        AnalyticAt ℝ
          (fun t => ∑ j, A t i j * factor t j) x₀
      apply Finset.univ.analyticAt_fun_sum
      intro j _
      exact (hA i j).mul
        (analyticAt_pi_iff.mp hfactor j)
    let residual : ℝ → Row → ℝ := fun t =>
      Matrix.mulVec (A t) (factor t)
    let remainder : ℝ → Row → ℝ := fun t =>
      (t - x₀) ^ (poleOrder - order) • b t
    have hremainderAnalytic :
        AnalyticAt ℝ remainder x₀ := by
      rw [analyticAt_pi_iff]
      intro i
      exact
        ((analyticAt_id.sub analyticAt_const).pow
          (poleOrder - order)).mul (hb i)
    have hresidual_eq :
        ∀ᶠ t in nhdsWithin x₀ (Ioi x₀),
          residual t = remainder t := by
      filter_upwards [hequation,
        hscaled_eq.filter_mono inf_le_left,
        (self_mem_nhdsWithin :
          ∀ᶠ t in nhdsWithin x₀ (Ioi x₀), t ∈ Ioi x₀)] with
          t heq hfactorEq ht
      have htne : t - x₀ ≠ 0 := sub_ne_zero.mpr ht.ne'
      have hfactorEq' :
          scaledSolution t =
            (t - x₀) ^ order • factor t := by
        simpa only [order] using hfactorEq
      rw [hfactorEq', Matrix.mulVec_smul] at heq
      have hpole :
          poleOrder = order + (poleOrder - order) := by
        omega
      funext i
      have hi := congrFun heq i
      simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
      rw [hpole, pow_add] at hi
      exact mul_left_cancel₀ (pow_ne_zero order htne)
        (by
          simpa only [residual, remainder, Pi.smul_apply,
            smul_eq_mul, mul_assoc] using hi)
    have hremainderZero : remainder x₀ = 0 := by
      have hdiffNe : poleOrder - order ≠ 0 :=
        Nat.ne_of_gt (Nat.sub_pos_of_lt horderLt)
      funext i
      simp [remainder, hdiffNe]
    have hresidualZero : residual x₀ = 0 := by
      have hleft :
          Tendsto residual
            (nhdsWithin x₀ (Ioi x₀)) (nhds (residual x₀)) :=
        hresidualAnalytic.continuousAt.tendsto.mono_left
          inf_le_left
      have hright :
          Tendsto residual
            (nhdsWithin x₀ (Ioi x₀)) (nhds (remainder x₀)) :=
        (hremainderAnalytic.continuousAt.tendsto.mono_left
          inf_le_left).congr'
            (hresidual_eq.mono fun _ ht => ht.symm)
      have hendpointEq :
          residual x₀ = remainder x₀ :=
        tendsto_nhds_unique hleft hright
      exact hendpointEq.trans hremainderZero
    exact ⟨
      { order := order
        order_lt_poleOrder := horderLt
        factor := factor
        analytic_factor := hfactor
        leading_ne_zero := hfactorZero
        scaledSolution_eq := hscaled_eq
        endpoint_kernel := by
          simpa only [residual] using hresidualZero }⟩

end
end LinearAlgebra
end Math
