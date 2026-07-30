/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AlgebraicSelection
import Math.AnalyticCoordinateCurve
import Math.PolynomialSignCell
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Data.Sign.Defs

/-!
# Univariate polynomial curve selection

This file proves the dimension-one base case of sign-compatible analytic
curve selection.  A finite family of real polynomials has one fixed sign
pattern on a sufficiently small positive interval.  If a prescribed sign
cell accumulates at zero from the right, it must be that eventual cell, so
the identity arc selects it with exact power coordinate `t`.

Higher-dimensional singular curve selection additionally needs elimination
and convergent Newton--Puiseux; none of that is assumed here.
-/

noncomputable section

open Filter Set SignType Topology

namespace Math

/-- The exact sign cell of a finite family of ordinary real polynomials. -/
def univariateSignCell
    {I : Type*} (p : I → Polynomial ℝ) (τ : I → SignType) :
    Set ℝ :=
  {x | ∀ i, SignType.sign ((p i).eval x) = τ i}

@[simp]
theorem mem_univariateSignCell
    {I : Type*} (p : I → Polynomial ℝ) (τ : I → SignType)
    (x : ℝ) :
    x ∈ univariateSignCell p τ ↔
      ∀ i, SignType.sign ((p i).eval x) = τ i :=
  Iff.rfl

/-- Every real polynomial has one constant sign on a sufficiently small
positive interval at zero. -/
theorem polynomial_eval_eventually_constant_sign
    (p : Polynomial ℝ) :
    ∃ s : SignType,
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        SignType.sign (p.eval x) = s := by
  have hp : AnalyticAt ℝ (fun x : ℝ => p.eval x) 0 :=
    (AnalyticOnNhd.eval_polynomial p) 0 (Set.mem_univ 0)
  rcases analyticAt_eventually_eq_or_lt_or_gt hp analyticAt_const with
    hzero | hneg | hpos
  · refine ⟨0, ?_⟩
    filter_upwards [hzero] with x hx
    rw [hx, sign_zero]
  · refine ⟨-1, ?_⟩
    filter_upwards [hneg] with x hx
    exact sign_eq_neg_one_iff.mpr hx
  · refine ⟨1, ?_⟩
    filter_upwards [hpos] with x hx
    exact sign_eq_one_iff.mpr hx

/-- A finite polynomial family has one simultaneous sign pattern on a
sufficiently small positive interval. -/
theorem finite_polynomial_family_eventually_constant_sign
    {I : Type*} [Finite I] (p : I → Polynomial ℝ) :
    ∃ τ : I → SignType,
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        x ∈ univariateSignCell p τ := by
  choose τ hτ using fun i => polynomial_eval_eventually_constant_sign (p i)
  refine ⟨τ, Filter.eventually_all.mpr fun i => ?_⟩
  exact hτ i

/-- A univariate sign cell accumulating at zero from the right contains an
entire sufficiently small positive interval. -/
theorem eventually_mem_univariateSignCell_of_mem_closure_right
    {I : Type*} [Finite I] {p : I → Polynomial ℝ}
    {τ : I → SignType}
    (hclosure :
      0 ∈ closure (univariateSignCell p τ ∩ Set.Ioi 0)) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ),
      x ∈ univariateSignCell p τ := by
  obtain ⟨υ, hυ⟩ :=
    finite_polynomial_family_eventually_constant_sign p
  have hfrequent :
      ∃ᶠ x in 𝓝[>] (0 : ℝ),
        x ∈ univariateSignCell p τ := by
    rw [frequently_nhdsWithin_iff]
    simpa [and_assoc, and_left_comm, and_comm] using
      (mem_closure_iff_frequently.mp hclosure)
  obtain ⟨x, hxτ, hxυ⟩ := (hfrequent.and_eventually hυ).exists
  have hτυ : τ = υ := by
    funext i
    exact (hxτ i).symm.trans (hxυ i)
  rwa [← hτυ] at hυ

/-- Dimension-one sign-compatible analytic curve selection.  The selected
arc is the identity, so its distinguished coordinate is exactly `t ^ 1`. -/
theorem hasAnalyticPowerCurveAt_univariateSignCell
    {I : Type*} [Finite I] {p : I → Polynomial ℝ}
    {τ : I → SignType}
    (hclosure :
      0 ∈ closure (univariateSignCell p τ ∩ Set.Ioi 0)) :
    HasAnalyticPowerCurveAt
      (univariateSignCell p τ)
      (ContinuousLinearMap.id ℝ ℝ) 0 := by
  have hmem :=
    eventually_mem_univariateSignCell_of_mem_closure_right hclosure
  obtain ⟨eta, heta, hinterval⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hmem
  refine ⟨1, id, eta, by positivity, heta, analyticAt_id, rfl, ?_⟩
  intro t ht
  exact ⟨hinterval ht, by simp⟩

/-- A polynomial coordinate curve in a finite-dimensional assignment
space. -/
def polynomialCoordinateCurve
    {σ : Type*} (coordinate : σ → Polynomial ℝ) :
    ℝ → (σ → ℝ) :=
  fun t i => (coordinate i).eval t

/-- Pull a multivariate polynomial back along a polynomial coordinate
curve. -/
def polynomialCurvePullback
    {σ : Type*} (coordinate : σ → Polynomial ℝ)
    (p : MvPolynomial σ ℝ) :
    Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C coordinate p

@[simp]
theorem eval_polynomialCurvePullback
    {σ : Type*} (coordinate : σ → Polynomial ℝ)
    (p : MvPolynomial σ ℝ) (t : ℝ) :
    (polynomialCurvePullback coordinate p).eval t =
      MvPolynomial.eval (polynomialCoordinateCurve coordinate t) p := by
  change
    Polynomial.evalRingHom t
        (MvPolynomial.eval₂Hom Polynomial.C coordinate p) =
      MvPolynomial.eval₂Hom (RingHom.id ℝ)
        (polynomialCoordinateCurve coordinate t) p
  rw [MvPolynomial.map_eval₂Hom]
  have hconst :
      (Polynomial.evalRingHom t).comp Polynomial.C =
        RingHom.id ℝ := by
    ext x
    simp
  have hcoordinate :
      (fun i => Polynomial.evalRingHom t (coordinate i)) =
        polynomialCoordinateCurve coordinate t := rfl
  exact MvPolynomial.eval₂Hom_congr hconst hcoordinate rfl

/-- Pullback identifies a multivariate sign cell along a polynomial curve
with an ordinary univariate sign cell. -/
theorem preimage_signCell_polynomialCoordinateCurve
    {I σ : Type*} (P : I → MvPolynomial σ ℝ)
    (τ : I → SignType) (coordinate : σ → Polynomial ℝ) :
    polynomialCoordinateCurve coordinate ⁻¹'
        PolynomialSignCell.signCell P τ =
      univariateSignCell
        (fun i => polynomialCurvePullback coordinate (P i)) τ := by
  ext t
  simp only [Set.mem_preimage, PolynomialSignCell.mem_signCell,
    mem_univariateSignCell]
  constructor
  · intro h i
    have hi := congrFun h i
    change
      SignType.sign
          (MvPolynomial.eval
            (polynomialCoordinateCurve coordinate t) (P i)) =
        τ i at hi
    rw [eval_polynomialCurvePullback]
    exact hi
  · intro h
    funext i
    change
      SignType.sign
          (MvPolynomial.eval
            (polynomialCoordinateCurve coordinate t) (P i)) =
        τ i
    rw [← eval_polynomialCurvePullback]
    exact h i

/-- Any polynomial arc which approaches a prescribed multivariate sign cell
and has one exact power coordinate supplies a checked analytic power curve
in that cell.

This is a finite certificate for line, monomial, and polynomially
parameterized singular branches. -/
theorem hasAnalyticPowerCurveAt_signCell_of_polynomialCoordinateCurve
    {I σ : Type*} [Finite I] [Fintype σ]
    {P : I → MvPolynomial σ ℝ} {τ : I → SignType}
    {coordinate : σ → Polynomial ℝ} {parameter : σ}
    {q : ℕ} (hq : 0 < q)
    (hparameter : coordinate parameter = Polynomial.X ^ q)
    (hclosure :
      0 ∈ closure
        ((polynomialCoordinateCurve coordinate) ⁻¹'
          PolynomialSignCell.signCell P τ ∩ Set.Ioi 0)) :
    HasAnalyticPowerCurveAt
      (PolynomialSignCell.signCell P τ)
      (ContinuousLinearMap.proj parameter)
      (polynomialCoordinateCurve coordinate 0) := by
  rw [preimage_signCell_polynomialCoordinateCurve] at hclosure
  have hmem :=
    eventually_mem_univariateSignCell_of_mem_closure_right hclosure
  obtain ⟨eta, heta, hinterval⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hmem
  have hcurve :
      AnalyticAt ℝ (polynomialCoordinateCurve coordinate) 0 := by
    rw [analyticAt_pi_iff]
    intro i
    exact (AnalyticOnNhd.eval_polynomial (coordinate i))
      0 (Set.mem_univ 0)
  refine ⟨q, polynomialCoordinateCurve coordinate, eta, hq, heta,
    hcurve, rfl, ?_⟩
  intro t ht
  refine ⟨?_, ?_⟩
  · have hpre :
        t ∈ polynomialCoordinateCurve coordinate ⁻¹'
          PolynomialSignCell.signCell P τ := by
      rw [preimage_signCell_polynomialCoordinateCurve]
      exact hinterval ht
    exact hpre
  · simp [polynomialCoordinateCurve, hparameter]

end Math
