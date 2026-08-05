/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.RegularPolynomialCurveSelection
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Analytic implicit functions and regular polynomial arcs

Mathlib's public implicit-function API constructs a strictly differentiable
local chart.  Its lower-level analytic inverse theorem is already
multidimensional, however.  This file connects the two APIs: an analytic
`ImplicitFunctionData` has an analytic implicit function.

As a consequence, the regular-level curve-selection theorem needs no assumed
analytic chart.  Analyticity of the original level map, surjectivity of its
derivative, and a positively oriented kernel vector suffice.  A finite family
of strict polynomial signs is preserved by openness.
-/

noncomputable section

open Filter Set Topology

namespace Math

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The implicit function associated to analytic implicit-function data is
analytic.  This is the multidimensional analytic inverse theorem specialized
to mathlib's canonical implicit chart. -/
theorem analyticAt_implicitFunctionData
    (φ : ImplicitFunctionData ℝ E F G)
    (hleft : AnalyticAt ℝ φ.leftFun φ.pt)
    (hright : AnalyticAt ℝ φ.rightFun φ.pt) :
    AnalyticAt ℝ
      (φ.implicitFunction (φ.leftFun φ.pt))
      (φ.rightFun φ.pt) := by
  let i : E ≃L[ℝ] F × G :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl
      φ.rightDeriv φ.range_leftDeriv φ.range_rightDeriv
      φ.isCompl_ker
  have hprod : AnalyticAt ℝ φ.prodFun φ.pt := by
    change
      AnalyticAt ℝ
        (fun x => (φ.leftFun x, φ.rightFun x)) φ.pt
    exact hleft.prod hright
  obtain ⟨p, hp⟩ := hprod
  have hderiv :
      continuousMultilinearCurryFin1 ℝ E (F × G) (p 1) =
        (i : E →L[ℝ] F × G) := by
    exact hp.hasFDerivAt.unique φ.hasStrictFDerivAt.hasFDerivAt
  have hp_one :
      p 1 =
        (continuousMultilinearCurryFin1 ℝ E (F × G)).symm i := by
    apply (continuousMultilinearCurryFin1 ℝ E (F × G)).injective
    rw [hderiv]
    exact
      (continuousMultilinearCurryFin1 ℝ E (F × G)).apply_symm_apply i
  have hinverse :
      AnalyticAt ℝ
        φ.toOpenPartialHomeomorph.symm
        (φ.prodFun φ.pt) := by
    refine ⟨p.leftInv i φ.pt, ?_⟩
    simpa only [ImplicitFunctionData.toOpenPartialHomeomorph_coe] using
      φ.toOpenPartialHomeomorph.hasFPowerSeriesAt_symm
        φ.pt_mem_toOpenPartialHomeomorph_source hp hp_one
  have hslice :
      AnalyticAt ℝ
        (fun y : G => (φ.leftFun φ.pt, y))
        (φ.rightFun φ.pt) :=
    analyticAt_const.prod analyticAt_id
  have hcomposition :=
    hinverse.comp_of_eq hslice (by
      simp only [ImplicitFunctionData.prodFun_apply])
  have hfun :
      φ.toOpenPartialHomeomorph.symm ∘
          (fun y : G => (φ.leftFun φ.pt, y)) =
        φ.implicitFunction (φ.leftFun φ.pt) := by
    rfl
  rw [← hfun]
  exact hcomposition

variable [FiniteDimensional ℝ F]

/-- The canonical implicit chart of an analytic map to a finite-dimensional
space is analytic. -/
theorem analyticAt_implicitFunction
    {f : E → F} {f' : E →L[ℝ] F} {x₀ : E}
    (hf : HasStrictFDerivAt f f' x₀)
    (hf_analytic : AnalyticAt ℝ f x₀)
    (hsurj : f'.range = ⊤) :
    AnalyticAt ℝ
      (hf.implicitFunction f f' hsurj (f x₀)) 0 := by
  let hker : f'.ker.ClosedComplemented :=
    f'.ker_closedComplemented_of_finiteDimensional_range
  let φ : ImplicitFunctionData ℝ E F f'.ker :=
    hf.implicitFunctionDataOfComplemented f f' hsurj hker
  have hleft : AnalyticAt ℝ φ.leftFun φ.pt := by
    simpa only [φ,
      HasStrictFDerivAt.implicitFunctionDataOfComplemented] using
        hf_analytic
  have hright : AnalyticAt ℝ φ.rightFun φ.pt := by
    change
      AnalyticAt ℝ
        (fun x : E => Classical.choose hker (x - x₀)) x₀
    exact
      ((Classical.choose hker).analyticAt 0).comp_of_eq
        (analyticAt_id.sub analyticAt_const) (by simp)
  have hchart :=
    analyticAt_implicitFunctionData φ hleft hright
  simpa only [φ,
    HasStrictFDerivAt.implicitFunctionDataOfComplemented,
    ImplicitFunctionData.implicitFunction,
    HasStrictFDerivAt.implicitFunction,
    HasStrictFDerivAt.implicitToOpenPartialHomeomorph,
    HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented,
    sub_self, map_zero] using hchart

/-- Analytic regular-level curve selection, with no chart hypothesis.

The set `U` packages any strict sign conditions valid at the base point. -/
theorem hasPositiveCoordinateAnalyticArcAt_regularLevel_of_analytic
    {f : E → F} {f' : E →L[ℝ] F} {x₀ : E}
    {coordinate : E →L[ℝ] ℝ} {U : Set E}
    (hf : HasStrictFDerivAt f f' x₀)
    (hf_analytic : AnalyticAt ℝ f x₀)
    (hsurj : f'.range = ⊤)
    (d : f'.ker)
    (hcoordinate_d : 0 < coordinate d.1)
    (hcoordinate_x₀ : coordinate x₀ = 0)
    (hU : U ∈ 𝓝 x₀) :
    HasPositiveCoordinateAnalyticArcAt
      ({x | f x = f x₀} ∩ U) coordinate x₀ := by
  apply hasPositiveCoordinateAnalyticArcAt_regularLevel
    hf hsurj (analyticAt_implicitFunction hf hf_analytic hsurj)
    d hcoordinate_d hcoordinate_x₀ hU

/-- Regular-locus curve selection inside a finite strict polynomial sign
cell, again without an assumed analytic chart. -/
theorem hasPositiveCoordinateAnalyticArcAt_strictPolynomialCell_of_analytic
    {ι σ : Type*} [Finite ι] [Fintype σ]
    {f : PolynomialSignCell.Assignment σ → F}
    {f' : PolynomialSignCell.Assignment σ →L[ℝ] F}
    {x₀ : PolynomialSignCell.Assignment σ}
    {coordinate :
      PolynomialSignCell.Assignment σ →L[ℝ] ℝ}
    (P : ι → MvPolynomial σ ℝ)
    (τ : PolynomialSignCell.SignPattern ι)
    (hτ : ∀ i, τ i ≠ 0)
    (hx₀ : x₀ ∈ PolynomialSignCell.signCell P τ)
    (hf : HasStrictFDerivAt f f' x₀)
    (hf_analytic : AnalyticAt ℝ f x₀)
    (hsurj : f'.range = ⊤)
    (d : f'.ker)
    (hcoordinate_d : 0 < coordinate d.1)
    (hcoordinate_x₀ : coordinate x₀ = 0) :
    HasPositiveCoordinateAnalyticArcAt
      ({x | f x = f x₀} ∩
        PolynomialSignCell.signCell P τ)
      coordinate x₀ := by
  apply hasPositiveCoordinateAnalyticArcAt_regularLevel_of_analytic
    hf hf_analytic hsurj d hcoordinate_d hcoordinate_x₀
  exact
    (PolynomialSignCell.isOpen_signCell_of_ne_zero P τ hτ).mem_nhds hx₀

end Math
