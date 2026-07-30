/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AnalyticCoordinateCurve
import Math.PolynomialSignCell
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Implicit

/-!
# Analytic arcs on regular polynomial loci

This file isolates the regular-locus part of analytic curve selection.
Mathlib's finite-dimensional implicit-function theorem supplies a canonical
local chart of a regular level set, its level-set identity, and its derivative.
If that chart is analytic, a tangent direction on which the distinguished
coordinate is positive produces a positive-coordinate analytic arc.

For a polynomial map the strict differentiability and analyticity of the
original map are standard.  The remaining regular-locus library gap is the
analyticity of the multidimensional implicit chart: mathlib currently proves
that its implicit function is strictly differentiable, and has smoothness
transfer theorems, but its analytic inverse-function theorem is one-dimensional.
The theorem below states that missing hypothesis exactly; it does not assume
an arc in the target set.

Strict polynomial inequalities which hold at the base point form an open
neighborhood `U`.  They can therefore be included without any further curve
selection.  Inequalities which vanish at the base point, and singular level
sets, remain outside this regular-locus result.
-/

set_option autoImplicit false

noncomputable section

open Filter Set SignType Topology

namespace Math

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A finite polynomial sign cell with no zero signs is open.  These are
exactly the sign conditions which persist automatically at a base point. -/
theorem PolynomialSignCell.isOpen_signCell_of_ne_zero
    {ι σ : Type*} [Finite ι]
    (P : ι → MvPolynomial σ ℝ)
    (τ : PolynomialSignCell.SignPattern ι)
    (hτ : ∀ i, τ i ≠ 0) :
    IsOpen (PolynomialSignCell.signCell P τ) := by
  rw [PolynomialSignCell.signCell_eq_iInter_signCondition]
  apply isOpen_iInter_of_finite
  intro i
  cases hi : τ i with
  | zero =>
      exact (hτ i hi).elim
  | neg =>
      have hopen :
          IsOpen
            {x : PolynomialSignCell.Assignment σ |
              MvPolynomial.eval x (P i) < 0} :=
        isOpen_lt (MvPolynomial.continuous_eval (P i)) continuous_const
      simpa [PolynomialSignCell.signCondition, hi,
        sign_eq_neg_one_iff] using hopen
  | pos =>
      have hopen :
          IsOpen
            {x : PolynomialSignCell.Assignment σ |
              0 < MvPolynomial.eval x (P i)} :=
        isOpen_lt continuous_const (MvPolynomial.continuous_eval (P i))
      simpa [PolynomialSignCell.signCondition, hi,
        sign_eq_one_iff] using hopen

/-- An analytic chart of a regular level set, with a positively oriented
tangent, gives a positive-coordinate analytic arc.

The set `U` packages any strict sign conditions valid at the base point.
The arc is constructed from mathlib's canonical implicit function in the
kernel direction `d`; level-set membership and orientation are conclusions,
not hypotheses about the resulting arc. -/
theorem hasPositiveCoordinateAnalyticArcAt_regularLevel
    {f : E → F} {f' : E →L[ℝ] F} {x₀ : E}
    {coordinate : E →L[ℝ] ℝ} {U : Set E}
    (hf : HasStrictFDerivAt f f' x₀)
    (hsurj : f'.range = ⊤)
    (hchart :
      AnalyticAt ℝ
        (hf.implicitFunction f f' hsurj (f x₀)) 0)
    (d : f'.ker)
    (hcoordinate_d : 0 < coordinate d.1)
    (hcoordinate_x₀ : coordinate x₀ = 0)
    (hU : U ∈ 𝓝 x₀) :
    HasPositiveCoordinateAnalyticArcAt
      ({x | f x = f x₀} ∩ U) coordinate x₀ := by
  let line : ℝ → f'.ker := fun t => t • d
  let chart : f'.ker → E :=
    hf.implicitFunction f f' hsurj (f x₀)
  let arc : ℝ → E := chart ∘ line
  have hline_analytic : AnalyticAt ℝ line 0 := by
    let lineCLM : ℝ →L[ℝ] f'.ker :=
      ContinuousLinearMap.toSpanSingleton ℝ d
    have hline_eq : line = lineCLM := by
      funext t
      simp [line, lineCLM]
    rw [hline_eq]
    exact lineCLM.analyticAt 0
  have harc_analytic : AnalyticAt ℝ arc 0 := by
    exact hchart.comp_of_eq hline_analytic (by simp [line])
  have hline0 : line 0 = 0 := by
    simp [line]
  have harc0 : arc 0 = x₀ := by
    simp [arc, chart, line]
  have hline_tendsto : Tendsto line (𝓝 (0 : ℝ)) (𝓝 0) :=
    by simpa [hline0] using hline_analytic.continuousAt.tendsto
  have hpair_tendsto :
      Tendsto (fun t => (f x₀, line t)) (𝓝 (0 : ℝ))
        (𝓝 (f x₀, (0 : f'.ker))) :=
    tendsto_const_nhds.prodMk_nhds hline_tendsto
  have hlevel :
      ∀ᶠ t in 𝓝 (0 : ℝ), f (arc t) = f x₀ := by
    have h :=
      hpair_tendsto.eventually (hf.map_implicitFunction_eq hsurj)
    simpa [arc, chart] using h
  have harc_tendsto : Tendsto arc (𝓝 (0 : ℝ)) (𝓝 x₀) := by
    simpa [harc0] using harc_analytic.continuousAt.tendsto
  have harc_U : ∀ᶠ t in 𝓝 (0 : ℝ), arc t ∈ U :=
    harc_tendsto.eventually hU
  have hline_deriv : HasDerivAt line d 0 := by
    simpa [line] using (hasDerivAt_id (𝕜 := ℝ) 0).smul_const d
  have hchart_deriv :
      HasFDerivAt chart f'.ker.subtypeL 0 := by
    simpa [chart] using (hf.to_implicitFunction hsurj).hasFDerivAt
  have hchart_deriv_line0 :
      HasFDerivAt chart f'.ker.subtypeL (line 0) := by
    simpa [hline0] using hchart_deriv
  have harc_deriv : HasDerivAt arc d.1 0 := by
    simpa [arc] using
      hchart_deriv_line0.comp_hasDerivAt 0 hline_deriv
  have hcoordinate_deriv :
      HasDerivAt (fun t => coordinate (arc t)) (coordinate d.1) 0 := by
    change HasDerivAt (coordinate ∘ arc) (coordinate d.1) 0
    exact coordinate.hasFDerivAt.comp_hasDerivAt 0 harc_deriv
  have hcoordinate_arc0 : coordinate (arc 0) = 0 := by
    rw [harc0, hcoordinate_x₀]
  have hcoordinate_pos :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < coordinate (arc t) := by
    have hsign :
        ∀ᶠ t in 𝓝 (0 : ℝ),
          SignType.sign (coordinate (arc t)) = SignType.sign (t - 0) := by
      apply eventually_nhdsWithin_sign_eq_of_deriv_pos
      · rw [hcoordinate_deriv.deriv]
        exact hcoordinate_d
      · exact hcoordinate_arc0
    filter_upwards
      [hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with
      t ht htright
    have ht_one : sign t = 1 := sign_pos htright
    rw [sub_zero, ht_one] at ht
    exact sign_eq_one_iff.mp ht
  have hgood :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        arc t ∈ ({x | f x = f x₀} ∩ U) ∧
          0 < coordinate (arc t) := by
    filter_upwards
      [hlevel.filter_mono nhdsWithin_le_nhds,
        harc_U.filter_mono nhdsWithin_le_nhds,
        hcoordinate_pos] with t htlevel htU htpos
    exact ⟨⟨htlevel, htU⟩, htpos⟩
  obtain ⟨eta, heta, hinterval⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
  exact ⟨arc, eta, heta, harc_analytic, harc0,
    hcoordinate_x₀, fun t ht => hinterval ht⟩

/-- The regular-level result transported to any larger target set.

This is convenient when a polynomial sign cell has been identified as a
relative-open subset of a regular equality locus. -/
theorem hasPositiveCoordinateAnalyticArcAt_of_regularLevel_subset
    {f : E → F} {f' : E →L[ℝ] F} {x₀ : E}
    {coordinate : E →L[ℝ] ℝ} {U A : Set E}
    (hf : HasStrictFDerivAt f f' x₀)
    (hsurj : f'.range = ⊤)
    (hchart :
      AnalyticAt ℝ
        (hf.implicitFunction f f' hsurj (f x₀)) 0)
    (d : f'.ker)
    (hcoordinate_d : 0 < coordinate d.1)
    (hcoordinate_x₀ : coordinate x₀ = 0)
    (hU : U ∈ 𝓝 x₀)
    (hsubset : {x | f x = f x₀} ∩ U ⊆ A) :
    HasPositiveCoordinateAnalyticArcAt A coordinate x₀ := by
  obtain ⟨arc, eta, heta, harc, harc0, hcoordinate0, hmem⟩ :=
    hasPositiveCoordinateAnalyticArcAt_regularLevel hf hsurj hchart d
      hcoordinate_d hcoordinate_x₀ hU
  exact ⟨arc, eta, heta, harc, harc0, hcoordinate0,
    fun t ht => ⟨hsubset (hmem t ht).1, (hmem t ht).2⟩⟩

/-- Regular-locus curve selection inside a strict polynomial sign cell.

All zero constraints are collected in the regular level map `f`; the
remaining polynomial signs are required to be nonzero.  The theorem then
constructs the desired analytic arc from the canonical implicit chart. -/
theorem hasPositiveCoordinateAnalyticArcAt_strictPolynomialCell
    {ι σ F : Type*} [Finite ι] [Fintype σ]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
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
    (hsurj : f'.range = ⊤)
    (hchart :
      AnalyticAt ℝ
        (hf.implicitFunction f f' hsurj (f x₀)) 0)
    (d : f'.ker)
    (hcoordinate_d : 0 < coordinate d.1)
    (hcoordinate_x₀ : coordinate x₀ = 0) :
    HasPositiveCoordinateAnalyticArcAt
      ({x | f x = f x₀} ∩
        PolynomialSignCell.signCell P τ)
      coordinate x₀ := by
  apply hasPositiveCoordinateAnalyticArcAt_regularLevel
    hf hsurj hchart d hcoordinate_d hcoordinate_x₀
  exact (PolynomialSignCell.isOpen_signCell_of_ne_zero P τ hτ).mem_nhds hx₀

end Math
