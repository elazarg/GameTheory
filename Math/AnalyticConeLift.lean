/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AnalyticConeDichotomy
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Analytic coefficient lifts on a fixed simplicial cone

A linearly independent finite generator family has a global linear left
inverse: apply a left inverse to its finite linear-combination map.  In a
finite-dimensional real normed space this coordinate map is continuous, so
its coefficients along an analytic curve are analytic.

Consequently, once a curve is known to remain in one fixed simplicial cone
on a punctured right neighborhood, it has a simultaneous analytic,
nonnegative coefficient lift on that same neighborhood.

Selecting the fixed support from an arbitrary finite cone is a separate
semialgebraic support-freezing step.  No such selection principle is assumed
or hidden here.
-/

open Finset Set Topology

namespace Math

noncomputable section

/-- The conic hull of a finite indexed generator family, expressed using
ordinary finitely indexed coefficient vectors. -/
def finiteConicHull
    {I E : Type*} [Fintype I] [AddCommMonoid E] [Module ℝ E]
    (generator : I → E) : Set E :=
  {x | ∃ coefficient : I → ℝ,
    (∀ i, 0 ≤ coefficient i) ∧
      ∑ i, coefficient i • generator i = x}

/-- A linearly independent finite generator family has a linear coordinate
map on the whole ambient space which is a left inverse to finite linear
combination. -/
theorem exists_linear_leftInverse_finiteCombination
    {I E : Type*} [Fintype I] [AddCommGroup E] [Module ℝ E]
    (generator : I → E) (hindependent : LinearIndependent ℝ generator) :
    ∃ coordinate : E →ₗ[ℝ] I → ℝ,
      ∀ coefficient : I → ℝ,
        coordinate (∑ i, coefficient i • generator i) = coefficient := by
  let combination : (I → ℝ) →ₗ[ℝ] E :=
    Fintype.linearCombination ℝ generator
  have hinjective : Function.Injective combination :=
    hindependent.fintypeLinearCombination_injective
  have hker : LinearMap.ker combination = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinjective
  let coordinate : E →ₗ[ℝ] I → ℝ := combination.leftInverse
  refine ⟨coordinate, fun coefficient => ?_⟩
  have hleft :=
    combination.leftInverse_apply_of_inj hker coefficient
  simpa [coordinate, combination, Fintype.linearCombination_apply] using
    hleft

/-- For any chosen left inverse, membership in the fixed simplicial cone is
equivalent to nonnegative extracted coordinates plus reconstruction. -/
theorem mem_finiteConicHull_iff_of_leftInverse
    {I E : Type*} [Fintype I] [AddCommGroup E] [Module ℝ E]
    (generator : I → E) (coordinate : E →ₗ[ℝ] I → ℝ)
    (hleft : ∀ coefficient : I → ℝ,
      coordinate (∑ i, coefficient i • generator i) = coefficient)
    (x : E) :
    x ∈ finiteConicHull generator ↔
      (∀ i, 0 ≤ coordinate x i) ∧
        ∑ i, coordinate x i • generator i = x := by
  constructor
  · rintro ⟨coefficient, hnonnegative, rfl⟩
    rw [hleft]
    exact ⟨hnonnegative, rfl⟩
  · rintro ⟨hnonnegative, hreconstruct⟩
    exact ⟨coordinate x, hnonnegative, hreconstruct⟩

/-- A fixed linearly independent support turns eventual conic membership of
an analytic curve into analytic, nonnegative coefficients which reconstruct
the curve. -/
theorem exists_analytic_nonnegative_fixedSupport_lift
    {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (generator : I → E) (hindependent : LinearIndependent ℝ generator)
    (curve : ℝ → E) {x₀ : ℝ}
    (hcurve : AnalyticAt ℝ curve x₀)
    (hcone :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        curve x ∈ finiteConicHull generator) :
    ∃ coordinate : E →ₗ[ℝ] I → ℝ,
      let coefficient : I → ℝ → ℝ :=
        fun i x => coordinate (curve x) i
      (∀ weights : I → ℝ,
        coordinate (∑ i, weights i • generator i) = weights) ∧
        (∀ i, AnalyticAt ℝ (coefficient i) x₀) ∧
        (∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
          (∀ i, 0 ≤ coefficient i x) ∧
            ∑ i, coefficient i x • generator i = curve x) := by
  obtain ⟨coordinate, hleft⟩ :=
    exists_linear_leftInverse_finiteCombination generator hindependent
  let coordinateCLM : E →L[ℝ] I → ℝ :=
    ⟨coordinate, coordinate.continuous_of_finiteDimensional⟩
  let coefficient : I → ℝ → ℝ :=
    fun i x => coordinate (curve x) i
  have hcoordinateCurve :
      AnalyticAt ℝ (fun x => coordinate (curve x)) x₀ := by
    exact (coordinateCLM.analyticAt (curve x₀)).comp hcurve
  have hcoefficient :
      ∀ i, AnalyticAt ℝ (coefficient i) x₀ := by
    exact analyticAt_pi_iff.mp hcoordinateCurve
  refine ⟨coordinate, hleft, hcoefficient, ?_⟩
  filter_upwards [hcone] with x hx
  have hx' :=
    (mem_finiteConicHull_iff_of_leftInverse
      generator coordinate hleft (curve x)).mp hx
  simpa [coefficient] using hx'

end

end Math
