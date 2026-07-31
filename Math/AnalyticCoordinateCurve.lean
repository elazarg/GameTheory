/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AnalyticPowerNormalization

/-!
# Analytic curves with an exact power coordinate

Curve selection naturally returns an analytic arc in an ambient
finite-dimensional space.  The analytic Bellman-germ construction
additionally needs one distinguished
coordinate, the discount complement, to equal an exact power of the new
parameter.  This file packages that coordinate-facing form.
-/

noncomputable section

open Filter Set Topology

namespace Math

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An analytic right arc in `A` through `x₀`, with a distinguished
continuous-linear coordinate which vanishes at `x₀` and is positive on the
punctured arc. -/
def HasPositiveCoordinateAnalyticArcAt
    (A : Set E) (coordinate : E →L[ℝ] ℝ) (x₀ : E) : Prop :=
  ∃ (arc : ℝ → E) (eta : ℝ),
    0 < eta ∧
      AnalyticAt ℝ arc 0 ∧
      arc 0 = x₀ ∧
      coordinate x₀ = 0 ∧
      ∀ t ∈ Ioo (0 : ℝ) eta,
        arc t ∈ A ∧ 0 < coordinate (arc t)

/-- An analytic right arc whose distinguished coordinate is exactly `t ^ q`
for one positive natural exponent. -/
def HasAnalyticPowerCurveAt
    (A : Set E) (coordinate : E →L[ℝ] ℝ) (x₀ : E) : Prop :=
  ∃ (q : ℕ) (gamma : ℝ → E) (eta : ℝ),
    0 < q ∧
      0 < eta ∧
      AnalyticAt ℝ gamma 0 ∧
      gamma 0 = x₀ ∧
      ∀ t ∈ Ioo (0 : ℝ) eta,
        gamma t ∈ A ∧ coordinate (gamma t) = t ^ q

/-- Enlarging the target set preserves a positive-coordinate analytic arc. -/
theorem HasPositiveCoordinateAnalyticArcAt.mono
    {A B : Set E} {coordinate : E →L[ℝ] ℝ} {x₀ : E}
    (h : HasPositiveCoordinateAnalyticArcAt A coordinate x₀)
    (hAB : A ⊆ B) :
    HasPositiveCoordinateAnalyticArcAt B coordinate x₀ := by
  obtain ⟨arc, eta, heta, harc, harc0, hcoordinate0, hmem⟩ := h
  exact ⟨arc, eta, heta, harc, harc0, hcoordinate0,
    fun t ht => ⟨hAB (hmem t ht).1, (hmem t ht).2⟩⟩

/-- Exact-power normalization for a distinguished continuous-linear
coordinate of an ambient analytic arc. -/
theorem HasPositiveCoordinateAnalyticArcAt.toHasAnalyticPowerCurveAt
    {A : Set E} {coordinate : E →L[ℝ] ℝ} {x₀ : E}
    (h : HasPositiveCoordinateAnalyticArcAt A coordinate x₀) :
    HasAnalyticPowerCurveAt A coordinate x₀ := by
  obtain ⟨arc, eta, heta, harc, harc0, hcoordinate0, hmem⟩ := h
  let graphSet : Set (ℝ × E) :=
    {p | p.2 ∈ A ∧ coordinate p.2 = p.1}
  let ell : ℝ → ℝ := fun t => coordinate (arc t)
  have hell : AnalyticAt ℝ ell 0 := by
    change AnalyticAt ℝ (coordinate ∘ arc) 0
    exact (coordinate.analyticAt (arc 0)).comp harc
  have hell0 : ell 0 = 0 := by
    simp [ell, harc0, hcoordinate0]
  have hell_pos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ell t := by
    filter_upwards [Ioo_mem_nhdsGT heta] with t ht
    exact (hmem t ht).2
  have hgraph : ∀ᶠ t in 𝓝[>] (0 : ℝ), (ell t, arc t) ∈ graphSet := by
    filter_upwards [Ioo_mem_nhdsGT heta] with t ht
    exact ⟨(hmem t ht).1, rfl⟩
  obtain ⟨q, gamma, eta', hq, heta', hgamma, hgamma0, hnormalized⟩ :=
    exists_analytic_power_parameterization
      (A := graphSet) hell harc hell0 hell_pos hgraph
  refine ⟨q, gamma, eta', hq, heta', hgamma, hgamma0.trans harc0, ?_⟩
  intro t ht
  have hm := hnormalized t ht
  change gamma t ∈ A ∧ coordinate (gamma t) = t ^ q at hm
  exact hm

/-- Restricting the target set preserves a power curve when the curve is
already eventually in the smaller set. -/
theorem HasAnalyticPowerCurveAt.mono
    {A B : Set E} {coordinate : E →L[ℝ] ℝ} {x₀ : E}
    (h : HasAnalyticPowerCurveAt A coordinate x₀) (hAB : A ⊆ B) :
    HasAnalyticPowerCurveAt B coordinate x₀ := by
  obtain ⟨q, gamma, eta, hq, heta, hgamma, hgamma0, hmem⟩ := h
  exact ⟨q, gamma, eta, hq, heta, hgamma, hgamma0,
    fun t ht => ⟨hAB (hmem t ht).1, (hmem t ht).2⟩⟩

end Math
