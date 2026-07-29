/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AnalyticMixedObstruction
import Math.LinearAlgebra.FiniteRayMaximum

/-!
# Fixed analytic maximizers for finite certificate rays

This file joins two independent reductions:

* a finite ray family attains the supremum of every positive-mass
  certificate ratio;
* a finite family of analytic value germs has one fixed eventual maximizer.

The theorem deliberately assumes that a common finite ray index already
parametrizes the certificate cone on a right neighborhood.  Producing such a
family from a parameter-dependent matrix is the basic-feasible-solution
stabilization step.
-/

open Set Topology

namespace Math
namespace LinearAlgebra

noncomputable section

/-- If a parameter-dependent certificate cone has a common finite ray
decomposition and the ray ratios are analytic germs, then one fixed ray
attains the certificate-ratio supremum throughout a right neighborhood.

The strict positive-mass hypothesis excludes candidates which cease to be
normalized feasible rays.  In the Farkas application the candidates have
mass exactly one. -/
theorem exists_fixed_eventual_positiveMassRay_sSup_eq
    {Certificate Ray : Type*} [Fintype Ray] [Nonempty Ray]
    (ray : ℝ → Ray → Certificate)
    (B M : ℝ → Certificate → ℝ)
    (rayValue : Ray → ℝ → ℝ) {x₀ : ℝ}
    (hanalytic : ∀ r, AnalyticAt ℝ (rayValue r) x₀)
    (hdata :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        (∀ r, 0 ≤ M x (ray x r)) ∧
          (∀ r, M x (ray x r) = 0 → B x (ray x r) ≤ 0) ∧
          HasFiniteRayDecomposition (ray x) (B x) (M x))
    (hratio :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ r,
        0 < M x (ray x r) ∧
          rayValue r x = B x (ray x r) / M x (ray x r)) :
    ∃ rMax,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        0 < M x (ray x rMax) ∧
          sSup (positiveMassRatioSet (B x) (M x)) =
            rayValue rMax x := by
  obtain ⟨rMax, hrMax⟩ :=
    finite_analytic_family_eventually_fixed_maximizer rayValue hanalytic
  refine ⟨rMax, ?_⟩
  filter_upwards [hrMax, hdata, hratio] with x hxMax hxData hxRatio
  obtain ⟨hrayMass, hzeroRay, hdecompose⟩ := hxData
  have hpositiveRay : ∃ r, 0 < M x (ray x r) := by
    let r : Ray := Classical.choice inferInstance
    exact ⟨r, (hxRatio r).1⟩
  obtain ⟨rBound, hrBoundMass, _hrayBound, hcertificateBound⟩ :=
    exists_maximizing_positiveMass_ray
      (ray x) (B x) (M x) hrayMass hzeroRay hpositiveRay hdecompose
  obtain ⟨rSup, hrSupMass, hsSup⟩ :=
    exists_positiveMass_ray_sSup_eq
      (ray x) (B x) (M x) hrayMass hzeroRay hpositiveRay hdecompose
  have hboundValue_le :
      rayValue rBound x ≤ rayValue rMax x :=
    hxMax rBound
  have hrMaxValue_le :
      rayValue rMax x ≤ rayValue rBound x := by
    have h :=
      hcertificateBound (ray x rMax) (hxRatio rMax).1
    simpa [(hxRatio rMax).2, (hxRatio rBound).2] using h
  have hsupValue_le :
      rayValue rSup x ≤ rayValue rBound x := by
    have h :=
      hcertificateBound (ray x rSup) hrSupMass
    simpa [(hxRatio rSup).2, (hxRatio rBound).2] using h
  have hratioSetBdd :
      BddAbove (positiveMassRatioSet (B x) (M x)) := by
    refine ⟨B x (ray x rBound) / M x (ray x rBound), ?_⟩
    rintro q ⟨z, hzMass, rfl⟩
    exact hcertificateBound z hzMass
  have hrBoundRatio_le_sSup :
      B x (ray x rBound) / M x (ray x rBound) ≤
        sSup (positiveMassRatioSet (B x) (M x)) :=
    le_csSup hratioSetBdd ⟨ray x rBound, hrBoundMass, rfl⟩
  have hrBoundValue_le_sup :
      rayValue rBound x ≤ rayValue rSup x := by
    rw [hsSup] at hrBoundRatio_le_sSup
    simpa [(hxRatio rBound).2, (hxRatio rSup).2] using
      hrBoundRatio_le_sSup
  have hrSup_eq_max :
      rayValue rSup x = rayValue rMax x := by
    apply le_antisymm
    · exact hsupValue_le.trans hboundValue_le
    · exact hrMaxValue_le.trans hrBoundValue_le_sup
  exact ⟨(hxRatio rMax).1, by
    calc
      sSup (positiveMassRatioSet (B x) (M x)) =
          B x (ray x rSup) / M x (ray x rSup) := hsSup
      _ = rayValue rSup x := (hxRatio rSup).2.symm
      _ = rayValue rMax x := hrSup_eq_max⟩

end
end LinearAlgebra
end Math
