import Math.AnalyticCoordinateCurve

set_option autoImplicit false

noncomputable section

open Set

namespace Math
namespace GateGProjection

/--
Projecting any analytic power curve through a continuous linear map gives a
positive-coordinate analytic arc whenever every point of the source set
projects to the target set with positive distinguished coordinate.  The
power coordinate used to construct the source curve need not be the
distinguished coordinate of the projection.
-/
theorem HasAnalyticPowerCurveAt.project_to_positiveCoordinateArc
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : Set E} {B : Set F}
    {sourceCoordinate : E →L[ℝ] ℝ}
    {source₀ : E} {target₀ : F}
    (hcurve :
      HasAnalyticPowerCurveAt A sourceCoordinate source₀)
    (projection : E →L[ℝ] F)
    (coordinate : F →L[ℝ] ℝ)
    (hendpoint : projection source₀ = target₀)
    (hcoordinate₀ : coordinate target₀ = 0)
    (hproject :
      ∀ z ∈ A,
        projection z ∈ B ∧
          0 < coordinate (projection z)) :
    HasPositiveCoordinateAnalyticArcAt
      B coordinate target₀ := by
  obtain ⟨q, gamma, eta, hq, heta, hgamma,
    hgamma₀, hmem⟩ := hcurve
  let arc : ℝ → F := fun t => projection (gamma t)
  have harc : AnalyticAt ℝ arc 0 := by
    change AnalyticAt ℝ (projection ∘ gamma) 0
    exact (projection.analyticAt (gamma 0)).comp hgamma
  have harc₀ : arc 0 = target₀ := by
    simp [arc, hgamma₀, hendpoint]
  refine ⟨arc, eta, heta, harc, harc₀,
    hcoordinate₀, ?_⟩
  intro t ht
  exact hproject (gamma t) (hmem t ht).1

end GateGProjection
end Math
