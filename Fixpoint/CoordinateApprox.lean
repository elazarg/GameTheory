import Mathlib

set_option autoImplicit false

namespace Fixpoint

section CoordinateApprox

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise distance bounds imply a global distance bound on the simplex (pi metric). -/
theorem dist_le_of_forall_coord_dist_le
    {x y : stdSimplex ℝ ι} {r : ℝ} (hr : 0 ≤ r)
    (hcoord : ∀ i : ι, dist (x i) (y i) ≤ r) :
    dist x y ≤ r := by
  simpa [Subtype.dist_eq] using (dist_pi_le_iff hr).2 hcoord

/-- Coordinatewise absolute error bounds imply a global approximate fixed-point bound. -/
theorem dist_le_of_forall_coord_abs_sub_le
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (x : stdSimplex ℝ ι) {r : ℝ} (hr : 0 ≤ r)
    (hcoord : ∀ i : ι, |f x i - x i| ≤ r) :
    dist (f x) x ≤ r := by
  refine dist_le_of_forall_coord_dist_le (x := f x) (y := x) hr ?_
  intro i
  simpa [Real.dist_eq] using hcoord i

/-- Uniform coordinatewise bounds at scale `1/(n+1)` provide approximate fixed points. -/
theorem hasApproxFixedPoints_of_coordwise_bounds
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (hcoordApprox :
      ∀ n : ℕ, ∃ x : stdSimplex ℝ ι, ∀ i : ι,
        |f x i - x i| ≤ (1 : ℝ) / (n + 1)) :
    ∀ n : ℕ, ∃ x : stdSimplex ℝ ι, dist (f x) x ≤ (1 : ℝ) / (n + 1) := by
  intro n
  rcases hcoordApprox n with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  refine dist_le_of_forall_coord_abs_sub_le (f := f) x ?_ ?_
  · positivity
  · exact hx

end CoordinateApprox

end Fixpoint
