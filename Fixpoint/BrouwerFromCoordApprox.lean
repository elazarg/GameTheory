import Fixpoint.BrouwerFromApprox
import Mathlib

set_option autoImplicit false

namespace Fixpoint

section LocalCoordApprox

variable {ι : Type*} [Fintype ι]

theorem hasApproxFixedPoints_of_coordwise_bounds_local
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (hcoordApprox :
      ∀ n : ℕ, ∃ x : stdSimplex ℝ ι, ∀ i : ι,
        |f x i - x i| ≤ (1 : ℝ) / (n + 1)) :
    ∀ n : ℕ, ∃ x : stdSimplex ℝ ι, dist (f x) x ≤ (1 : ℝ) / (n + 1) := by
  intro n
  rcases hcoordApprox n with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  refine (dist_pi_le_iff (by positivity)).2 ?_
  intro i
  simpa [Real.dist_eq] using hx i

end LocalCoordApprox

/--
If each scale `1/(n+1)` admits a simplex point with coordinatewise error bounded by that scale,
then `f` has a fixed point.
-/
theorem exists_fixedPoint_of_coordwiseApprox_on_stdSimplex
    {ι : Type*} [Fintype ι]
    (f : stdSimplex Real ι → stdSimplex Real ι)
    (hcont : Continuous f)
    (hcoordApprox :
      ∀ n : ℕ, ∃ x : stdSimplex Real ι, ∀ i : ι,
        |f x i - x i| ≤ (1 : ℝ) / (n + 1)) :
    ∃ x : stdSimplex Real ι, IsFixedPt f x := by
  refine exists_fixedPoint_of_approx_on_stdSimplex f hcont ?_
  exact hasApproxFixedPoints_of_coordwise_bounds_local f hcoordApprox

end Fixpoint
