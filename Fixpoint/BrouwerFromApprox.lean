import Mathlib
import Fixpoint.ApproximateToExact

set_option autoImplicit false

namespace Fixpoint

open Function

/--
Simplex-specialized approximate-to-exact fixed-point principle.
This is the exact compactness/continuity endgame needed once a Sperner layer
provides approximate fixed points.
-/
theorem exists_fixedPoint_of_approx_on_stdSimplex
    {ι : Type*} [Fintype ι]
    (f : stdSimplex Real ι → stdSimplex Real ι)
    (hcont : Continuous f)
    (happrox : ∀ n : ℕ, ∃ x : stdSimplex Real ι, dist (f x) x ≤ (1 : ℝ) / (n + 1)) :
    ∃ x : stdSimplex Real ι, IsFixedPt f x := by
  have hcompact : IsCompact (Set.univ : Set (stdSimplex Real ι)) := isCompact_univ
  have happrox' :
      ∀ n : ℕ, ∃ x ∈ (Set.univ : Set (stdSimplex Real ι)),
        dist (f x) x ≤ (1 : ℝ) / (n + 1) := by
    intro n
    rcases happrox n with ⟨x, hx⟩
    exact ⟨x, Set.mem_univ x, hx⟩
  rcases exists_fixedPoint_of_approx_on_compact
      (S := (Set.univ : Set (stdSimplex Real ι)))
      hcompact f hcont happrox' with ⟨x, _hxU, hfix⟩
  exact ⟨x, hfix⟩

end Fixpoint
