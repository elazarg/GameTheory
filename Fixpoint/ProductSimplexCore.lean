import Mathlib
import Fixpoint.ApproximateToExact

set_option autoImplicit false

namespace Fixpoint

open Function

/-- Product of per-player simplices (mixed profiles as coordinate distributions). -/
abbrev MixedSimplex
    (ι : Type*) (A : ι → Type _) [Fintype ι] [∀ i, Fintype (A i)] : Type _ :=
  ∀ i, stdSimplex Real (A i)

section Compactness

variable {ι : Type*} {A : ι → Type _}
variable [Fintype ι] [∀ i, Fintype (A i)]

instance instCompactSpaceMixedSimplex :
    CompactSpace (MixedSimplex ι A) := by
  infer_instance

/-- The mixed-profile domain is compact. -/
theorem isCompact_univ_mixedSimplex :
    IsCompact (Set.univ : Set (MixedSimplex ι A)) := by
  simpa using (isCompact_univ : IsCompact (Set.univ : Set (MixedSimplex ι A)))

end Compactness

section ApproxToExact

variable {ι : Type*} {A : ι → Type _}
variable [Fintype ι] [∀ i, Fintype (A i)]

/--
On the mixed-profile product simplex, arbitrarily fine approximate fixed points imply an exact one.
-/
theorem exists_fixedPoint_of_approx_on_mixedSimplex
    (f : MixedSimplex ι A → MixedSimplex ι A)
    (hcont : Continuous f)
    (happrox : ∀ n : ℕ, ∃ x : MixedSimplex ι A, dist (f x) x ≤ (1 : ℝ) / (n + 1)) :
    ∃ x : MixedSimplex ι A, IsFixedPt f x := by
  have hcompact : IsCompact (Set.univ : Set (MixedSimplex ι A)) := isCompact_univ
  have happrox' :
      ∀ n : ℕ, ∃ x ∈ (Set.univ : Set (MixedSimplex ι A)),
        dist (f x) x ≤ (1 : ℝ) / (n + 1) := by
    intro n
    rcases happrox n with ⟨x, hx⟩
    exact ⟨x, Set.mem_univ x, hx⟩
  rcases exists_fixedPoint_of_approx_on_compact
      (S := (Set.univ : Set (MixedSimplex ι A)))
      hcompact f hcont happrox' with ⟨x, _hxU, hfix⟩
  exact ⟨x, hfix⟩

end ApproxToExact

end Fixpoint
