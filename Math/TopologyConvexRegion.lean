import Mathlib.Topology.Basic
import Mathlib.Topology.Continuous
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace Math
namespace Topology
namespace Convex
namespace Region

variable {E ι α : Type*}
variable [Preorder α]

def lowerBoundRegion (F : Set E) (coord : ι → E → α) (v : ι → α) : Set E :=
  {x | x ∈ F ∧ ∀ i : ι, v i ≤ coord i x}

theorem coord_lower_isClosed
    [TopologicalSpace E] [TopologicalSpace α]
    (coord : E → α) (v : α)
    (hcont : Continuous coord)
    (hclosed : IsClosed {a : α | v ≤ a}) :
    IsClosed {x : E | v ≤ coord x} := by
  simpa [Set.preimage] using (_root_.IsClosed.preimage hcont hclosed)

theorem all_coord_lower_isClosed
    [TopologicalSpace E] [TopologicalSpace α]
    (coord : ι → E → α) (v : ι → α)
    (hclosed : ∀ i, IsClosed {x : E | v i ≤ coord i x}) :
    IsClosed {x : E | ∀ i : ι, v i ≤ coord i x} := by
  have hset :
      {x : E | ∀ i : ι, v i ≤ coord i x}
        = ⋂ i : ι, {x : E | v i ≤ coord i x} := by
    ext x
    simp
  rw [hset]
  exact isClosed_iInter hclosed

theorem lowerBoundRegion_isClosed
    [TopologicalSpace E] [TopologicalSpace α]
    {F : Set E} (coord : ι → E → α) (v : ι → α)
    (hF : IsClosed F)
    (hclosed : ∀ i, IsClosed {x : E | v i ≤ coord i x}) :
    IsClosed (lowerBoundRegion F coord v) := by
  have hregion :
      lowerBoundRegion F coord v
        = F ∩ {x : E | ∀ i : ι, v i ≤ coord i x} := by
    ext x
    rfl
  rw [hregion]
  exact hF.inter (all_coord_lower_isClosed coord v hclosed)

theorem lowerBoundRegion_isCompact
    [TopologicalSpace E] [T2Space E] [TopologicalSpace α]
    {F : Set E} (coord : ι → E → α) (v : ι → α)
    (hF : IsCompact F)
    (hclosed : ∀ i, IsClosed {x : E | v i ≤ coord i x}) :
    IsCompact (lowerBoundRegion F coord v) := by
  refine _root_.IsCompact.of_isClosed_subset hF
    (lowerBoundRegion_isClosed coord v hF.isClosed hclosed) ?_
  intro x hx
  exact hx.1

theorem lowerBoundRegion_isConvex
    [AddCommMonoid E] [Module ℝ E]
    {F : Set E} (coord : ι → E → ℝ) (v : ι → ℝ)
    (hF : Convex ℝ F)
    (hconv : ∀ i, Convex ℝ {x : E | v i ≤ coord i x}) :
    Convex ℝ (lowerBoundRegion F coord v) := by
  have hset :
      {x : E | ∀ i : ι, v i ≤ coord i x}
        = ⋂ i : ι, {x : E | v i ≤ coord i x} := by
    ext x
    simp
  have h2 : Convex ℝ {x : E | ∀ i : ι, v i ≤ coord i x} := by
    rw [hset]
    exact convex_iInter hconv
  have hregion :
      lowerBoundRegion F coord v
        = F ∩ {x : E | ∀ i : ι, v i ≤ coord i x} := by
    ext x
    rfl
  rw [hregion]
  exact hF.inter h2

end Region
end Convex
end Topology
end Math
