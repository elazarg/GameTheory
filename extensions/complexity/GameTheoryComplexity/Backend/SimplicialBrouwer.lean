import GameTheory.Math.GridBrouwer
import GameTheoryComplexity.Sperner

/-! Succinct simplicial Brouwer search uses the existing circuit-coded grid
but specifies answers by a rational displacement residual. Outputs select a
triangle and its barycenter; arbitrary rational-point outputs require a separate
encoding and interpolation bridge. The residual criterion is exact arithmetic,
so the certified color verifier also verifies this relation. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Math.Sperner GameTheory.Math.Brouwer

/-- Find a grid triangle whose barycenter has displacement at most one sixth
in each coordinate. The field interpolates the three color displacement vectors
affinely on each triangle of the unscaled square. -/
def simplicialBrouwerRelation (input word : List Bool) : Prop :=
  ∃ t, decodeGridNode (pairFst input).length word = some (some t) ∧
    |(triangleBarycenterDisplacement (spernerColor input) t).1| ≤ 1 / 6 ∧
    |(triangleBarycenterDisplacement (spernerColor input) t).2| ≤ 1 / 6

/-- The quantitative residual condition recognizes exactly trichromatic cells. -/
theorem simplicialBrouwerRelation_iff (input word : List Bool) :
    simplicialBrouwerRelation input word ↔ spernerRelation input word := by
  simp only [simplicialBrouwerRelation, spernerRelation,
    triangleBarycenterDisplacement_small_iff]

/-- Every accepted barycenter answer actually has zero displacement. -/
theorem simplicialBrouwerRelation_zero {input word : List Bool}
    (h : simplicialBrouwerRelation input word) :
    ∃ t, decodeGridNode (pairFst input).length word = some (some t) ∧
      triangleBarycenterDisplacement (spernerColor input) t = (0, 0) := by
  obtain ⟨t, hd, hx, hy⟩ := h
  exact ⟨t, hd, (triangleBarycenterDisplacement_eq_zero_iff _ _).mpr
    ((triangleBarycenterDisplacement_small_iff _ _).mp ⟨hx, hy⟩)⟩

/-- Residual answers have the same linear encoding bound as grid triangles. -/
theorem simplicialBrouwerRelation_polyBalanced : PolyBalanced simplicialBrouwerRelation := by
  have h : simplicialBrouwerRelation = spernerRelation :=
    funext fun input => funext fun word => propext (simplicialBrouwerRelation_iff input word)
  rw [h]
  exact spernerRelation_polyBalanced

/-- The existing polynomial-time verifier checks the rational residual predicate
through its proved equivalence, without enumerating the exponential grid. -/
theorem simplicialBrouwerRelation_mem_FNP : simplicialBrouwerRelation ∈ FNP := by
  have h : simplicialBrouwerRelation = spernerRelation :=
    funext fun input => funext fun word => propext (simplicialBrouwerRelation_iff input word)
  rw [h]
  exact spernerRelation_mem_FNP

/-- Every residual answer decodes to the same encoded Sperner triangle. -/
def spernerToSimplicialBrouwerReduction :
    SearchReduction spernerRelation simplicialBrouwerRelation where
  instanceMap := id
  instanceMap_mem_FP := id_mem_FP
  decode := fun v => v 1
  decode_mem_FPn := cobham_iff_FPn.mp (.proj 1)
  sound := fun input word h => (simplicialBrouwerRelation_iff input word).mp h

/-- Every trichromatic triangle has a zero residual at its barycenter. -/
def simplicialBrouwerToSpernerReduction :
    SearchReduction simplicialBrouwerRelation spernerRelation where
  instanceMap := id
  instanceMap_mem_FP := id_mem_FP
  decode := fun v => v 1
  decode_mem_FPn := cobham_iff_FPn.mp (.proj 1)
  sound := fun input word h => (simplicialBrouwerRelation_iff input word).mpr h

end GameTheory.Complexity.Backend
