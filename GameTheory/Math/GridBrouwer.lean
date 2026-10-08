import GameTheory.Math.GridSperner
import GameTheory.Math.SpernerGridGeometry
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Rational displacement vectors for three-color square-grid labelings.
At triangle barycenters, zero displacement and sufficiently small residuals
detect precisely the trichromatic cells. Boundary exclusions make the vectors
point inward or tangent to each edge. -/

namespace GameTheory.Math.Brouwer

/-- The three color vectors balance with equal weights. -/
def colorDisplacement (a : Fin 3) : ℚ × ℚ :=
  if a = 0 then (1, 1) else if a = 1 then (-1, 0) else (0, -1)

/-- Affine interpolation of the displacement vectors in a colored triangle. -/
def weightedDisplacement (a b c : Fin 3) (u v w : ℚ) : ℚ × ℚ :=
  (u * (colorDisplacement a).1 + v * (colorDisplacement b).1 +
      w * (colorDisplacement c).1,
    u * (colorDisplacement a).2 + v * (colorDisplacement b).2 +
      w * (colorDisplacement c).2)

/-- A small affine residual forces all three vertex colors, even without
nonnegative weights. Any affine line through two color vectors misses this box. -/
theorem weightedDisplacement_small_implies_trichromatic (a b c : Fin 3)
    (u v w : ℚ)
    (hsum : u + v + w = 1)
    (hx : |(weightedDisplacement a b c u v w).1| ≤ 1 / 6)
    (hy : |(weightedDisplacement a b c u v w).2| ≤ 1 / 6) :
    Sperner.Trichromatic a b c := by
  rw [abs_le] at hx hy
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [weightedDisplacement, colorDisplacement, Sperner.Trichromatic] at * <;>
    linarith

/-- Displacement at the barycenter of three colored vertices. -/
def barycenterDisplacement (a b c : Fin 3) : ℚ × ℚ :=
  weightedDisplacement a b c (1 / 3) (1 / 3) (1 / 3)

/-- Zero barycenter displacement detects exactly the trichromatic triples. -/
theorem barycenterDisplacement_eq_zero_iff (a b c : Fin 3) :
    barycenterDisplacement a b c = (0, 0) ↔ Sperner.Trichromatic a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [barycenterDisplacement, weightedDisplacement, colorDisplacement,
      Sperner.Trichromatic, Prod.mk.injEq]

/-- The discrete residual gap separates trichromatic cells from all other cells. -/
theorem barycenterDisplacement_small_iff (a b c : Fin 3) :
    (|(barycenterDisplacement a b c).1| ≤ 1 / 6 ∧
      |(barycenterDisplacement a b c).2| ≤ 1 / 6) ↔
      Sperner.Trichromatic a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [barycenterDisplacement, weightedDisplacement, colorDisplacement,
      Sperner.Trichromatic, Prod.mk.injEq]

/-- Evaluate the displacement of a grid triangle using its canonical corners. -/
def triangleBarycenterDisplacement (color : ℕ → ℕ → Fin 3)
    (t : Sperner.GridTriangle) : ℚ × ℚ :=
  barycenterDisplacement (color (Sperner.corner t 0).1 (Sperner.corner t 0).2)
    (color (Sperner.corner t 1).1 (Sperner.corner t 1).2)
    (color (Sperner.corner t 2).1 (Sperner.corner t 2).2)

/-- Canonical grid-corner formulation of the exact zero test. -/
theorem triangleBarycenterDisplacement_eq_zero_iff (color : ℕ → ℕ → Fin 3)
    (t : Sperner.GridTriangle) :
    triangleBarycenterDisplacement color t = (0, 0) ↔
      Sperner.Trichromatic (color (Sperner.corner t 0).1 (Sperner.corner t 0).2)
        (color (Sperner.corner t 1).1 (Sperner.corner t 1).2)
        (color (Sperner.corner t 2).1 (Sperner.corner t 2).2) :=
  barycenterDisplacement_eq_zero_iff _ _ _

/-- Small coordinate residuals at a barycenter force all three colors. -/
theorem triangleBarycenterDisplacement_small_iff (color : ℕ → ℕ → Fin 3)
    (t : Sperner.GridTriangle) :
    (|(triangleBarycenterDisplacement color t).1| ≤ 1 / 6 ∧
      |(triangleBarycenterDisplacement color t).2| ≤ 1 / 6) ↔
      Sperner.Trichromatic (color (Sperner.corner t 0).1 (Sperner.corner t 0).2)
        (color (Sperner.corner t 1).1 (Sperner.corner t 1).2)
        (color (Sperner.corner t 2).1 (Sperner.corner t 2).2) :=
  barycenterDisplacement_small_iff _ _ _

/-- Sperner boundary exclusions yield inward or tangent vectors on all four edges. -/
theorem gridBoundary_inward {color : ℕ → ℕ → Fin 3} {n : ℕ}
    (hb : Sperner.GridBoundary color n) :
    (∀ j, j ≤ n → 0 ≤ (colorDisplacement (color 0 j)).1) ∧
      (∀ i, i ≤ n → 0 ≤ (colorDisplacement (color i 0)).2) ∧
      (∀ j, j ≤ n → (colorDisplacement (color n j)).1 ≤ 0) ∧
      (∀ i, i ≤ n → (colorDisplacement (color i n)).2 ≤ 0) := by
  have hleft : ∀ a : Fin 3, a ≠ 1 → 0 ≤ (colorDisplacement a).1 := by decide
  have hbottom : ∀ a : Fin 3, a ≠ 2 → 0 ≤ (colorDisplacement a).2 := by decide
  have hright : ∀ a : Fin 3, a ≠ 0 → (colorDisplacement a).1 ≤ 0 := by decide
  have htop : ∀ a : Fin 3, a ≠ 0 → (colorDisplacement a).2 ≤ 0 := by decide
  exact ⟨fun j hj => hleft _ (hb.1 j hj),
    fun i hi => hbottom _ (hb.2.1 i hi),
    fun j hj => hright _ (hb.2.2.1 j hj),
    fun i hi => htop _ (hb.2.2.2 i hi)⟩

/-- Every boundary-respecting grid has a valid triangle with zero barycenter displacement. -/
theorem exists_grid_zero_displacement {color : ℕ → ℕ → Fin 3} {n : ℕ}
    (hb : Sperner.GridBoundary color n) :
    ∃ t, Sperner.ValidTriangle n t ∧ triangleBarycenterDisplacement color t = (0, 0) := by
  obtain ⟨i, hi, j, hj, h⟩ := Sperner.exists_grid_trichromatic hb
  rcases h with h | h
  · refine ⟨⟨i, j, false⟩, ⟨hi, hj⟩, ?_⟩
    apply (triangleBarycenterDisplacement_eq_zero_iff _ _).mpr
    simpa [Sperner.corner] using h
  · refine ⟨⟨i, j, true⟩, ⟨hi, hj⟩, ?_⟩
    apply (triangleBarycenterDisplacement_eq_zero_iff _ _).mpr
    simpa [Sperner.corner] using h

end GameTheory.Math.Brouwer



