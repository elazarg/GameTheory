import GameTheory.Math.SpernerDoors
import GameTheory.Math.SpernerGridGeometry
import GameTheory.Math.GridSperner

/-! Oriented doors in square-grid triangles. Canonical boundary enforcement
leaves one exterior door, on the first bottom edge of the lower origin triangle. -/

namespace GameTheory.Math.Sperner

/-- Flux on one side of a colored grid triangle. -/
def gridSideFlux (color : ℕ → ℕ → Fin 3) (t : GridTriangle) (p : Fin 3) : ℤ :=
  sideFlux (color (corner t 0).1 (corner t 0).2)
    (color (corner t 1).1 (corner t 1).2) (color (corner t 2).1 (corner t 2).2) p

/-- Select a grid triangle's door of the requested orientation. -/
def gridDoor (color : ℕ → ℕ → Fin 3) (t : GridTriangle) (incoming : Bool) :
    Option (Fin 3) :=
  door (color (corner t 0).1 (corner t 0).2)
    (color (corner t 1).1 (corner t 1).2) (color (corner t 2).1 (corner t 2).2) incoming

/-- Numbered-side flux agrees with the edge between successive corners. -/
theorem gridSideFlux_eq_edgeFlux (color : ℕ → ℕ → Fin 3) (t : GridTriangle) (p : Fin 3) :
    gridSideFlux color t p = edgeFlux (color (corner t p).1 (corner t p).2)
      (color (corner t (p + 1)).1 (corner t (p + 1)).2) := by
  fin_cases p <;> rfl

/-- A grid side is selected exactly when its flux has the requested sign. -/
theorem gridDoor_eq_some_iff (color : ℕ → ℕ → Fin 3) (t : GridTriangle)
    (incoming : Bool) (p : Fin 3) :
    gridDoor color t incoming = some p ↔
      gridSideFlux color t p = (if incoming then (1 : ℤ) else -1) :=
  door_eq_some_iff _ _ _ incoming p

/-- The canonical coloring's only exterior door is the incoming origin side. -/
theorem missing_gridDoor {n : ℕ} {interior : ℕ → ℕ → Fin 3}
    {t : GridTriangle} {p : Fin 3} {incoming : Bool} (hn : 0 < n)
    (hv : ValidTriangle n t)
    (hd : gridDoor (standardGridColor n interior) t incoming = some p)
    (ha : across n t p = none) :
    incoming = true ∧ t = ⟨0, 0, false⟩ ∧ p = 0 := by
  have hf := (gridDoor_eq_some_iff _ _ incoming p).mp hd
  rcases t with ⟨x, y, upper⟩
  rcases hv with ⟨hx, hy⟩
  cases upper <;> fin_cases p
  all_goals simp [across] at ha
  all_goals
    cases incoming <;>
      simp_all [gridSideFlux, sideFlux, corner, standardGridColor, edgeFlux]
  all_goals split_ifs at hf <;> simp_all <;> omega

/-- The lower origin triangle has its incoming door on side zero. -/
theorem origin_gridDoor (n : ℕ) (interior : ℕ → ℕ → Fin 3) (_hn : 0 < n) :
    gridDoor (standardGridColor n interior) ⟨0, 0, false⟩ true = some 0 := by
  simp [gridDoor, door, sideFlux, corner, standardGridColor, edgeFlux]

end GameTheory.Math.Sperner
