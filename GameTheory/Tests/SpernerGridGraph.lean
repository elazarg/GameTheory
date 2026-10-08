import GameTheory.Math.SpernerGridGraph

/-! Local graph controls cover short paths, a disconnected six-triangle cycle,
the smallest grid, and isolation of unused coordinate encodings. -/

namespace GameTheory.Tests.SpernerGridGraph

open GameTheory.Math.Sperner
open GameTheory.Math.EndOfLine

/-- An isolated interior color-one vertex surrounded by color-zero vertices. -/
def cycleInterior (i j : ℕ) : Fin 3 := if i = 2 ∧ j = 2 then 1 else 0

example : gridPointer 5 cycleInterior false (some ⟨1, 1, false⟩) = some ⟨1, 1, true⟩ ∧
    gridPointer 5 cycleInterior false (some ⟨1, 1, true⟩) = some ⟨1, 2, false⟩ ∧
    gridPointer 5 cycleInterior false (some ⟨1, 2, false⟩) = some ⟨2, 2, true⟩ ∧
    gridPointer 5 cycleInterior false (some ⟨2, 2, true⟩) = some ⟨2, 2, false⟩ ∧
    gridPointer 5 cycleInterior false (some ⟨2, 2, false⟩) = some ⟨2, 1, true⟩ ∧
    gridPointer 5 cycleInterior false (some ⟨2, 1, true⟩) = some ⟨1, 1, false⟩ := by decide

example : ¬IsEndpoint (gridPointer 5 cycleInterior true) (gridPointer 5 cycleInterior false)
    (some ⟨1, 1, false⟩) := by decide

example : gridPointer 2 (fun _ _ => 0) false (some entranceTriangle) =
    some ⟨1, 0, true⟩ := by decide

example : IsEndpoint (gridPointer 2 (fun _ _ => 0) true)
    (gridPointer 2 (fun _ _ => 0) false) (some ⟨1, 0, true⟩) := by decide

example : IsEndpoint (gridPointer 2 (fun _ _ => 2) true)
    (gridPointer 2 (fun _ _ => 2) false) (some ⟨0, 0, false⟩) := by decide

/-- At size one, the entrance triangle itself is trichromatic and is a valid answer. -/
example : IsEndpoint (gridPointer 1 (fun _ _ => 0) true)
    (gridPointer 1 (fun _ _ => 0) false) (some entranceTriangle) := by decide

example (interior : ℕ → ℕ → Fin 3) :
    gridPointer 1 interior true none = none ∧ gridPointer 1 interior false none ≠ none ∧
      gridPointer 1 interior true (gridPointer 1 interior false none) = none :=
  grid_source 1 interior (by decide)

example : gridPointer 2 cycleInterior true (some ⟨2, 0, false⟩) = some ⟨2, 0, false⟩ ∧
    gridPointer 2 cycleInterior false (some ⟨2, 0, false⟩) = some ⟨2, 0, false⟩ ∧
    ¬IsEndpoint (gridPointer 2 cycleInterior true) (gridPointer 2 cycleInterior false)
      (some ⟨2, 0, false⟩) := by decide

example : gridPointer 0 cycleInterior true (gridPointer 0 cycleInterior false none) ≠
    none := by decide

example (interior : ℕ → ℕ → Fin 3) (node : Option GridTriangle) (hne : node ≠ none)
    (h : IsEndpoint (gridPointer 5 interior true) (gridPointer 5 interior false) node) :
    ∃ t, node = some t ∧ ValidTriangle 5 t ∧
      Trichromatic
        (standardGridColor 5 interior (corner t 0).1 (corner t 0).2)
        (standardGridColor 5 interior (corner t 1).1 (corner t 1).2)
        (standardGridColor 5 interior (corner t 2).1 (corner t 2).2) :=
  grid_endpoint_decodes (by decide) hne h

end GameTheory.Tests.SpernerGridGraph
