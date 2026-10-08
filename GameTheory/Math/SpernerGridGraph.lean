import GameTheory.Math.SpernerGridDoors
import GameTheory.Math.EndOfLine

/-! Local directed pointers for the square-grid Sperner graph. A single extra
node supplies the known boundary source. Invalid triangle coordinates are
isolated, and every other endpoint is a trichromatic triangular cell. -/

namespace GameTheory.Math.Sperner

/-- The first lower triangle borders the unique entrance of the standard boundary. -/
def entranceTriangle : GridTriangle := ⟨0, 0, false⟩

/-- Compute one directed pointer by inspecting three corners and crossing one edge.
The empty node is the boundary source; invalid coordinates remain isolated. -/
def gridPointer (n : ℕ) (interior : ℕ → ℕ → Fin 3) (incoming : Bool) :
    Option GridTriangle → Option GridTriangle
  | none => if incoming then none else some entranceTriangle
  | some t =>
    if ValidTriangle n t then
      match gridDoor (standardGridColor n interior) t incoming with
      | none => some t
      | some p => match across n t p with
        | some (u, _) => some u
        | none => if incoming then none else some t
    else some t

private theorem opposite_door {n : ℕ} {color : ℕ → ℕ → Fin 3}
    {t u : GridTriangle} {p q : Fin 3} {incoming : Bool}
    (ha : across n t p = some (u, q))
    (hd : gridDoor color t incoming = some p) :
    gridDoor color u (!incoming) = some q := by
  apply (gridDoor_eq_some_iff _ _ _ _).mpr
  have hs := (gridDoor_eq_some_iff _ _ _ _).mp hd
  rw [gridSideFlux_eq_edgeFlux] at hs ⊢
  obtain ⟨hc, hc'⟩ := across_corners_reverse ha
  rw [hc, hc', edgeFlux_reverse, hs]
  cases incoming <;> rfl

/-- The opposite pointer reverses every selected door, including the boundary entrance. -/
theorem gridPointer_inverse {n : ℕ} {interior : ℕ → ℕ → Fin 3}
    {t : GridTriangle} {p : Fin 3} {incoming : Bool}
    (hn : 0 < n) (hv : ValidTriangle n t)
    (hd : gridDoor (standardGridColor n interior) t incoming = some p) :
    gridPointer n interior (!incoming) (gridPointer n interior incoming (some t)) =
      some t := by
  cases ha : across n t p with
  | none =>
    obtain ⟨hin, ht, _⟩ := missing_gridDoor hn hv hd ha
    subst incoming
    subst t
    simp [gridPointer, hv, hd, ha, entranceTriangle]
  | some uq =>
    rcases uq with ⟨u, q⟩
    have hu := across_valid hv ha
    have hr := across_reverse hv ha
    have hdoor := opposite_door ha hd
    simp [gridPointer, hv, hd, ha, hu, hdoor, hr]

/-- A local pointer is nontrivial exactly when the triangle has that door. -/
theorem gridPointer_ne_self_iff {n : ℕ} {interior : ℕ → ℕ → Fin 3}
    {t : GridTriangle} (incoming : Bool) (hn : 0 < n) (hv : ValidTriangle n t) :
    gridPointer n interior incoming (some t) ≠ some t ↔
      (gridDoor (standardGridColor n interior) t incoming).isSome = true := by
  cases hd : gridDoor (standardGridColor n interior) t incoming with
  | none => simp [gridPointer, hv, hd]
  | some p =>
    cases ha : across n t p with
    | none =>
      obtain ⟨hin, _, _⟩ := missing_gridDoor hn hv hd ha
      subst incoming
      simp [gridPointer, hv, hd, ha]
    | some uq =>
      rcases uq with ⟨u, q⟩
      have hne := across_distinct ha
      simp [gridPointer, hv, hd, ha, hne]

private theorem gridPointer_inverse_of_isSome {n : ℕ}
    {interior : ℕ → ℕ → Fin 3} {t : GridTriangle} {incoming : Bool}
    (hn : 0 < n) (hv : ValidTriangle n t)
    (h : (gridDoor (standardGridColor n interior) t incoming).isSome = true) :
    gridPointer n interior (!incoming) (gridPointer n interior incoming (some t)) =
      some t := by
  cases hd : gridDoor (standardGridColor n interior) t incoming with
  | none => simp [hd] at h
  | some p => exact gridPointer_inverse hn hv hd

/-- Incoming doors correspond exactly to consistent nontrivial predecessor pointers. -/
theorem grid_hasPredecessor_iff {n : ℕ} {interior : ℕ → ℕ → Fin 3}
    {t : GridTriangle} (hn : 0 < n) (hv : ValidTriangle n t) :
    EndOfLine.HasPredecessor (gridPointer n interior true) (gridPointer n interior false)
        (some t) ↔ (gridDoor (standardGridColor n interior) t true).isSome = true := by
  constructor
  · intro h
    exact (gridPointer_ne_self_iff true hn hv).mp h.1
  · intro h
    exact ⟨(gridPointer_ne_self_iff true hn hv).mpr h,
      gridPointer_inverse_of_isSome hn hv h⟩

/-- Outgoing doors correspond exactly to consistent nontrivial successor pointers. -/
theorem grid_hasSuccessor_iff {n : ℕ} {interior : ℕ → ℕ → Fin 3}
    {t : GridTriangle} (hn : 0 < n) (hv : ValidTriangle n t) :
    EndOfLine.HasSuccessor (gridPointer n interior true) (gridPointer n interior false)
        (some t) ↔ (gridDoor (standardGridColor n interior) t false).isSome = true := by
  constructor
  · intro h
    exact (gridPointer_ne_self_iff false hn hv).mp h.1
  · intro h
    exact ⟨(gridPointer_ne_self_iff false hn hv).mpr h,
      gridPointer_inverse_of_isSome hn hv h⟩

/-- A valid triangle is an endpoint exactly when its corner colors are all distinct. -/
theorem grid_endpoint_iff {n : ℕ} {interior : ℕ → ℕ → Fin 3}
    {t : GridTriangle} (hn : 0 < n) (hv : ValidTriangle n t) :
    EndOfLine.IsEndpoint (gridPointer n interior true) (gridPointer n interior false)
        (some t) ↔
      Trichromatic
        (standardGridColor n interior (corner t 0).1 (corner t 0).2)
        (standardGridColor n interior (corner t 1).1 (corner t 1).2)
        (standardGridColor n interior (corner t 2).1 (corner t 2).2) := by
  rw [EndOfLine.IsEndpoint, grid_hasPredecessor_iff hn hv, grid_hasSuccessor_iff hn hv,
    ← door_imbalance_iff_trichromatic]
  change ((_ = true ∧ ¬_ = true) ∨ (_ = true ∧ ¬_ = true)) ↔
    (gridDoor (standardGridColor n interior) t true).isSome ≠
      (gridDoor (standardGridColor n interior) t false).isSome
  cases (gridDoor (standardGridColor n interior) t true).isSome <;>
    cases (gridDoor (standardGridColor n interior) t false).isSome <;> decide

/-- The added boundary node is a genuine source at every positive grid size. -/
theorem grid_source (n : ℕ) (interior : ℕ → ℕ → Fin 3) (hn : 0 < n) :
    gridPointer n interior true none = none ∧ gridPointer n interior false none ≠ none ∧
      gridPointer n interior true (gridPointer n interior false none) = none := by
  have hv : ValidTriangle n entranceTriangle := ⟨hn, hn⟩
  have hd : gridDoor (standardGridColor n interior) entranceTriangle true = some 0 :=
    origin_gridDoor n interior hn
  have ha : across n entranceTriangle 0 = none := rfl
  simp [gridPointer, hv, hd, ha]

/-- Every endpoint other than the added source decodes to a valid trichromatic cell.
This covers endpoints on all components, not just the path from the source. -/
theorem grid_endpoint_decodes {n : ℕ} {interior : ℕ → ℕ → Fin 3}
    {node : Option GridTriangle} (hn : 0 < n) (hne : node ≠ none)
    (he : EndOfLine.IsEndpoint (gridPointer n interior true) (gridPointer n interior false)
      node) :
    ∃ t, node = some t ∧ ValidTriangle n t ∧
      Trichromatic
        (standardGridColor n interior (corner t 0).1 (corner t 0).2)
        (standardGridColor n interior (corner t 1).1 (corner t 1).2)
        (standardGridColor n interior (corner t 2).1 (corner t 2).2) := by
  cases node with
  | none => exact False.elim (hne rfl)
  | some t =>
    by_cases hv : ValidTriangle n t
    · exact ⟨t, rfl, hv, (grid_endpoint_iff hn hv).mp he⟩
    · simp [EndOfLine.IsEndpoint, EndOfLine.HasPredecessor, EndOfLine.HasSuccessor,
        gridPointer, hv] at he

/-- The local graph has an endpoint represented by a bounded triangular cell. -/
theorem exists_grid_endpoint (n : ℕ) (interior : ℕ → ℕ → Fin 3) (hn : 0 < n) :
    ∃ t, ValidTriangle n t ∧ EndOfLine.IsEndpoint
      (gridPointer n interior true) (gridPointer n interior false) (some t) := by
  obtain ⟨i, hi, j, hj, htri⟩ := exists_grid_trichromatic
    (standardGridColor_boundary n interior hn)
  rcases htri with hlower | hupper
  · refine ⟨⟨i, j, false⟩, ⟨hi, hj⟩, (grid_endpoint_iff hn ⟨hi, hj⟩).mpr ?_⟩
    simpa [corner] using hlower
  · refine ⟨⟨i, j, true⟩, ⟨hi, hj⟩, (grid_endpoint_iff hn ⟨hi, hj⟩).mpr ?_⟩
    simpa [corner] using hupper

end GameTheory.Math.Sperner
