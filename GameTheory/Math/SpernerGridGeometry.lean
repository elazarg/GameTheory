import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! Each square is split along its southwest-to-northeast diagonal into two
counterclockwise triangles. Adjacent triangles traverse their shared edge in
opposite directions; edges on the square boundary have no adjacent triangle. -/

namespace GameTheory.Math.Sperner

/-- One of the two triangles in a grid square. -/
structure GridTriangle where
  /-- Horizontal coordinate of the square's southwest corner. -/
  x : ℕ
  /-- Vertical coordinate of the square's southwest corner. -/
  y : ℕ
  /-- Select the upper half; false selects the lower half. -/
  upper : Bool
  deriving DecidableEq

/-- A triangle lies in a square of an `n` by `n` grid. -/
def ValidTriangle (n : ℕ) (t : GridTriangle) : Prop := t.x < n ∧ t.y < n

instance (n : ℕ) (t : GridTriangle) : Decidable (ValidTriangle n t) :=
  inferInstanceAs (Decidable (t.x < n ∧ t.y < n))

/-- Counterclockwise vertices, starting at the square's southwest corner. -/
def corner (t : GridTriangle) (p : Fin 3) : ℕ × ℕ :=
  if t.upper then
    if p = 0 then (t.x, t.y)
    else if p = 1 then (t.x + 1, t.y + 1) else (t.x, t.y + 1)
  else
    if p = 0 then (t.x, t.y)
    else if p = 1 then (t.x + 1, t.y) else (t.x + 1, t.y + 1)

/-- Cross the edge from vertex `p` to vertex `p + 1`, when it is an interior edge. -/
def across (n : ℕ) (t : GridTriangle) (p : Fin 3) : Option (GridTriangle × Fin 3) :=
  if t.upper then
    if p = 0 then some (⟨t.x, t.y, false⟩, 2)
    else if p = 1 then
      if t.y + 1 < n then some (⟨t.x, t.y + 1, false⟩, 0) else none
    else if t.x = 0 then none else some (⟨t.x - 1, t.y, false⟩, 1)
  else
    if p = 0 then
      if t.y = 0 then none else some (⟨t.x, t.y - 1, true⟩, 1)
    else if p = 1 then
      if t.x + 1 < n then some (⟨t.x + 1, t.y, true⟩, 2) else none
    else some (⟨t.x, t.y, true⟩, 0)

/-- Crossing an interior edge preserves membership in the grid. -/
theorem across_valid {n : ℕ} {t u : GridTriangle} {p q : Fin 3}
    (ht : ValidTriangle n t) (ha : across n t p = some (u, q)) : ValidTriangle n u := by
  rcases t with ⟨x, y, upper⟩
  cases upper <;> fin_cases p <;> simp [across] at ha
  · obtain ⟨hy, rfl, rfl⟩ := ha
    simp_all [ValidTriangle]
    omega
  · obtain ⟨hx, rfl, rfl⟩ := ha
    simp_all [ValidTriangle]
  · obtain ⟨rfl, rfl⟩ := ha
    exact ht
  · obtain ⟨rfl, rfl⟩ := ha
    exact ht
  · obtain ⟨hy, rfl, rfl⟩ := ha
    simp_all [ValidTriangle]
  · obtain ⟨hx, rfl, rfl⟩ := ha
    simp_all [ValidTriangle]
    omega

/-- Crossing the same shared edge from its other side returns to the original triangle. -/
theorem across_reverse {n : ℕ} {t u : GridTriangle} {p q : Fin 3}
    (ht : ValidTriangle n t) (ha : across n t p = some (u, q)) :
    across n u q = some (t, p) := by
  rcases t with ⟨x, y, upper⟩
  cases upper <;> fin_cases p <;> simp [across] at ha
  · obtain ⟨hy, rfl, rfl⟩ := ha
    have he : y - 1 + 1 = y := by omega
    simp_all [across, ValidTriangle]
  · obtain ⟨hx, rfl, rfl⟩ := ha
    simp [across]
  · obtain ⟨rfl, rfl⟩ := ha
    rfl
  · obtain ⟨rfl, rfl⟩ := ha
    rfl
  · obtain ⟨hy, rfl, rfl⟩ := ha
    simp [across]
  · obtain ⟨hx, rfl, rfl⟩ := ha
    have he : x - 1 + 1 = x := by omega
    simp_all [across, ValidTriangle]

/-- Two sides of a shared edge belong to different triangles. -/
theorem across_distinct {n : ℕ} {t u : GridTriangle} {p q : Fin 3}
    (ha : across n t p = some (u, q)) : u ≠ t := by
  rcases t with ⟨x, y, upper⟩
  cases upper <;> fin_cases p <;> simp [across] at ha
  · obtain ⟨_, rfl, rfl⟩ := ha
    simp
  · obtain ⟨_, rfl, rfl⟩ := ha
    simp
  · obtain ⟨rfl, rfl⟩ := ha
    simp
  · obtain ⟨rfl, rfl⟩ := ha
    simp
  · obtain ⟨_, rfl, rfl⟩ := ha
    simp
  · obtain ⟨_, rfl, rfl⟩ := ha
    simp

/-- Adjacent triangles traverse their common edge in opposite directions. -/
theorem across_corners_reverse {n : ℕ} {t u : GridTriangle} {p q : Fin 3}
    (ha : across n t p = some (u, q)) :
    corner u q = corner t (p + 1) ∧ corner u (q + 1) = corner t p := by
  rcases t with ⟨x, y, upper⟩
  cases upper <;> fin_cases p <;> simp [across] at ha
  · obtain ⟨hy, rfl, rfl⟩ := ha
    have he : y - 1 + 1 = y := by omega
    simp [corner, he]
  · obtain ⟨hx, rfl, rfl⟩ := ha
    simp [corner]
  · obtain ⟨rfl, rfl⟩ := ha
    simp [corner]
  · obtain ⟨rfl, rfl⟩ := ha
    simp [corner]
  · obtain ⟨hy, rfl, rfl⟩ := ha
    simp [corner]
  · obtain ⟨hx, rfl, rfl⟩ := ha
    have he : x - 1 + 1 = x := by omega
    simp [corner, he]

end GameTheory.Math.Sperner
