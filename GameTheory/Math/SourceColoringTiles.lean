import GameTheory.Math.GridWireColoringTile

/-! Four finite color tiles carry the standard boundary entrance into a shifted
routed graph. Their specified collars match the ordinary path tiles, and none
contains a trichromatic triangle. The corner and turn tiles replace the known
source's endpoint witness by an incoming boundary connection. -/

namespace GameTheory.Math.Sperner

/-- The corner tile's base-three row words are fixed local color data. -/
private def sourceCornerRows : List ℕ := [1092, 2181, 1656, 1659, 1656, 1683, 2139]

/-- Color a vertex of the corner source-boundary tile. -/
def sourceCornerTileColor (x y : ℕ) : Fin 3 :=
  ⟨(sourceCornerRows[y]?.getD 2186 / 3 ^ x) % 3, Nat.mod_lt _ (by decide)⟩

/-- The turn tile's base-three row words are fixed local color data. -/
private def sourceTurnRows : List ℕ := [2139, 1800, 828, 24, 1626, 1644, 2184]

/-- Color a vertex of the turn source-boundary tile. -/
def sourceTurnTileColor (x y : ℕ) : Fin 3 :=
  ⟨(sourceTurnRows[y]?.getD 2186 / 3 ^ x) % 3, Nat.mod_lt _ (by decide)⟩

/-- Bottom padding uses only the bottom boundary color and background. -/
def sourceBottomTileColor (_x y : ℕ) : Fin 3 := if y = 0 then 1 else 2

/-- Left padding uses only the left boundary color and background. -/
def sourceLeftTileColor (x _y : ℕ) : Fin 3 := if x = 0 then 0 else 2

/-- Bottom padding never uses color zero. -/
theorem sourceBottomTileColor_ne_zero (x y : ℕ) : sourceBottomTileColor x y ≠ 0 := by
  simp only [sourceBottomTileColor]
  split_ifs <;> decide

/-- Left padding never uses color one. -/
theorem sourceLeftTileColor_ne_one (x y : ℕ) : sourceLeftTileColor x y ≠ 1 := by
  simp only [sourceLeftTileColor]
  split_ifs <;> decide

/-- Standard bottom and left colors with an outgoing north port. -/
def sourceCornerBoundaryColor (d : Fin 4) (k : ℕ) : Fin 3 :=
  if d = 0 then if k = 0 ∨ k = 2 then 0 else if k = 3 then 1 else 2
  else if d = 1 then if k = 0 then 1 else 2
  else if d = 2 then if k = 0 then 0 else 1 else 0

/-- The northbound entrance turns east while preserving the left boundary. -/
def sourceTurnBoundaryColor (d : Fin 4) (k : ℕ) : Fin 3 :=
  if d = 0 then if k = 0 then 0 else 2
  else if d = 1 then if k = 2 then 1 else if k = 3 then 0 else 2
  else if d = 2 then if k = 0 ∨ k = 2 then 0 else if k = 3 then 1 else 2
  else 0

/-- Bottom padding carries color one below an inactive interior. -/
def sourceBottomBoundaryColor (d : Fin 4) (k : ℕ) : Fin 3 :=
  if d = 0 then 2 else if d = 2 then 1 else if k = 0 then 1 else 2

/-- Left padding carries color zero beside an inactive interior. -/
def sourceLeftBoundaryColor (d : Fin 4) (k : ℕ) : Fin 3 :=
  if d = 1 then 2 else if d = 3 then 0 else if k = 0 then 0 else 2

private theorem sourceCorner_boundary_certificate : ∀ d : Fin 4, ∀ k : Fin 7,
    (if d = 0 then sourceCornerTileColor k 6
          else if d = 1 then sourceCornerTileColor 6 k
          else if d = 2 then sourceCornerTileColor k 0 else sourceCornerTileColor 0 k) =
            sourceCornerBoundaryColor d k := by decide

/-- Every closed corner tile edge has exactly its specified collar. -/
theorem sourceCornerTileColor_boundary (d : Fin 4) {k : ℕ} (hk : k ≤ 6) :
    (if d = 0 then sourceCornerTileColor k 6
          else if d = 1 then sourceCornerTileColor 6 k
          else if d = 2 then sourceCornerTileColor k 0 else sourceCornerTileColor 0 k) =
            sourceCornerBoundaryColor d k :=
  sourceCorner_boundary_certificate d ⟨k, by omega⟩

private theorem sourceCorner_triangle_certificate : ∀ x y : Fin 6, ∀ upper : Bool,
    ¬Trichromatic (sourceCornerTileColor x y)
      (if upper then sourceCornerTileColor (x + 1) (y + 1) else sourceCornerTileColor (x + 1) y)
      (if upper then sourceCornerTileColor x (y + 1)
        else sourceCornerTileColor (x + 1) (y + 1)) := by decide

/-- The corner source-boundary tile introduces no trichromatic triangle. -/
theorem sourceCornerTileColor_not_trichromatic {x y : ℕ} (hx : x < 6) (hy : y < 6)
    (upper : Bool) :
    ¬Trichromatic (sourceCornerTileColor x y)
      (if upper then sourceCornerTileColor (x + 1) (y + 1) else sourceCornerTileColor (x + 1) y)
      (if upper then sourceCornerTileColor x (y + 1)
        else sourceCornerTileColor (x + 1) (y + 1)) :=
  sourceCorner_triangle_certificate ⟨x, hx⟩ ⟨y, hy⟩ upper

private theorem sourceTurn_boundary_certificate : ∀ d : Fin 4, ∀ k : Fin 7,
    (if d = 0 then sourceTurnTileColor k 6
          else if d = 1 then sourceTurnTileColor 6 k
          else if d = 2 then sourceTurnTileColor k 0 else sourceTurnTileColor 0 k) =
            sourceTurnBoundaryColor d k := by decide

/-- Every closed turn tile edge has exactly its specified collar. -/
theorem sourceTurnTileColor_boundary (d : Fin 4) {k : ℕ} (hk : k ≤ 6) :
    (if d = 0 then sourceTurnTileColor k 6
          else if d = 1 then sourceTurnTileColor 6 k
          else if d = 2 then sourceTurnTileColor k 0 else sourceTurnTileColor 0 k) =
            sourceTurnBoundaryColor d k :=
  sourceTurn_boundary_certificate d ⟨k, by omega⟩

private theorem sourceTurn_triangle_certificate : ∀ x y : Fin 6, ∀ upper : Bool,
    ¬Trichromatic (sourceTurnTileColor x y)
      (if upper then sourceTurnTileColor (x + 1) (y + 1) else sourceTurnTileColor (x + 1) y)
      (if upper then sourceTurnTileColor x (y + 1)
        else sourceTurnTileColor (x + 1) (y + 1)) := by decide

/-- The turn source-boundary tile introduces no trichromatic triangle. -/
theorem sourceTurnTileColor_not_trichromatic {x y : ℕ} (hx : x < 6) (hy : y < 6)
    (upper : Bool) :
    ¬Trichromatic (sourceTurnTileColor x y)
      (if upper then sourceTurnTileColor (x + 1) (y + 1) else sourceTurnTileColor (x + 1) y)
      (if upper then sourceTurnTileColor x (y + 1)
        else sourceTurnTileColor (x + 1) (y + 1)) :=
  sourceTurn_triangle_certificate ⟨x, hx⟩ ⟨y, hy⟩ upper

private theorem sourceBottom_boundary_certificate : ∀ d : Fin 4, ∀ k : Fin 7,
    (if d = 0 then sourceBottomTileColor k 6
          else if d = 1 then sourceBottomTileColor 6 k
          else if d = 2 then sourceBottomTileColor k 0 else sourceBottomTileColor 0 k) =
            sourceBottomBoundaryColor d k := by decide

/-- Every closed bottom tile edge has exactly its specified collar. -/
theorem sourceBottomTileColor_boundary (d : Fin 4) {k : ℕ} (hk : k ≤ 6) :
    (if d = 0 then sourceBottomTileColor k 6
          else if d = 1 then sourceBottomTileColor 6 k
          else if d = 2 then sourceBottomTileColor k 0 else sourceBottomTileColor 0 k) =
            sourceBottomBoundaryColor d k :=
  sourceBottom_boundary_certificate d ⟨k, by omega⟩

private theorem sourceBottom_triangle_certificate : ∀ x y : Fin 6, ∀ upper : Bool,
    ¬Trichromatic (sourceBottomTileColor x y)
      (if upper then sourceBottomTileColor (x + 1) (y + 1) else sourceBottomTileColor (x + 1) y)
      (if upper then sourceBottomTileColor x (y + 1)
        else sourceBottomTileColor (x + 1) (y + 1)) := by decide

/-- The bottom source-boundary tile introduces no trichromatic triangle. -/
theorem sourceBottomTileColor_not_trichromatic {x y : ℕ} (hx : x < 6) (hy : y < 6)
    (upper : Bool) :
    ¬Trichromatic (sourceBottomTileColor x y)
      (if upper then sourceBottomTileColor (x + 1) (y + 1) else sourceBottomTileColor (x + 1) y)
      (if upper then sourceBottomTileColor x (y + 1)
        else sourceBottomTileColor (x + 1) (y + 1)) :=
  sourceBottom_triangle_certificate ⟨x, hx⟩ ⟨y, hy⟩ upper

private theorem sourceLeft_boundary_certificate : ∀ d : Fin 4, ∀ k : Fin 7,
    (if d = 0 then sourceLeftTileColor k 6
          else if d = 1 then sourceLeftTileColor 6 k
          else if d = 2 then sourceLeftTileColor k 0 else sourceLeftTileColor 0 k) =
            sourceLeftBoundaryColor d k := by decide

/-- Every closed left tile edge has exactly its specified collar. -/
theorem sourceLeftTileColor_boundary (d : Fin 4) {k : ℕ} (hk : k ≤ 6) :
    (if d = 0 then sourceLeftTileColor k 6
          else if d = 1 then sourceLeftTileColor 6 k
          else if d = 2 then sourceLeftTileColor k 0 else sourceLeftTileColor 0 k) =
            sourceLeftBoundaryColor d k :=
  sourceLeft_boundary_certificate d ⟨k, by omega⟩

private theorem sourceLeft_triangle_certificate : ∀ x y : Fin 6, ∀ upper : Bool,
    ¬Trichromatic (sourceLeftTileColor x y)
      (if upper then sourceLeftTileColor (x + 1) (y + 1) else sourceLeftTileColor (x + 1) y)
      (if upper then sourceLeftTileColor x (y + 1)
        else sourceLeftTileColor (x + 1) (y + 1)) := by decide

/-- The left source-boundary tile introduces no trichromatic triangle. -/
theorem sourceLeftTileColor_not_trichromatic {x y : ℕ} (hx : x < 6) (hy : y < 6)
    (upper : Bool) :
    ¬Trichromatic (sourceLeftTileColor x y)
      (if upper then sourceLeftTileColor (x + 1) (y + 1) else sourceLeftTileColor (x + 1) y)
      (if upper then sourceLeftTileColor x (y + 1)
        else sourceLeftTileColor (x + 1) (y + 1)) :=
  sourceLeft_triangle_certificate ⟨x, hx⟩ ⟨y, hy⟩ upper

end GameTheory.Math.Sperner
