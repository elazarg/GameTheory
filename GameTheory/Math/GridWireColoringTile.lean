import GameTheory.Math.SpernerGridGeometry
import GameTheory.Math.SpernerTriangle
import Mathlib.Data.Fintype.Option

/-! Constant-size color tiles thicken directed grid paths. Incoming and outgoing
ports carry opposite zero/one transitions; all other boundary points have color
two. A balanced tile has no trichromatic triangle, while an endpoint tile has
exactly one at a fixed location. -/

namespace GameTheory.Math.Sperner

/-- Distinct active ports, or the completely inactive configuration. Directions
are north, east, south and west, numbered zero through three. -/
def ValidTilePorts (incoming outgoing : Option (Fin 4)) : Prop :=
  incoming ≠ outgoing ∨ incoming = none

instance (incoming outgoing : Option (Fin 4)) :
    Decidable (ValidTilePorts incoming outgoing) :=
  inferInstanceAs (Decidable (incoming ≠ outgoing ∨ incoming = none))

/-- Exactly one active port marks an endpoint. -/
def TileEndpoint (incoming outgoing : Option (Fin 4)) : Prop :=
  (incoming = none ∧ outgoing ≠ none) ∨ (incoming ≠ none ∧ outgoing = none)

instance (incoming outgoing : Option (Fin 4)) : Decidable (TileEndpoint incoming outgoing) :=
  inferInstanceAs (Decidable
    ((incoming = none ∧ outgoing ≠ none) ∨ (incoming ≠ none ∧ outgoing = none)))

private def tilePortIndex (p : Option (Fin 4)) : ℕ := (p.map (fun d => d.val + 1)).getD 0

/-- Seven base-three row words describe a six-by-six tile. The tables are fixed
constants; their complete boundary and triangle specifications are proved below. -/
private def tileRows (incoming outgoing : Option (Fin 4)) : List ℕ :=
  match tilePortIndex incoming, tilePortIndex outgoing with
  | 0, 0 => [2186, 2186, 2186, 2186, 2186, 2186, 2186]
  | 0, 1 => [2186, 2066, 1715, 1781, 1703, 1811, 2141]
  | 0, 2 => [2186, 1904, 1070, 68, 1670, 1673, 2186]
  | 0, 3 => [2123, 1472, 1634, 1697, 1673, 1670, 2186]
  | 0, 4 => [2186, 2162, 1629, 1684, 1652, 1661, 2186]
  | 1, 0 => [2186, 2147, 1652, 1679, 1634, 1637, 2123]
  | 1, 2 => [2186, 1904, 1085, 5, 1634, 2111, 2123]
  | 1, 3 => [2123, 2120, 1625, 1625, 1637, 1634, 2123]
  | 1, 4 => [2186, 2108, 1629, 1624, 1634, 1634, 2123]
  | 2, 0 => [2186, 2108, 35, 1115, 1859, 1823, 2186]
  | 2, 1 => [2186, 2162, 11, 983, 1820, 2090, 2141]
  | 2, 3 => [2123, 2120, 50, 1022, 1835, 2066, 2186]
  | 2, 4 => [2186, 2108, 36, 985, 1796, 2075, 2186]
  | 3, 0 => [2141, 2135, 1655, 1676, 1646, 1640, 2186]
  | 3, 1 => [2141, 2135, 1649, 1658, 1649, 1658, 2141]
  | 3, 2 => [2141, 1802, 818, 62, 1676, 1682, 2186]
  | 3, 4 => [2141, 2135, 1656, 1651, 1652, 1664, 2186]
  | 4, 0 => [2186, 2147, 1651, 1674, 1646, 1628, 2186]
  | 4, 1 => [2186, 2150, 1660, 1647, 1658, 1685, 2141]
  | 4, 2 => [2186, 2066, 1003, 0, 1493, 1481, 2186]
  | 4, 3 => [2123, 2120, 1633, 1620, 1646, 1640, 2186]
  | _, _ => [2186, 2186, 2186, 2186, 2186, 2186, 2186]

/-- Read the base-three color digit at a tile vertex. -/
def wireTileColor (incoming outgoing : Option (Fin 4)) (x y : ℕ) : Fin 3 :=
  ⟨((tileRows incoming outgoing)[y]?.getD 2186 / 3 ^ x) % 3, Nat.mod_lt _ (by decide)⟩

/-- Read the north, east, south or west edge in increasing coordinate order. -/
def wireTileBoundary (incoming outgoing : Option (Fin 4)) (d : Fin 4) (k : ℕ) : Fin 3 :=
  if d = 0 then wireTileColor incoming outgoing k 6
  else if d = 1 then wireTileColor incoming outgoing 6 k
  else if d = 2 then wireTileColor incoming outgoing k 0
  else wireTileColor incoming outgoing 0 k

/-- The first color of an outgoing port in increasing coordinate order. -/
def wireTileOutwardFirst (d : Fin 4) : Fin 3 := if d = 0 ∨ d = 3 then 0 else 1

/-- Boundary ports use positions two and three; their colors reverse on an
incoming edge. The remaining boundary is background color two. -/
def wireTilePortColor (incoming outgoing : Option (Fin 4)) (d : Fin 4) (k : ℕ) : Fin 3 :=
  let first := wireTileOutwardFirst d
  let second : Fin 3 := if first = 0 then 1 else 0
  if k = 2 then
    if incoming = some d then second else if outgoing = some d then first else 2
  else if k = 3 then
    if incoming = some d then first else if outgoing = some d then second else 2
  else 2

private theorem boundary_certificate :
    ∀ incoming outgoing : Option (Fin 4), ∀ d : Fin 4, ∀ k : Fin 7,
      ValidTilePorts incoming outgoing →
        wireTileBoundary incoming outgoing d k = wireTilePortColor incoming outgoing d k := by
  decide

/-- Every closed tile edge has exactly its specified port colors. -/
theorem wireTileColor_boundary (incoming outgoing : Option (Fin 4))
    (ha : ValidTilePorts incoming outgoing) (d : Fin 4) {k : ℕ} (hk : k ≤ 6) :
    wireTileBoundary incoming outgoing d k = wireTilePortColor incoming outgoing d k :=
  boundary_certificate incoming outgoing d ⟨k, by omega⟩ ha

private theorem triangle_certificate :
    ∀ incoming outgoing : Option (Fin 4), ∀ x y : Fin 6, ∀ upper : Bool,
      ValidTilePorts incoming outgoing →
        (Trichromatic (wireTileColor incoming outgoing x y)
          (if upper then wireTileColor incoming outgoing (x + 1) (y + 1)
            else wireTileColor incoming outgoing (x + 1) y)
          (if upper then wireTileColor incoming outgoing x (y + 1)
            else wireTileColor incoming outgoing (x + 1) (y + 1)) ↔
          TileEndpoint incoming outgoing ∧ x.val = 2 ∧ y.val = 2 ∧ upper = false) := by
  decide

/-- An endpoint tile has one trichromatic triangle; balanced and inactive tiles
have none. The same fixed lower triangle witnesses every endpoint direction. -/
theorem wireTileColor_trichromatic_iff (incoming outgoing : Option (Fin 4))
    (ha : ValidTilePorts incoming outgoing) {x y : ℕ} (hx : x < 6) (hy : y < 6)
    (upper : Bool) :
    Trichromatic (wireTileColor incoming outgoing x y)
      (if upper then wireTileColor incoming outgoing (x + 1) (y + 1)
        else wireTileColor incoming outgoing (x + 1) y)
      (if upper then wireTileColor incoming outgoing x (y + 1)
        else wireTileColor incoming outgoing (x + 1) (y + 1)) ↔
      TileEndpoint incoming outgoing ∧ x = 2 ∧ y = 2 ∧ upper = false :=
  triangle_certificate incoming outgoing ⟨x, hx⟩ ⟨y, hy⟩ upper ha

end GameTheory.Math.Sperner
