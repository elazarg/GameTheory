import GameTheory.Math.GridWireColoringTile

/-! Compatible finite color tiles glue to a coloring of the natural square grid.
Tile boundaries agree across seams, including corners, so every triangle is
classified by its unique local square and its macrovertex's port status. -/

namespace GameTheory.Math.Sperner

/-- Color a grid point using its size-six macrocell and its local remainder coordinates. -/
def wireGridColor (incoming outgoing : ℕ → ℕ → Option (Fin 4)) (x y : ℕ) : Fin 3 :=
  wireTileColor (incoming (x / 6) (y / 6)) (outgoing (x / 6) (y / 6)) (x % 6) (y % 6)

private theorem div_mod_tile (i x : ℕ) (hx : x < 6) :
    (6 * i + x) / 6 = i ∧ (6 * i + x) % 6 = x := by omega

/-- Compatible seam colors make the global coloring agree on every closed tile. -/
theorem wireGridColor_local_agreement (incoming outgoing : ℕ → ℕ → Option (Fin 4))
    (hvalid : ∀ i j, ValidTilePorts (incoming i j) (outgoing i j))
    (heast : ∀ i j k, k ≤ 6 →
      wireTilePortColor (incoming i j) (outgoing i j) 1 k =
        wireTilePortColor (incoming (i + 1) j) (outgoing (i + 1) j) 3 k)
    (hnorth : ∀ i j k, k ≤ 6 →
      wireTilePortColor (incoming i j) (outgoing i j) 0 k =
        wireTilePortColor (incoming i (j + 1)) (outgoing i (j + 1)) 2 k)
    (i j x y : ℕ) (hx : x ≤ 6) (hy : y ≤ 6) :
    wireGridColor incoming outgoing (6 * i + x) (6 * j + y) =
      wireTileColor (incoming i j) (outgoing i j) x y := by
  by_cases hxe : x = 6 <;> by_cases hye : y = 6
  · subst x; subst y
    have hxi := div_mod_tile (i + 1) 0 (by omega)
    have hyj := div_mod_tile (j + 1) 0 (by omega)
    have h6i : 6 * i + 6 = 6 * (i + 1) + 0 := by omega
    have h6j : 6 * j + 6 = 6 * (j + 1) + 0 := by omega
    rw [wireGridColor, h6i, h6j, hxi.1, hxi.2, hyj.1, hyj.2]
    have hnew := wireTileColor_boundary _ _ (hvalid (i + 1) (j + 1)) 2
      (k := 0) (by omega)
    have hold := wireTileColor_boundary _ _ (hvalid i j) 0 (k := 6) (by omega)
    simpa [wireTileBoundary, wireTilePortColor] using hnew.trans hold.symm
  · subst x
    have hxi := div_mod_tile (i + 1) 0 (by omega)
    have hyj := div_mod_tile j y (by omega)
    have h6i : 6 * i + 6 = 6 * (i + 1) + 0 := by omega
    rw [wireGridColor, h6i, hxi.1, hxi.2, hyj.1, hyj.2]
    have hnew := wireTileColor_boundary _ _ (hvalid (i + 1) j) 3 hy
    have hold := wireTileColor_boundary _ _ (hvalid i j) 1 hy
    simpa [wireTileBoundary] using hnew.trans ((heast i j y hy).symm.trans hold.symm)
  · subst y
    have hxi := div_mod_tile i x (by omega)
    have hyj := div_mod_tile (j + 1) 0 (by omega)
    have h6j : 6 * j + 6 = 6 * (j + 1) + 0 := by omega
    rw [wireGridColor, h6j, hxi.1, hxi.2, hyj.1, hyj.2]
    have hnew := wireTileColor_boundary _ _ (hvalid i (j + 1)) 2 hx
    have hold := wireTileColor_boundary _ _ (hvalid i j) 0 hx
    simpa [wireTileBoundary] using hnew.trans ((hnorth i j x hx).symm.trans hold.symm)
  · have hxi := div_mod_tile i x (by omega)
    have hyj := div_mod_tile j y (by omega)
    simp only [wireGridColor, hxi.1, hxi.2, hyj.1, hyj.2]

section CompatibleTiles

variable (incoming outgoing : ℕ → ℕ → Option (Fin 4))
  (hvalid : ∀ i j, ValidTilePorts (incoming i j) (outgoing i j))
  (heast : ∀ i j k, k ≤ 6 →
    wireTilePortColor (incoming i j) (outgoing i j) 1 k =
      wireTilePortColor (incoming (i + 1) j) (outgoing (i + 1) j) 3 k)
  (hnorth : ∀ i j k, k ≤ 6 →
    wireTilePortColor (incoming i j) (outgoing i j) 0 k =
      wireTilePortColor (incoming i (j + 1)) (outgoing i (j + 1)) 2 k)

include hvalid heast hnorth

/-- A translated tile has a trichromatic triangle precisely at its endpoint witness. -/
theorem wireGridColor_tile_trichromatic_iff (i j : ℕ) {x y : ℕ}
    (hx : x < 6) (hy : y < 6) (upper : Bool) :
    Trichromatic (wireGridColor incoming outgoing (6 * i + x) (6 * j + y))
      (if upper then wireGridColor incoming outgoing (6 * i + x + 1) (6 * j + y + 1)
        else wireGridColor incoming outgoing (6 * i + x + 1) (6 * j + y))
      (if upper then wireGridColor incoming outgoing (6 * i + x) (6 * j + y + 1)
        else wireGridColor incoming outgoing (6 * i + x + 1) (6 * j + y + 1)) ↔
      TileEndpoint (incoming i j) (outgoing i j) ∧ x = 2 ∧ y = 2 ∧ upper = false := by
  have h00 := wireGridColor_local_agreement incoming outgoing hvalid heast hnorth
    i j x y (by omega) (by omega)
  have h10 := wireGridColor_local_agreement incoming outgoing hvalid heast hnorth
    i j (x + 1) y (by omega) (by omega)
  have h01 := wireGridColor_local_agreement incoming outgoing hvalid heast hnorth
    i j x (y + 1) (by omega) (by omega)
  have h11 := wireGridColor_local_agreement incoming outgoing hvalid heast hnorth
    i j (x + 1) (y + 1) (by omega) (by omega)
  simp only [← Nat.add_assoc] at h10 h01 h11
  rw [h00, h10, h01, h11]
  exact wireTileColor_trichromatic_iff _ _ (hvalid i j) hx hy upper

/-- Every global trichromatic triangle is the fixed witness of an endpoint macrovertex. -/
theorem wireGridColor_trichromatic_iff (x y : ℕ) (upper : Bool) :
    Trichromatic (wireGridColor incoming outgoing x y)
      (if upper then wireGridColor incoming outgoing (x + 1) (y + 1)
        else wireGridColor incoming outgoing (x + 1) y)
      (if upper then wireGridColor incoming outgoing x (y + 1)
        else wireGridColor incoming outgoing (x + 1) (y + 1)) ↔
      TileEndpoint (incoming (x / 6) (y / 6)) (outgoing (x / 6) (y / 6)) ∧
        x % 6 = 2 ∧ y % 6 = 2 ∧ upper = false := by
  have hx : x % 6 < 6 := Nat.mod_lt x (by omega)
  have hy : y % 6 < 6 := Nat.mod_lt y (by omega)
  have h := wireGridColor_tile_trichromatic_iff incoming outgoing hvalid heast hnorth
    (x / 6) (y / 6) hx hy upper
  have hxe : 6 * (x / 6) + x % 6 = x := by omega
  have hye : 6 * (y / 6) + y % 6 = y := by omega
  simpa only [hxe, hye] using h

/-- Canonical grid-triangle corners satisfy the same exhaustive endpoint classification. -/
theorem wireGridColor_corner_trichromatic_iff (t : GridTriangle) :
    Trichromatic
      (wireGridColor incoming outgoing (corner t 0).1 (corner t 0).2)
      (wireGridColor incoming outgoing (corner t 1).1 (corner t 1).2)
      (wireGridColor incoming outgoing (corner t 2).1 (corner t 2).2) ↔
      TileEndpoint (incoming (t.x / 6) (t.y / 6)) (outgoing (t.x / 6) (t.y / 6)) ∧
        t.x % 6 = 2 ∧ t.y % 6 = 2 ∧ t.upper = false := by
  cases hupper : t.upper
  · simpa [corner, hupper] using
      wireGridColor_trichromatic_iff incoming outgoing hvalid heast hnorth t.x t.y false
  · simpa [corner, hupper] using
      wireGridColor_trichromatic_iff incoming outgoing hvalid heast hnorth t.x t.y true

end CompatibleTiles

end GameTheory.Math.Sperner
