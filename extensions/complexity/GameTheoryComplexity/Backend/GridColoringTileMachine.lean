module

public import GameTheoryComplexity.Backend.GridRoutingArithmetic
public import GameTheoryComplexity.Backend.SpernerCornerMachine
public import GameTheory.Math.GridWireColoringTile
public import GameTheory.Math.SourceColoringTiles

@[expose] public section

/-! Constant-size tile lookup uses binary comparisons and finite selectors.
Runtime coordinates remain binary; lookup never recurses on their numeric value. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.Sperner

/-- Fixed-depth binary lookup compares complete numeric fields and retains a fallback. -/
def coloringTileLookupBits (table : ℕ → List Bool) (fallback : List Bool) :
    ℕ → List Bool → List Bool
  | 0, _ => fallback
  | n + 1, bits => select (routingEQFlag bits (lowBits 3 n))
      (table n) (coloringTileLookupBits table fallback n bits)

private theorem tileLookup_value (table : ℕ → List Bool) (fallback bits : List Bool)
    (n : ℕ) (hn : n ≤ 8) :
    coloringTileLookupBits table fallback n bits =
      if lsbValue bits < n then table (lsbValue bits) else fallback := by
  induction n with
  | zero => simp [coloringTileLookupBits]
  | succ n ih =>
    have hb : n < 2 ^ 3 := by norm_num; omega
    rw [coloringTileLookupBits, routingEQFlag_value, lsbValue_lowBits hb]
    by_cases he : lsbValue bits = n
    · simp [he, select]
    · rw [ih (by omega)]
      have hi : lsbValue bits < n + 1 ↔ lsbValue bits < n := by omega
      simp [he, select, hi]

@[fun_prop] theorem coloringTileLookupBits_polyTime
    {α : Type} {enc : α ↪ List Bool}
    (table : α → ℕ → List Bool) (fallback : α → List Bool) (n : ℕ)
    (ht : ∀ i, ComputableInPolyTime (fun z => table z i) enc encBits)
    (hf : ComputableInPolyTime fallback enc encBits)
    {bits : α → List Bool} (hb : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun z => coloringTileLookupBits (table z) (fallback z) n (bits z))
      enc encBits := by
  induction n with
  | zero => exact hf
  | succ n ih =>
      exact select_polyTime.comp ((routingEQFlag_polyTime hb (const (lowBits 3 n))).prod
        ((ht n).prod ih))

/-- Port codes zero through four represent absence, north, east, south and west. -/
def decodeColoringPort (bits : List Bool) : Option (Fin 4) :=
  match lsbValue bits with
  | 1 => some 0
  | 2 => some 1
  | 3 => some 2
  | 4 => some 3
  | _ => none

/-- The finite tile port associated with a small constant table index. -/
def coloringPortOfIndex : ℕ → Option (Fin 4)
  | 1 => some 0
  | 2 => some 1
  | 3 => some 2
  | 4 => some 3
  | _ => none

/-- A fixed seven-by-seven color table is queried by binary local coordinates. -/
def finiteColorTileBits (color : ℕ → ℕ → Fin 3) (x y : List Bool) : List Bool :=
  coloringTileLookupBits (fun i => coloringTileLookupBits (fun j => encodeGridColor (color i j))
    (encodeGridColor 2) 7 y) (encodeGridColor 2) 7 x

/-- A five-entry binary selector decodes canonical tile ports with an absent-port fallback. -/
def coloringTilePortBits (f : Option (Fin 4) → List Bool) (bits : List Bool) : List Bool :=
  coloringTileLookupBits (fun i => f (coloringPortOfIndex i)) (f none) 5 bits

/-- Evaluate a size-six tile with canonical color output and background outside its square. -/
def coloringTileBits (incoming outgoing x y : List Bool) : List Bool :=
  coloringTilePortBits (fun a => coloringTilePortBits (fun b => finiteColorTileBits (wireTileColor a b) x y)
    outgoing) incoming

private theorem tilePortLookup_value (f : Option (Fin 4) → List Bool) (bits : List Bool) :
    coloringTilePortBits f bits = f (decodeColoringPort bits) := by
  rw [coloringTilePortBits, tileLookup_value _ _ _ _ (by omega)]
  change (if lsbValue bits < 5 then f (coloringPortOfIndex (lsbValue bits))
    else f none) = f (coloringPortOfIndex (lsbValue bits))
  split_ifs with h
  · rfl
  · have hp : coloringPortOfIndex (lsbValue bits) = none := by
      unfold coloringPortOfIndex
      split <;> first | rfl | omega
    rw [hp]

/-- Lookup agrees with the exact finite tile on every bounded local coordinate word. -/
theorem coloringTileBits_value (incoming outgoing x y : List Bool)
    (hx : lsbValue x ≤ 6) (hy : lsbValue y ≤ 6) :
    coloringTileBits incoming outgoing x y = encodeGridColor
      (wireTileColor (decodeColoringPort incoming) (decodeColoringPort outgoing)
        (lsbValue x) (lsbValue y)) := by
  rw [coloringTileBits, tilePortLookup_value, tilePortLookup_value]
  simp only [finiteColorTileBits, tileLookup_value _ _ _ 7 (by omega),
    show lsbValue x < 7 by omega, show lsbValue y < 7 by omega, ↓reduceIte]

/-- A fixed color table charges arbitrary native coordinate producers. -/
@[fun_prop] theorem finiteColorTileBits_polyTime (color : ℕ → ℕ → Fin 3)
    {α : Type} {enc : α ↪ List Bool} {x y : α → List Bool}
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun z => finiteColorTileBits color (x z) (y z)) enc encBits := by
  have hrow (i : ℕ) := coloringTileLookupBits_polyTime
    (fun (_ : α) j => encodeGridColor (color i j))
    (fun _ => encodeGridColor 2) 7 (fun j => const (encodeGridColor (color i j)))
    (const (encodeGridColor 2)) (bits := y) hy
  exact coloringTileLookupBits_polyTime
    (fun z i => coloringTileLookupBits (fun j => encodeGridColor (color i j))
      (encodeGridColor 2) 7 (y z))
    (fun _ => encodeGridColor 2) 7 hrow (const (encodeGridColor 2)) (bits := x) hx

@[fun_prop] theorem coloringTilePortBits_polyTime
    {α : Type} {enc : α ↪ List Bool}
    (f : α → Option (Fin 4) → List Bool)
    (hf : ∀ a, ComputableInPolyTime (fun z => f z a) enc encBits)
    {bits : α → List Bool} (hb : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun z => coloringTilePortBits (f z) (bits z)) enc encBits :=
  coloringTileLookupBits_polyTime _ _ 5 (fun i => hf (coloringPortOfIndex i)) (hf none) hb

/-- Tile evaluation charges the native port and coordinate word producers. -/
@[fun_prop] theorem coloringTileBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {incoming outgoing x y : α → List Bool}
    (hi : ComputableInPolyTime incoming enc encBits)
    (ho : ComputableInPolyTime outgoing enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun z => coloringTileBits (incoming z) (outgoing z) (x z) (y z))
      enc encBits := by
  apply coloringTilePortBits_polyTime _ _ hi
  intro a
  exact coloringTilePortBits_polyTime _
    (fun b => finiteColorTileBits_polyTime (wireTileColor a b) hx hy) ho

/-- On every word, finite lookup returns a canonical color and treats overflow as background. -/
theorem finiteColorTileBits_value (color : ℕ → ℕ → Fin 3) (x y : List Bool) :
    finiteColorTileBits color x y = encodeGridColor
      (if lsbValue x < 7 ∧ lsbValue y < 7 then
        color (lsbValue x) (lsbValue y) else 2) := by
  simp only [finiteColorTileBits, tileLookup_value _ _ _ 7 (by omega)]
  split_ifs <;> simp_all

/-- Finite color lookup always emits two flags. -/
@[simp] theorem finiteColorTileBits_length (color : ℕ → ℕ → Fin 3) (x y : List Bool) :
    (finiteColorTileBits color x y).length = 2 := by
  rw [finiteColorTileBits_value]
  rfl

/-- Ordinary tile lookup always emits two flags, including on malformed port words. -/
@[simp] theorem coloringTileBits_length (incoming outgoing x y : List Bool) :
    (coloringTileBits incoming outgoing x y).length = 2 := by
  rw [coloringTileBits, tilePortLookup_value, tilePortLookup_value]
  exact finiteColorTileBits_length _ _ _

/-- The four source collars are selected by a fixed finite tile kind. -/
def sourceColoringTileBits (kind : Fin 4) (x y : List Bool) : List Bool :=
  finiteColorTileBits
    (if kind = 0 then sourceCornerTileColor else if kind = 1 then sourceTurnTileColor
      else if kind = 2 then sourceBottomTileColor else sourceLeftTileColor) x y

/-- Source collars have native polynomial-time machines for each fixed finite kind. -/
@[fun_prop] theorem sourceColoringTileBits_polyTime (kind : Fin 4)
    {α : Type} {enc : α ↪ List Bool} {x y : α → List Bool}
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun z => sourceColoringTileBits kind (x z) (y z)) enc encBits :=
  finiteColorTileBits_polyTime _ hx hy

/-- Source collars agree exactly with their finite color tables on bounded local coordinates. -/
theorem sourceColoringTileBits_value (kind : Fin 4) (x y : List Bool)
    (hx : lsbValue x ≤ 6) (hy : lsbValue y ≤ 6) :
    sourceColoringTileBits kind x y = encodeGridColor
      ((if kind = 0 then sourceCornerTileColor else if kind = 1 then sourceTurnTileColor
        else if kind = 2 then sourceBottomTileColor else sourceLeftTileColor)
          (lsbValue x) (lsbValue y)) := by
  rw [sourceColoringTileBits, finiteColorTileBits_value]
  simp only [show lsbValue x < 7 by omega, show lsbValue y < 7 by omega,
    and_self, ite_true]

end GameTheory.Complexity.Backend
