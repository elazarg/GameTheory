import GameTheoryComplexity.Backend.GridRoutingArithmetic
import GameTheoryComplexity.Backend.SpernerCornerMachine
import GameTheory.Math.GridWireColoringTile
import GameTheory.Math.SourceColoringTiles

/-! Constant-size tile lookup uses binary comparisons and finite selectors.
Runtime coordinates remain binary; lookup never recurses on their numeric value. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.Sperner

private def tileLookup (table : ℕ → List Bool) (fallback : List Bool) :
    ℕ → List Bool → List Bool
  | 0, _ => fallback
  | n + 1, bits => caseBit₀ (routingEQFlag bits (Nat.toBitsLE 3 n))
      (table n) (tileLookup table fallback n bits)

private theorem tileLookup_value (table : ℕ → List Bool) (fallback bits : List Bool)
    (n : ℕ) (hn : n ≤ 8) :
    tileLookup table fallback n bits =
      if Nat.fromBitsLE bits < n then table (Nat.fromBitsLE bits) else fallback := by
  induction n with
  | zero => simp [tileLookup]
  | succ n ih =>
    have hb : n < 2 ^ 3 := by norm_num; omega
    rw [tileLookup, routingEQFlag_value, Nat.fromBitsLE_toBitsLE hb]
    by_cases he : Nat.fromBitsLE bits = n
    · simp [he, caseBit₀]
    · rw [ih (by omega)]
      have hi : Nat.fromBitsLE bits < n + 1 ↔ Nat.fromBitsLE bits < n := by omega
      simp [he, caseBit₀, hi]

private theorem tileLookupFn_mem_FP (table : List Bool → ℕ → List Bool)
    (fallback : List Bool → List Bool) (n : ℕ)
    (ht : ∀ i, (fun z => table z i) ∈ FP) (hf : fallback ∈ FP)
    {bits : List Bool → List Bool} (hb : bits ∈ FP) :
    (fun z => tileLookup (table z) (fallback z) n (bits z)) ∈ FP := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact selectFn_mem_FP
      (routingEQFlagFn_mem_FP hb (constFn_mem_FP (Nat.toBitsLE 3 n)))
      (ht n) ih

/-- Port codes zero through four represent absence, north, east, south and west. -/
def decodeColoringPort (bits : List Bool) : Option (Fin 4) :=
  match Nat.fromBitsLE bits with
  | 1 => some 0
  | 2 => some 1
  | 3 => some 2
  | 4 => some 3
  | _ => none

private def portOfIndex : ℕ → Option (Fin 4)
  | 1 => some 0
  | 2 => some 1
  | 3 => some 2
  | 4 => some 3
  | _ => none

/-- A fixed seven-by-seven color table is queried by binary local coordinates. -/
def finiteColorTileBits (color : ℕ → ℕ → Fin 3) (x y : List Bool) : List Bool :=
  tileLookup (fun i => tileLookup (fun j => encodeGridColor (color i j))
    (encodeGridColor 2) 7 y) (encodeGridColor 2) 7 x

private def tilePortLookup (f : Option (Fin 4) → List Bool) (bits : List Bool) : List Bool :=
  tileLookup (fun i => f (portOfIndex i)) (f none) 5 bits

/-- Evaluate a size-six tile with canonical color output and background outside its square. -/
def coloringTileBits (incoming outgoing x y : List Bool) : List Bool :=
  tilePortLookup (fun a => tilePortLookup (fun b => finiteColorTileBits (wireTileColor a b) x y)
    outgoing) incoming

private theorem tilePortLookup_value (f : Option (Fin 4) → List Bool) (bits : List Bool) :
    tilePortLookup f bits = f (decodeColoringPort bits) := by
  rw [tilePortLookup, tileLookup_value _ _ _ _ (by omega)]
  change (if Nat.fromBitsLE bits < 5 then f (portOfIndex (Nat.fromBitsLE bits))
    else f none) = f (portOfIndex (Nat.fromBitsLE bits))
  split_ifs with h
  · rfl
  · have hp : portOfIndex (Nat.fromBitsLE bits) = none := by
      unfold portOfIndex
      split <;> first | rfl | omega
    rw [hp]

/-- Lookup agrees with the exact finite tile on every bounded local coordinate word. -/
theorem coloringTileBits_value (incoming outgoing x y : List Bool)
    (hx : Nat.fromBitsLE x ≤ 6) (hy : Nat.fromBitsLE y ≤ 6) :
    coloringTileBits incoming outgoing x y = encodeGridColor
      (wireTileColor (decodeColoringPort incoming) (decodeColoringPort outgoing)
        (Nat.fromBitsLE x) (Nat.fromBitsLE y)) := by
  rw [coloringTileBits, tilePortLookup_value, tilePortLookup_value]
  simp only [finiteColorTileBits, tileLookup_value _ _ _ 7 (by omega),
    show Nat.fromBitsLE x < 7 by omega, show Nat.fromBitsLE y < 7 by omega, ↓reduceIte]

/-- A fixed color table evaluates in polynomial time on arbitrary coordinate producers. -/
theorem finiteColorTileBitsFn_mem_FP (color : ℕ → ℕ → Fin 3)
    {x y : List Bool → List Bool} (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => finiteColorTileBits color (x z) (y z)) ∈ FP := by
  have hrow (i : ℕ) := tileLookupFn_mem_FP
    (fun (_ : List Bool) j => encodeGridColor (color i j))
    (fun _ => encodeGridColor 2) 7
    (fun j => constFn_mem_FP (encodeGridColor (color i j)))
    (constFn_mem_FP (encodeGridColor 2)) (bits := y) hy
  exact tileLookupFn_mem_FP
    (fun z i => tileLookup (fun j => encodeGridColor (color i j))
      (encodeGridColor 2) 7 (y z))
    (fun _ => encodeGridColor 2) 7 hrow (constFn_mem_FP (encodeGridColor 2))
    (bits := x) hx

private theorem tilePortLookupFn_mem_FP (f : List Bool → Option (Fin 4) → List Bool)
    (hf : ∀ a, (fun z => f z a) ∈ FP) {bits : List Bool → List Bool} (hb : bits ∈ FP) :
    (fun z => tilePortLookup (f z) (bits z)) ∈ FP :=
  tileLookupFn_mem_FP _ _ 5 (fun i => hf (portOfIndex i)) (hf none) hb

/-- Tile lookup composes polynomial-time port and coordinate word producers. -/
theorem coloringTileBitsFn_mem_FP {incoming outgoing x y : List Bool → List Bool}
    (hi : incoming ∈ FP) (ho : outgoing ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => coloringTileBits (incoming z) (outgoing z) (x z) (y z)) ∈ FP := by
  apply tilePortLookupFn_mem_FP _ _ hi
  intro a
  exact tilePortLookupFn_mem_FP _
    (fun b => finiteColorTileBitsFn_mem_FP (wireTileColor a b) hx hy) ho

/-- On every word, finite lookup returns a canonical color and treats overflow as background. -/
theorem finiteColorTileBits_value (color : ℕ → ℕ → Fin 3) (x y : List Bool) :
    finiteColorTileBits color x y = encodeGridColor
      (if Nat.fromBitsLE x < 7 ∧ Nat.fromBitsLE y < 7 then
        color (Nat.fromBitsLE x) (Nat.fromBitsLE y) else 2) := by
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

/-- Source collar lookup has an actual polynomial-time certificate for each fixed kind. -/
theorem sourceColoringTileBitsFn_mem_FP (kind : Fin 4)
    {x y : List Bool → List Bool} (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => sourceColoringTileBits kind (x z) (y z)) ∈ FP :=
  finiteColorTileBitsFn_mem_FP _ hx hy

/-- Source collars agree exactly with their finite color tables on bounded local coordinates. -/
theorem sourceColoringTileBits_value (kind : Fin 4) (x y : List Bool)
    (hx : Nat.fromBitsLE x ≤ 6) (hy : Nat.fromBitsLE y ≤ 6) :
    sourceColoringTileBits kind x y = encodeGridColor
      ((if kind = 0 then sourceCornerTileColor else if kind = 1 then sourceTurnTileColor
        else if kind = 2 then sourceBottomTileColor else sourceLeftTileColor)
          (Nat.fromBitsLE x) (Nat.fromBitsLE y)) := by
  rw [sourceColoringTileBits, finiteColorTileBits_value]
  simp only [show Nat.fromBitsLE x < 7 by omega, show Nat.fromBitsLE y < 7 by omega,
    and_self, ite_true]

end GameTheory.Complexity.Backend
