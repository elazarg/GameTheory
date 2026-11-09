module

public import GameTheoryComplexity.Backend.GridColoringPortMachine
public import GameTheoryComplexity.Backend.SpernerRoutingDecoderMachine
public import GameTheory.Math.GridSpernerRouting

@[expose] public section

/-! Binary coordinate queries select a local color tile after division by six.
Source collars replace the known endpoint, while seeded pointer queries compute
the remaining ordinary tile ports in polynomial time. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString WordOperations
open GameTheory.Math.Sperner GameTheory.Math.GridWire

@[simp] private theorem coloring_nil_value : lsbValue [] = 0 := rfl
@[simp] private theorem coloring_one_value : lsbValue [true] = 1 := rfl

/-- Retain the low bit and divide its tail to compute a three-bit residue modulo six. -/
def coloringModSixBits (bits : List Bool) : List Bool :=
  [bits.headD false] ++ routingModThreeBits bits.tail

private theorem coloringModSixBits_value (bits : List Bool) :
    lsbValue (coloringModSixBits bits) = lsbValue bits % 6 := by
  cases bits with
  | nil => rfl
  | cons bit bits =>
    cases bit <;>
      simp [coloringModSixBits, routingModThreeBits_value, lsbValue] <;> omega

@[fun_prop] theorem coloringModSixBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {bits : α → List Bool}
    (hb : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun z => coloringModSixBits (bits z)) enc encBits := by
  have hhead : ComputableInPolyTime (fun word : List Bool => word.headD false)
      encBits encBool := .headD false
  exact bitsAppend (bitsCons (hhead.comp hb) (const []))
    (routingModThreeBits_polyTime (bitsTail.comp hb))

/-- Select the finite source collar or ordinary routed tile at raw binary tile indices. -/
def coloringMixedTileBits (ruler : List Bool) (P S : List Bool → List Bool)
    (i j x y : List Bool) : List Bool :=
  let ordinary := coloringTileBits
    (coloringRoutedPortBits ruler P S true (gridPredBits i) (gridPredBits j))
    (coloringRoutedPortBits ruler P S false (gridPredBits i) (gridPredBits j)) x y
  let origin := coloringTileBits (encodeColoringPort (some 3))
    (encodeColoringPort (some 1)) x y
  select (routingEQFlag i [])
    (select (routingEQFlag j []) (sourceColoringTileBits 0 x y)
      (select (routingEQFlag j [true]) (sourceColoringTileBits 1 x y)
        (sourceColoringTileBits 3 x y)))
    (select (routingEQFlag j []) (sourceColoringTileBits 2 x y)
      (select (andFlag (routingEQFlag i [true]) (routingEQFlag j [true])) origin ordinary))

/-- An unbounded interior color query evaluates the exact local source or routing tile. -/
def routingSpernerInteriorBits (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : List Bool :=
  coloringMixedTileBits ruler P S (routingDivSixBits x) (routingDivSixBits y)
    (coloringModSixBits x) (coloringModSixBits y)

/-- Serialized color queries use the extended coordinate blocks of the target Sperner grid. -/
def routingSpernerColorQuery (ruler : List Bool) (P S : List Bool → List Bool)
    (word : List Bool) : List Bool :=
  let width := (routingSpernerRuler ruler).length + 1
  routingSpernerInteriorBits ruler P S (word.take width) (word.drop width)

private theorem coloringMixedTileBits_length (ruler : List Bool) (P S : List Bool → List Bool)
    (i j x y : List Bool) : (coloringMixedTileBits ruler P S i j x y).length = 2 := by
  by_cases hi0 : lsbValue i = 0 <;> by_cases hj0 : lsbValue j = 0 <;>
    by_cases hi1 : lsbValue i = 1 <;> by_cases hj1 : lsbValue j = 1 <;>
    simp [coloringMixedTileBits, routingEQFlag_value, hi0, hj0, hi1, hj1,
      andFlag, select, sourceColoringTileBits]

/-- Every interior query returns exactly two canonical color flags. -/
@[simp] theorem routingSpernerInteriorBits_length (ruler : List Bool)
    (P S : List Bool → List Bool) (x y : List Bool) :
    (routingSpernerInteriorBits ruler P S x y).length = 2 :=
  coloringMixedTileBits_length _ _ _ _ _ _ _

/-- Serialized color queries always emit the two color flags expected by Sperner. -/
@[simp] theorem routingSpernerColorQuery_length (ruler : List Bool)
    (P S : List Bool → List Bool) (word : List Bool) :
    (routingSpernerColorQuery ruler P S word).length = 2 :=
  routingSpernerInteriorBits_length _ _ _ _ _

private theorem coloringMixedTileBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (i j x y : List Bool) (hx : lsbValue x ≤ 6) (hy : lsbValue y ≤ 6) :
    coloringMixedTileBits ruler P S i j x y = encodeGridColor
      (gridSpernerRoutingTileColor (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
        (lsbValue i) (lsbValue j) (lsbValue x) (lsbValue y)) := by
  have hsource (kind : Fin 4) := sourceColoringTileBits_value kind x y hx hy
  have horigin := coloringTileBits_value (encodeColoringPort (some 3))
    (encodeColoringPort (some 1)) x y hx hy
  simp only [decodeColoringPort_encode] at horigin
  by_cases hi0 : lsbValue i = 0
  · by_cases hj0 : lsbValue j = 0 <;> by_cases hj1 : lsbValue j = 1 <;>
      simp [coloringMixedTileBits, routingEQFlag_value, hi0, hj0, hj1, select,
        gridSpernerRoutingTileColor, hsource]
  · by_cases hj0 : lsbValue j = 0
    · simp [coloringMixedTileBits, routingEQFlag_value, hi0, hj0, select,
        gridSpernerRoutingTileColor, hsource]
    · have hord := coloringTileBits_value
        (coloringRoutedPortBits ruler P S true (gridPredBits i) (gridPredBits j))
        (coloringRoutedPortBits ruler P S false (gridPredBits i) (gridPredBits j)) x y hx hy
      conv at hord => rhs; rw [coloringRoutedPortBits_value, coloringRoutedPortBits_value,
        decodeColoringPort_encode, decodeColoringPort_encode,
        gridPredBits_value_of_pos i (by omega), gridPredBits_value_of_pos j (by omega)]
      simp only [Bool.false_eq_true, ↓reduceIte] at hord
      by_cases hi1 : lsbValue i = 1 <;> by_cases hj1 : lsbValue j = 1 <;>
        simp [coloringMixedTileBits, routingEQFlag_value, hi0, hj0, hi1, hj1, select,
          andFlag, gridSpernerRoutingTileColor, horigin, hord]

/-- Every binary coordinate word gives the exact unbounded routing interior color. -/
theorem routingSpernerInteriorBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : routingSpernerInteriorBits ruler P S x y = encodeGridColor
      (gridSpernerRoutingInterior (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
        (lsbValue x) (lsbValue y)) := by
  rw [routingSpernerInteriorBits, coloringMixedTileBits_value]
  · rw [routingDivSixBits_value, routingDivSixBits_value,
      coloringModSixBits_value, coloringModSixBits_value]
    rfl
  · rw [coloringModSixBits_value]; omega
  · rw [coloringModSixBits_value]; omega

/-- Every serialized query has exact semantics on its parsed extended coordinate fields. -/
theorem routingSpernerColorQuery_value (ruler : List Bool) (P S : List Bool → List Bool)
    (word : List Bool) : routingSpernerColorQuery ruler P S word = encodeGridColor
      (gridSpernerRoutingInterior (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
        (lsbValue (word.take ((routingSpernerRuler ruler).length + 1)))
        (lsbValue (word.drop ((routingSpernerRuler ruler).length + 1)))) :=
  routingSpernerInteriorBits_value _ _ _ _ _

/-- Encoded coordinates within the extended capacity retain their exact interior color. -/
theorem routingSpernerColorQuery_encode (ruler : List Bool) (P S : List Bool → List Bool)
    {x y : ℕ} (hx : x < 2 ^ ((routingSpernerRuler ruler).length + 1))
    (hy : y < 2 ^ ((routingSpernerRuler ruler).length + 1)) :
    routingSpernerColorQuery ruler P S
      (lowBits ((routingSpernerRuler ruler).length + 1) x ++
        lowBits ((routingSpernerRuler ruler).length + 1) y) = encodeGridColor
      (gridSpernerRoutingInterior (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S) x y) := by
  rw [routingSpernerColorQuery_value]
  simp [-routingSpernerRuler_length, lsbValue_lowBits hx, lsbValue_lowBits hy]

/-- The standard interior-query interface agrees throughout the finite routing square. -/
theorem gridInteriorColor_routingSpernerColorQuery (ruler : List Bool)
    (P S : List Bool → List Bool) {x y : ℕ}
    (hx : x ≤ 2 ^ (routingSpernerRuler ruler).length)
    (hy : y ≤ 2 ^ (routingSpernerRuler ruler).length) :
    gridInteriorColor (routingSpernerRuler ruler).length
      (routingSpernerColorQuery ruler P S) x y =
      gridSpernerRoutingInterior (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S) x y := by
  have hp := Nat.two_pow_pos (routingSpernerRuler ruler).length
  have hxx : x < 2 ^ ((routingSpernerRuler ruler).length + 1) := by rw [pow_succ]; omega
  have hyy : y < 2 ^ ((routingSpernerRuler ruler).length + 1) := by rw [pow_succ]; omega
  rw [gridInteriorColor, routingSpernerColorQuery_encode ruler P S hxx hyy,
    decodeGridColor_encode]

/-- Canonical boundary correction agrees exactly with the mathematical finite coloring. -/
theorem routingSpernerColorQuery_color (ruler : List Bool) (P S : List Bool → List Bool)
    {x y : ℕ} (hx : x ≤ 2 ^ (routingSpernerRuler ruler).length)
    (hy : y ≤ 2 ^ (routingSpernerRuler ruler).length) :
    standardGridColor (2 ^ (routingSpernerRuler ruler).length)
      (gridInteriorColor (routingSpernerRuler ruler).length
        (routingSpernerColorQuery ruler P S)) x y =
      gridSpernerRoutingColor (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
        (2 ^ (routingSpernerRuler ruler).length) x y := by
  have h := gridInteriorColor_routingSpernerColorQuery ruler P S hx hy
  simp only [gridSpernerRoutingColor, standardGridColor, h]

/-- Mixed-tile selection charges native seeded ports and finite table lookup. -/
@[fun_prop] theorem coloringMixedTileBitsUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed i j x y : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hi : ComputableInPolyTime i enc encBits)
    (hj : ComputableInPolyTime j enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => coloringMixedTileBits (ruler z) (P (seed z)) (S (seed z)) (i z) (j z) (x z) (y z)) enc encBits := by
  have hip := gridPredBits_polyTime.comp hi
  have hjp := gridPredBits_polyTime.comp hj
  have hpred := coloringRoutedPortBitsUniform_polyTime true P S hruler hseed hip hjp hP hS
  have hsucc := coloringRoutedPortBitsUniform_polyTime false P S hruler hseed hip hjp hP hS
  have hord := coloringTileBits_polyTime hpred hsucc hx hy
  have horigin := coloringTileBits_polyTime (const (encodeColoringPort (some 3)))
    (const (encodeColoringPort (some 1))) hx hy
  have hi0 := routingEQFlag_polyTime hi (const [])
  have hj0 := routingEQFlag_polyTime hj (const [])
  have hi1 := routingEQFlag_polyTime hi (const [true])
  have hj1 := routingEQFlag_polyTime hj (const [true])
  have h11 := andFlag_polyTime.comp (hi1.prod hj1)
  have hleft := select_polyTime.comp (hj0.prod ((sourceColoringTileBits_polyTime 0 hx hy).prod
    (select_polyTime.comp (hj1.prod ((sourceColoringTileBits_polyTime 1 hx hy).prod
      (sourceColoringTileBits_polyTime 3 hx hy))))))
  have hright := select_polyTime.comp (hj0.prod ((sourceColoringTileBits_polyTime 2 hx hy).prod
    (select_polyTime.comp (h11.prod (horigin.prod hord)))))
  exact select_polyTime.comp (hi0.prod (hleft.prod hright))

/-- Interior color queries charge binary division, local residues and native seeded tile ports. -/
@[fun_prop] theorem routingSpernerInteriorBitsUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed x y : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingSpernerInteriorBits (ruler z) (P (seed z)) (S (seed z)) (x z) (y z)) enc encBits := by
  exact coloringMixedTileBitsUniform_polyTime P S hruler hseed
    (routingDivSixBits_polyTime hx) (routingDivSixBits_polyTime hy)
    (coloringModSixBits_polyTime hx) (coloringModSixBits_polyTime hy) hP hS

/-- Serialized color queries charge the exact unary field width and all native seeded arithmetic. -/
@[fun_prop] theorem routingSpernerColorQueryUniform_polyTime
    (P S : List Bool → List Bool → List Bool)
    {α : Type} {enc : α ↪ List Bool} {ruler seed word : α → List Bool}
    (hruler : ComputableInPolyTime ruler enc encBits)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hword : ComputableInPolyTime word enc encBits)
    (hP : ComputableInPolyTime (fun p : List Bool × List Bool => P p.1 p.2)
      (encPair encBits encBits) encBits)
    (hS : ComputableInPolyTime (fun p : List Bool × List Bool => S p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun z => routingSpernerColorQuery (ruler z) (P (seed z)) (S (seed z)) (word z)) enc encBits := by
  have hwidth : ComputableInPolyTime
      (fun z => (routingSpernerRuler (ruler z)).length + 1) enc encUnary := by
    simpa only [Function.comp_def, List.length_append, List.length_singleton] using
      length_bits.comp (bitsAppend (routingSpernerRuler_polyTime hruler) (const [false]))
  exact routingSpernerInteriorBitsUniform_polyTime P S hruler hseed
    (bitsTakeWithInput hword hwidth) (bitsDropWithInput hword hwidth) hP hS

end GameTheory.Complexity.Backend
