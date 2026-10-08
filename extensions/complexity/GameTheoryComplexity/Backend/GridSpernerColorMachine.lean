import GameTheoryComplexity.Backend.GridColoringPortMachine
import GameTheoryComplexity.Backend.SpernerRoutingDecoderMachine
import GameTheory.Math.GridSpernerRouting

/-! Binary coordinate queries select a local color tile after division by six.
Source collars replace the known endpoint, while seeded pointer queries compute
the remaining ordinary tile ports in polynomial time. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.Sperner GameTheory.Math.GridWire

@[simp] private theorem coloring_nil_value : Nat.fromBitsLE [] = 0 := rfl
@[simp] private theorem coloring_one_value : Nat.fromBitsLE [true] = 1 := rfl

private def coloringModSixBits (bits : List Bool) : List Bool :=
  bitAt [] bits ++ routingModThreeBits bits.tail

private theorem coloringModSixBits_value (bits : List Bool) :
    Nat.fromBitsLE (coloringModSixBits bits) = Nat.fromBitsLE bits % 6 := by
  cases bits with
  | nil => rfl
  | cons bit bits =>
    cases bit <;>
      simp [coloringModSixBits, bitAt_eq, bitOf,
        routingModThreeBits_value, Nat.fromBitsLE_cons] <;> omega

private theorem coloringModSixBitsFn_mem_FP {bits : List Bool → List Bool} (hb : bits ∈ FP) :
    (fun z => coloringModSixBits (bits z)) ∈ FP := by
  have hh : (fun z => bitAt [] (bits z)) ∈ FP :=
    CobhamFP_subset_FP (headFlagFn (FP_subset_CobhamFP hb))
  have ht : (fun z => (bits z).tail) ∈ FP :=
    CobhamFP_subset_FP (Cobham.tailFn (FP_subset_CobhamFP hb))
  exact appendFn_mem_FP hh (mem_FP_comp (f := fun z => (bits z).tail)
    (g := routingModThreeBits) ht routingModThreeBits_mem_FP)

private def coloringMixedTileBits (ruler : List Bool) (P S : List Bool → List Bool)
    (i j x y : List Bool) : List Bool :=
  let ordinary := coloringTileBits
    (coloringRoutedPortBits ruler P S true (gridPredBits i) (gridPredBits j))
    (coloringRoutedPortBits ruler P S false (gridPredBits i) (gridPredBits j)) x y
  let origin := coloringTileBits (encodeColoringPort (some 3))
    (encodeColoringPort (some 1)) x y
  caseBit₀ (routingEQFlag i [])
    (caseBit₀ (routingEQFlag j []) (sourceColoringTileBits 0 x y)
      (caseBit₀ (routingEQFlag j [true]) (sourceColoringTileBits 1 x y)
        (sourceColoringTileBits 3 x y)))
    (caseBit₀ (routingEQFlag j []) (sourceColoringTileBits 2 x y)
      (caseBit₀ (andBit (routingEQFlag i [true]) (routingEQFlag j [true])) origin ordinary))

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
  by_cases hi0 : Nat.fromBitsLE i = 0 <;> by_cases hj0 : Nat.fromBitsLE j = 0 <;>
    by_cases hi1 : Nat.fromBitsLE i = 1 <;> by_cases hj1 : Nat.fromBitsLE j = 1 <;>
    simp [coloringMixedTileBits, routingEQFlag_value, hi0, hj0, hi1, hj1,
      andBit, caseBit₀, sourceColoringTileBits]

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
    (i j x y : List Bool) (hx : Nat.fromBitsLE x ≤ 6) (hy : Nat.fromBitsLE y ≤ 6) :
    coloringMixedTileBits ruler P S i j x y = encodeGridColor
      (gridSpernerRoutingTileColor (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
        (Nat.fromBitsLE i) (Nat.fromBitsLE j) (Nat.fromBitsLE x) (Nat.fromBitsLE y)) := by
  have hsource (kind : Fin 4) := sourceColoringTileBits_value kind x y hx hy
  have horigin := coloringTileBits_value (encodeColoringPort (some 3))
    (encodeColoringPort (some 1)) x y hx hy
  simp only [decodeColoringPort_encode] at horigin
  by_cases hi0 : Nat.fromBitsLE i = 0
  · by_cases hj0 : Nat.fromBitsLE j = 0 <;> by_cases hj1 : Nat.fromBitsLE j = 1 <;>
      simp [coloringMixedTileBits, routingEQFlag_value, hi0, hj0, hj1, caseBit₀,
        gridSpernerRoutingTileColor, hsource]
  · by_cases hj0 : Nat.fromBitsLE j = 0
    · simp [coloringMixedTileBits, routingEQFlag_value, hi0, hj0, caseBit₀,
        gridSpernerRoutingTileColor, hsource]
    · have hord := coloringTileBits_value
        (coloringRoutedPortBits ruler P S true (gridPredBits i) (gridPredBits j))
        (coloringRoutedPortBits ruler P S false (gridPredBits i) (gridPredBits j)) x y hx hy
      conv at hord => rhs; rw [coloringRoutedPortBits_value, coloringRoutedPortBits_value,
        decodeColoringPort_encode, decodeColoringPort_encode,
        gridPredBits_value_of_pos i (by omega), gridPredBits_value_of_pos j (by omega)]
      simp only [Bool.false_eq_true, ↓reduceIte] at hord
      by_cases hi1 : Nat.fromBitsLE i = 1 <;> by_cases hj1 : Nat.fromBitsLE j = 1 <;>
        simp [coloringMixedTileBits, routingEQFlag_value, hi0, hj0, hi1, hj1, caseBit₀,
          andBit, gridSpernerRoutingTileColor, horigin, hord]

/-- Every binary coordinate word gives the exact unbounded routing interior color. -/
theorem routingSpernerInteriorBits_value (ruler : List Bool) (P S : List Bool → List Bool)
    (x y : List Bool) : routingSpernerInteriorBits ruler P S x y = encodeGridColor
      (gridSpernerRoutingInterior (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S)
        (Nat.fromBitsLE x) (Nat.fromBitsLE y)) := by
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
        (Nat.fromBitsLE (word.take ((routingSpernerRuler ruler).length + 1)))
        (Nat.fromBitsLE (word.drop ((routingSpernerRuler ruler).length + 1)))) :=
  routingSpernerInteriorBits_value _ _ _ _ _

/-- Encoded coordinates within the extended capacity retain their exact interior color. -/
theorem routingSpernerColorQuery_encode (ruler : List Bool) (P S : List Bool → List Bool)
    {x y : ℕ} (hx : x < 2 ^ ((routingSpernerRuler ruler).length + 1))
    (hy : y < 2 ^ ((routingSpernerRuler ruler).length + 1)) :
    routingSpernerColorQuery ruler P S
      (Nat.toBitsLE ((routingSpernerRuler ruler).length + 1) x ++
        Nat.toBitsLE ((routingSpernerRuler ruler).length + 1) y) = encodeGridColor
      (gridSpernerRoutingInterior (2 ^ ruler.length)
        (routingOriginalPointer ruler P) (routingOriginalPointer ruler S) x y) := by
  rw [routingSpernerColorQuery_value]
  simp [-routingSpernerRuler_length, Nat.fromBitsLE_toBitsLE hx, Nat.fromBitsLE_toBitsLE hy]

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

private theorem coloringMixedTileBitsUniformFn_mem_FP
    (P S : List Bool → List Bool → List Bool)
    {ruler seed i j x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hi : i ∈ FP) (hj : j ∈ FP)
    (hx : x ∈ FP) (hy : y ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => coloringMixedTileBits (ruler z) (P (seed z)) (S (seed z))
      (i z) (j z) (x z) (y z)) ∈ FP := by
  have hip : (fun z => gridPredBits (i z)) ∈ FP := mem_FP_comp hi gridPredBits_mem_FP
  have hjp : (fun z => gridPredBits (j z)) ∈ FP := mem_FP_comp hj gridPredBits_mem_FP
  have hpred := coloringRoutedPortBitsUniformFn_mem_FP true P S hr hs hip hjp hP hS
  have hsucc := coloringRoutedPortBitsUniformFn_mem_FP false P S hr hs hip hjp hP hS
  have hord := coloringTileBitsFn_mem_FP hpred hsucc hx hy
  have horigin := coloringTileBitsFn_mem_FP
    (constFn_mem_FP (encodeColoringPort (some 3)))
    (constFn_mem_FP (encodeColoringPort (some 1))) hx hy
  have hi0 := routingEQFlagFn_mem_FP hi (constFn_mem_FP [])
  have hj0 := routingEQFlagFn_mem_FP hj (constFn_mem_FP [])
  have hi1 := routingEQFlagFn_mem_FP hi (constFn_mem_FP [true])
  have hj1 := routingEQFlagFn_mem_FP hj (constFn_mem_FP [true])
  have h11 : (fun z => andBit (routingEQFlag (i z) [true])
      (routingEQFlag (j z) [true])) ∈ FP :=
    CobhamFP_subset_FP (Cobham.andFn (FP_subset_CobhamFP hi1) (FP_subset_CobhamFP hj1))
  exact selectFn_mem_FP hi0
    (selectFn_mem_FP hj0 (sourceColoringTileBitsFn_mem_FP 0 hx hy)
      (selectFn_mem_FP hj1 (sourceColoringTileBitsFn_mem_FP 1 hx hy)
        (sourceColoringTileBitsFn_mem_FP 3 hx hy)))
    (selectFn_mem_FP hj0 (sourceColoringTileBitsFn_mem_FP 2 hx hy)
      (selectFn_mem_FP h11 horigin hord))

/-- The binary interior query is uniformly polynomial time in coordinate and pointer seeds. -/
theorem routingSpernerInteriorBitsUniformFn_mem_FP
    (P S : List Bool → List Bool → List Bool) {ruler seed x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingSpernerInteriorBits (ruler z) (P (seed z)) (S (seed z))
      (x z) (y z)) ∈ FP :=
  coloringMixedTileBitsUniformFn_mem_FP P S hr hs
    (mem_FP_comp (f := x) (g := routingDivSixBits) hx routingDivSixBits_mem_FP)
    (mem_FP_comp (f := y) (g := routingDivSixBits) hy routingDivSixBits_mem_FP)
    (coloringModSixBitsFn_mem_FP hx) (coloringModSixBitsFn_mem_FP hy) hP hS

/-- Serialized color queries retain a uniform polynomial-time certificate for varying seeds. -/
theorem routingSpernerColorQueryUniformFn_mem_FP
    (P S : List Bool → List Bool → List Bool) {ruler seed word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hs : seed ∈ FP) (hw : word ∈ FP)
    (hP : (fun z => P (pairFst z) (pairSnd z)) ∈ FP)
    (hS : (fun z => S (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => routingSpernerColorQuery (ruler z) (P (seed z)) (S (seed z)) (word z)) ∈ FP := by
  have hwidth : (fun z => routingSpernerRuler (ruler z) ++ [false]) ∈ FP :=
    appendFn_mem_FP (routingSpernerRulerFn_mem_FP hr) (constFn_mem_FP [false])
  have hx : (fun z => (word z).take ((routingSpernerRuler (ruler z)).length + 1)) ∈ FP := by
    have h := Cobham.takeFn (FP_subset_CobhamFP hwidth) (FP_subset_CobhamFP hw)
    exact CobhamFP_subset_FP (h.of_eq fun v => by simp)
  have hy : (fun z => (word z).drop ((routingSpernerRuler (ruler z)).length + 1)) ∈ FP := by
    have h := Cobham.dropFn (FP_subset_CobhamFP hwidth) (FP_subset_CobhamFP hw)
    exact CobhamFP_subset_FP (h.of_eq fun v => by simp)
  exact routingSpernerInteriorBitsUniformFn_mem_FP P S hr hs hx hy hP hS

end GameTheory.Complexity.Backend
