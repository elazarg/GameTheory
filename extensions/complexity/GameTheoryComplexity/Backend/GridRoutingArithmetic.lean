module

public import GameTheoryComplexity.Backend.BinaryCertificateArithmetic
public import GameTheoryComplexity.Backend.WordOperations
public import Complexity.Foundations.Data.BitString.Binary

@[expose] public section

/-! Binary routing arithmetic reuses the exact adder and unsigned comparator.
The constant factors three and six use shifts and addition, with no numeric loops. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime WordOperations Cslib.BitString

/-- Add two little-endian words, retaining the full carry. -/
def routingAddBits (x y : List Bool) : List Bool := binaryCertificateAdd ![x, y]

/-- Compare arbitrary little-endian words as unsigned natural numbers. -/
def routingLEFlag (x y : List Bool) : List Bool := binaryCertificateLE ![x, y]

/-- Strict unsigned comparison is the negation of the reversed non-strict comparison. -/
def routingLTFlag (x y : List Bool) : List Bool := notFlag (routingLEFlag y x)

/-- Numeric equality permits unequal word widths and arbitrary high zero padding. -/
def routingEQFlag (x y : List Bool) : List Bool :=
  andFlag (routingLEFlag x y) (routingLEFlag y x)

/-- Multiply a binary word by three using one shift and one addition. -/
def routingTripleBits (bits : List Bool) : List Bool := routingAddBits bits (false :: bits)

/-- Multiply a binary word by six by shifting its triple once. -/
def routingSixBits (bits : List Bool) : List Bool := false :: routingTripleBits bits

/-- Addition reserves one more output bit than its longer operand. -/
@[simp] theorem routingAddBits_length (x y : List Bool) :
    (routingAddBits x y).length = max x.length y.length + 1 :=
  binaryCertificateAdd_length x y

/-- Addition has exact natural-number semantics, including on padded inputs. -/
theorem routingAddBits_value (x y : List Bool) :
    lsbValue (routingAddBits x y) = lsbValue x + lsbValue y := by
  simpa only [routingAddBits, lsbValue_eq_foldr_bit, ofBits] using binaryCertificateAdd_value x y

/-- Non-strict comparison always emits one Boolean flag. -/
@[simp] theorem routingLEFlag_length (x y : List Bool) : (routingLEFlag x y).length = 1 :=
  binaryCertificateLE_length x y

/-- Non-strict comparison accepts exactly the unsigned order relation. -/
theorem routingLEFlag_value (x y : List Bool) :
    routingLEFlag x y = [decide (lsbValue x ≤ lsbValue y)] := by
  by_cases h : ofBits x ≤ ofBits y
  · have hl : lsbValue x ≤ lsbValue y := by
      simpa only [lsbValue_eq_foldr_bit, ofBits] using h
    simp [routingLEFlag, binaryCertificateLE, h, hl]
  · have hl : ¬lsbValue x ≤ lsbValue y := by
      simpa only [lsbValue_eq_foldr_bit, ofBits] using h
    simp [routingLEFlag, binaryCertificateLE, h, hl]

/-- Strict comparison accepts exactly strict unsigned order. -/
theorem routingLTFlag_value (x y : List Bool) :
    routingLTFlag x y = [decide (lsbValue x < lsbValue y)] := by
  by_cases h : lsbValue y ≤ lsbValue x
  · have hn : ¬ lsbValue x < lsbValue y := by omega
    simp [routingLTFlag, routingLEFlag_value, h, hn, notFlag]
  · have hl : lsbValue x < lsbValue y := by omega
    simp [routingLTFlag, routingLEFlag_value, h, hl, notFlag]

/-- Numeric equality accepts exactly equal decoded values, independently of padding. -/
theorem routingEQFlag_value (x y : List Bool) :
    routingEQFlag x y = [decide (lsbValue x = lsbValue y)] := by
  by_cases he : lsbValue x = lsbValue y
  · simp [routingEQFlag, routingLEFlag_value, he, andFlag]
  · by_cases hxy : lsbValue x ≤ lsbValue y
    · have hyx : ¬ lsbValue y ≤ lsbValue x := by omega
      simp [routingEQFlag, routingLEFlag_value, hxy, hyx, he, andFlag]
    · simp [routingEQFlag, routingLEFlag_value, hxy, he, andFlag]

/-- Numeric equality always emits one Boolean flag. -/
@[simp] theorem routingEQFlag_length (x y : List Bool) : (routingEQFlag x y).length = 1 := by
  rw [routingEQFlag_value]
  rfl

/-- Strict comparison always emits one Boolean flag. -/
@[simp] theorem routingLTFlag_length (x y : List Bool) : (routingLTFlag x y).length = 1 := by
  rw [routingLTFlag_value]
  rfl

/-- Tripling reserves two extra bits for the shifted operand and the carry. -/
@[simp] theorem routingTripleBits_length (bits : List Bool) :
    (routingTripleBits bits).length = bits.length + 2 := by
  simp [routingTripleBits]

/-- Tripling decodes to exact multiplication by three. -/
theorem routingTripleBits_value (bits : List Bool) :
    lsbValue (routingTripleBits bits) = 3 * lsbValue bits := by
  rw [routingTripleBits, routingAddBits_value]
  simp only [lsbValue, Bool.toNat_false]
  omega

/-- Multiplication by six reserves three extra bits. -/
@[simp] theorem routingSixBits_length (bits : List Bool) :
    (routingSixBits bits).length = bits.length + 3 := by simp [routingSixBits]

/-- Multiplication by six has exact natural-number semantics. -/
theorem routingSixBits_value (bits : List Bool) :
    lsbValue (routingSixBits bits) = 6 * lsbValue bits := by
  simp only [routingSixBits, lsbValue, Bool.toNat_false, routingTripleBits_value]
  omega

private theorem wordPair_polyTime {α : Type} {enc : α ↪ List Bool} {x y : α → List Bool}
    (hx : ComputableInPolyTime x enc encBits) (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun a => ![x a, y a]) enc (encPi encBits) := by
  apply ComputableInPolyTime.pi
  intro i
  fin_cases i
  · exact hx
  · exact hy

/-- Addition charges both word producers and its padded full-carry result. -/
@[fun_prop] theorem routingAddBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {x y : α → List Bool}
    (hx : ComputableInPolyTime x enc encBits) (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun a => routingAddBits (x a) (y a)) enc encBits :=
  binaryCertificateAdd_polyTime.comp (wordPair_polyTime hx hy)

/-- Unsigned comparison charges both word producers. -/
@[fun_prop] theorem routingLEFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {x y : α → List Bool}
    (hx : ComputableInPolyTime x enc encBits) (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun a => routingLEFlag (x a) (y a)) enc encBits :=
  binaryCertificateLE_polyTime.comp (wordPair_polyTime hx hy)

@[fun_prop] theorem routingLTFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {x y : α → List Bool}
    (hx : ComputableInPolyTime x enc encBits) (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun a => routingLTFlag (x a) (y a)) enc encBits :=
  notFlag_polyTime.comp (routingLEFlag_polyTime hy hx)

@[fun_prop] theorem routingEQFlag_polyTime
    {α : Type} {enc : α ↪ List Bool} {x y : α → List Bool}
    (hx : ComputableInPolyTime x enc encBits) (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun a => routingEQFlag (x a) (y a)) enc encBits :=
  andFlag_polyTime.comp ((routingLEFlag_polyTime hx hy).prod (routingLEFlag_polyTime hy hx))

@[fun_prop] theorem routingTripleBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {bits : α → List Bool}
    (hb : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun a => routingTripleBits (bits a)) enc encBits :=
  routingAddBits_polyTime hb (bitsCons (const false) hb)

@[fun_prop] theorem routingSixBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {bits : α → List Bool}
    (hb : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun a => routingSixBits (bits a)) enc encBits :=
  bitsCons (const false) (routingTripleBits_polyTime hb)

end GameTheory.Complexity.Backend
