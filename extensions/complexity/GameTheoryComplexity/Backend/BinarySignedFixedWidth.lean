module

public import GameTheoryComplexity.Backend.BinarySignedAddition

@[expose] public section

/-! Fixed-width signed arithmetic with a length ruler.

Every result is stored in exactly the ruler's width. Values fitting the
magnitude capacity are preserved; larger magnitudes are truncated explicitly.
-/

namespace GameTheory.Complexity.Backend

open Cslib.BitString Turing.MultiTapeTM

private theorem ofBits_head_add_tail (x : List Bool) :
    ofBits x = (x.headD false).toNat + 2 * ofBits x.tail := by
  cases x with
  | nil => rfl
  | cons b t =>
    simp only [ofBits, List.foldr_cons, Nat.bit_val, List.headD_cons, List.tail_cons]
    omega

private theorem ofBits_mod_two (x : List Bool) :
    ofBits x % 2 = (x.headD false).toNat := by
  rw [ofBits_head_add_tail]
  have hb : (x.headD false).toNat ≤ 1 := by cases x.headD false <;> decide
  omega

/-- Normalize a signed word to exactly the ruler's width, truncating high bits. -/
def binarySignedFixed (ruler x : List Bool) : List Bool :=
  lowBits ruler.length (ofBits x)

@[simp] theorem binarySignedFixed_length (ruler x : List Bool) :
    (binarySignedFixed ruler x).length = ruler.length := by
  simp [binarySignedFixed]

/-- Normalizing an already sized field preserves its bytes, including negative zero. -/
theorem binarySignedFixed_eq_of_length (ruler x : List Bool) (hx : x.length = ruler.length) :
    binarySignedFixed ruler x = x := by
  rw [binarySignedFixed, ← hx, ofBits, ← Cslib.BitString.lsbValue_eq_foldr_bit]
  exact Cslib.BitString.lowBits_lsbValue x

theorem binarySignedValue_natAbs (x : List Bool) :
    (binarySignedValue x).natAbs = ofBits x.tail := by
  unfold binarySignedValue
  split <;> simp

/-- The stored word preserves every representable signed value. -/
theorem binarySignedFixed_value (ruler x : List Bool) (hr : 0 < ruler.length)
    (hx : (binarySignedValue x).natAbs < 2 ^ (ruler.length - 1)) :
    binarySignedValue (binarySignedFixed ruler x) = binarySignedValue x := by
  have hmag : ofBits x.tail < 2 ^ (ruler.length - 1) := by
    simpa only [binarySignedValue_natAbs] using hx
  have hwidth : ruler.length = ruler.length - 1 + 1 := by omega
  have hfit : ofBits x < 2 ^ ruler.length := by
    rw [hwidth, Nat.pow_succ, ofBits_head_add_tail]
    have hb : (x.headD false).toNat ≤ 1 := by cases x.headD false <;> decide
    omega
  have hvalue : ofBits (binarySignedFixed ruler x) = ofBits x := by
    exact Nat.foldr_bit_testBit (Nat.size_le.mpr hfit)
  have hheadNat : ((binarySignedFixed ruler x).headD false).toNat =
      (x.headD false).toNat := by
    have hm := congrArg (fun n => n % 2) hvalue
    simpa only [ofBits_mod_two] using hm
  have hhead : (binarySignedFixed ruler x).headD false = x.headD false := by
    cases b : (binarySignedFixed ruler x).headD false <;>
      cases c : x.headD false <;>
      simp only [b, c, Bool.toNat_false, Bool.toNat_true] at hheadNat ⊢ <;> omega
  have htail : ofBits (binarySignedFixed ruler x).tail = ofBits x.tail := by
    rw [ofBits_head_add_tail (binarySignedFixed ruler x), ofBits_head_add_tail x, hhead] at hvalue
    omega
  unfold binarySignedValue
  rw [hhead, htail]

/-- Fixed-width storage preserves zero, including when its ruler is empty. -/
theorem binarySignedFixed_value_zero (ruler x : List Bool)
    (hx : binarySignedValue x = 0) :
    binarySignedValue (binarySignedFixed ruler x) = 0 := by
  cases ruler with
  | nil => rfl
  | cons b ruler =>
    have hmag : (binarySignedValue x).natAbs < 2 ^ ((b :: ruler).length - 1) := by
      rw [hx]
      simp
    rw [binarySignedFixed_value (b :: ruler) x (by simp) hmag, hx]

/-- Every fixed-width word has a magnitude below its signed capacity. -/
theorem binarySignedFixed_natAbs_lt (ruler x : List Bool) :
    (binarySignedValue (binarySignedFixed ruler x)).natAbs < 2 ^ (ruler.length - 1) := by
  rw [binarySignedValue_natAbs]
  have hlen := binarySignedFixed_length ruler x
  have htail : (binarySignedFixed ruler x).tail.length = ruler.length - 1 := by
    simp only [List.length_tail, hlen]
  simpa only [ofBits, htail] using Nat.foldr_bit_lt (binarySignedFixed ruler x).tail

/-- Add and normalize immediately to prevent accumulation of padding. -/
def binarySignedFixedAdd (ruler x y : List Bool) : List Bool :=
  binarySignedFixed ruler (binarySignedAdd x y)

/-- Subtract and normalize immediately to the supplied field width. -/
def binarySignedFixedSub (ruler x y : List Bool) : List Bool :=
  binarySignedFixed ruler (binarySignedSub x y)

/-- Multiply and normalize immediately to the supplied field width. -/
def binarySignedFixedMul (ruler x y : List Bool) : List Bool :=
  binarySignedFixed ruler (binarySignedMul x y)

@[simp] theorem binarySignedFixedAdd_length (ruler x y : List Bool) :
    (binarySignedFixedAdd ruler x y).length = ruler.length := binarySignedFixed_length _ _

@[simp] theorem binarySignedFixedSub_length (ruler x y : List Bool) :
    (binarySignedFixedSub ruler x y).length = ruler.length := binarySignedFixed_length _ _

@[simp] theorem binarySignedFixedMul_length (ruler x y : List Bool) :
    (binarySignedFixedMul ruler x y).length = ruler.length := binarySignedFixed_length _ _

theorem binarySignedFixedAdd_value (ruler x y : List Bool) (hr : 0 < ruler.length)
    (h : (binarySignedValue x + binarySignedValue y).natAbs < 2 ^ (ruler.length - 1)) :
    binarySignedValue (binarySignedFixedAdd ruler x y) = binarySignedValue x + binarySignedValue y := by
  have hh : (binarySignedValue (binarySignedAdd x y)).natAbs < 2 ^ (ruler.length - 1) := by
    rwa [binarySignedAdd_value]
  exact (binarySignedFixed_value ruler _ hr hh).trans (binarySignedAdd_value x y)

theorem binarySignedFixedSub_value (ruler x y : List Bool) (hr : 0 < ruler.length)
    (h : (binarySignedValue x - binarySignedValue y).natAbs < 2 ^ (ruler.length - 1)) :
    binarySignedValue (binarySignedFixedSub ruler x y) = binarySignedValue x - binarySignedValue y := by
  have hh : (binarySignedValue (binarySignedSub x y)).natAbs < 2 ^ (ruler.length - 1) := by
    rwa [binarySignedSub_value]
  exact (binarySignedFixed_value ruler _ hr hh).trans (binarySignedSub_value x y)

theorem binarySignedFixedMul_value (ruler x y : List Bool) (hr : 0 < ruler.length)
    (h : (binarySignedValue x * binarySignedValue y).natAbs < 2 ^ (ruler.length - 1)) :
    binarySignedValue (binarySignedFixedMul ruler x y) = binarySignedValue x * binarySignedValue y := by
  have hh : (binarySignedValue (binarySignedMul x y)).natAbs < 2 ^ (ruler.length - 1) := by
    rwa [binarySignedMul_value]
  exact (binarySignedFixed_value ruler _ hr hh).trans (binarySignedMul_value x y)

@[fun_prop] theorem binarySignedFixed_polyTime {Input : Type} {input : Input ↪ List Bool}
    {ruler x : Input → List Bool}
    (hruler : ComputableInPolyTime ruler input encBits)
    (hx : ComputableInPolyTime x input encBits) :
    ComputableInPolyTime (fun a => binarySignedFixed (ruler a) (x a)) input encBits := by
  have hwidth := ComputableInPolyTime.length_bits_comp hruler
  have hvalue := ComputableInPolyTime.bitsToNat.comp hx
  exact ComputableInPolyTime.bitsLow hwidth hvalue

@[fun_prop] theorem binarySignedFixedAdd_polyTime {Input : Type} {input : Input ↪ List Bool}
    {ruler x y : Input → List Bool}
    (hr : ComputableInPolyTime ruler input encBits)
    (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => binarySignedFixedAdd (ruler a) (x a) (y a)) input encBits :=
  binarySignedFixed_polyTime hr (binarySignedAdd_polyTime hx hy)

@[fun_prop] theorem binarySignedFixedSub_polyTime {Input : Type} {input : Input ↪ List Bool}
    {ruler x y : Input → List Bool}
    (hr : ComputableInPolyTime ruler input encBits)
    (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => binarySignedFixedSub (ruler a) (x a) (y a)) input encBits :=
  binarySignedFixed_polyTime hr (binarySignedSub_polyTime hx hy)

@[fun_prop] theorem binarySignedFixedMul_polyTime {Input : Type} {input : Input ↪ List Bool}
    {ruler x y : Input → List Bool}
    (hr : ComputableInPolyTime ruler input encBits)
    (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => binarySignedFixedMul (ruler a) (x a) (y a)) input encBits :=
  binarySignedFixed_polyTime hr (binarySignedMul_polyTime hx hy)

end GameTheory.Complexity.Backend
