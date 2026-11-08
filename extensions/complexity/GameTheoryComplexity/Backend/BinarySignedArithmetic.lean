module

public import GameTheoryComplexity.Backend.BinaryWordMultiplication
public import GameTheoryComplexity.Backend.WordOperations

@[expose] public section

/-! Signed binary multiplication and comparison with explicit sign headers.

The tail is an arbitrary little-endian magnitude. Empty words, sign-only words,
and padded negative zeros all denote zero. Operations use certified word
machines and never iterate the represented integer values.
-/

namespace GameTheory.Complexity.Backend

open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

/-- A true header denotes a negative little-endian magnitude. -/
def binarySignedValue (x : List Bool) : ℤ :=
  if x.headD false then -(ofBits x.tail : ℤ) else (ofBits x.tail : ℤ)

/-- Multiply signed words by multiplying their tails and taking the exclusive-or sign. -/
def binarySignedMul (x y : List Bool) : List Bool :=
  [(x.headD false).xor (y.headD false)] ++ binaryWordMul x.tail y.tail

theorem binarySignedMul_value (x y : List Bool) :
    binarySignedValue (binarySignedMul x y) = binarySignedValue x * binarySignedValue y := by
  rw [binarySignedMul]
  simp only [List.singleton_append, binarySignedValue, List.headD_cons, List.tail_cons,
    binaryWordMul_value, Nat.cast_mul]
  generalize x.headD false = a
  generalize y.headD false = b
  cases a <;> cases b <;> simp

theorem binarySignedMul_length (x y : List Bool) :
    (binarySignedMul x y).length ≤ 1 + y.length + 2 * x.length := by
  rw [binarySignedMul]
  simp only [List.length_append, List.length_singleton]
  have h := binaryWordMul_length x.tail y.tail
  simp only [List.length_tail] at h
  omega

private def signedRawLT (x y : List Bool) : List Bool :=
  notFlag (binaryCertificateLE ![y, x])

private theorem signedRawLT_value (x y : List Bool) :
    signedRawLT x y = [decide (ofBits x < ofBits y)] := by
  by_cases h : ofBits y ≤ ofBits x
  · have hn : ¬ ofBits x < ofBits y := by omega
    simp [signedRawLT, binaryCertificateLE_value, h, hn, notFlag]
  · have hl : ofBits x < ofBits y := by omega
    simp [signedRawLT, binaryCertificateLE_value, h, hl, notFlag]

private def effectiveNegative (x : List Bool) : List Bool :=
  andFlag ([x.headD false]) (signedRawLT [] x.tail)

private theorem effectiveNegative_value (x : List Bool) :
    effectiveNegative x = [decide (binarySignedValue x < 0)] := by
  rw [effectiveNegative, signedRawLT_value]
  rw [show ofBits [] = 0 from rfl]
  unfold binarySignedValue
  generalize x.headD false = b
  cases b
  · simp [andFlag]
  · by_cases h : 0 < ofBits x.tail
    · simp [andFlag, h]
    · have hz : ofBits x.tail = 0 := by omega
      simp [andFlag, hz]

@[fun_prop] private theorem binaryCertificateLE_comp
    {Input : Type} {input : Input ↪ List Bool} {x y : Input → List Bool}
    (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => binaryCertificateLE ![x a, y a]) input encBits := by
  have htable : ComputableInPolyTime (fun a : Input => ![x a, y a])
      input (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hx
    · exact hy
  exact binaryCertificateLE_polyTime.comp htable

/-- Compare effective signs first and compare magnitudes in the appropriate direction. -/
def binarySignedLTFlag (x y : List Bool) : List Bool :=
  select (andFlag [x.headD false] (notFlag (binaryCertificateLE ![x.tail, []])))
    (select (andFlag [y.headD false] (notFlag (binaryCertificateLE ![y.tail, []])))
      (notFlag (binaryCertificateLE ![x.tail, y.tail])) [true])
    (select (andFlag [y.headD false] (notFlag (binaryCertificateLE ![y.tail, []])))
      [false] (notFlag (binaryCertificateLE ![y.tail, x.tail])))

theorem binarySignedLTFlag_value (x y : List Bool) :
    binarySignedLTFlag x y = [decide (binarySignedValue x < binarySignedValue y)] := by
  change select (effectiveNegative x)
    (select (effectiveNegative y) (signedRawLT y.tail x.tail) [true])
    (select (effectiveNegative y) [false] (signedRawLT x.tail y.tail)) = _
  rw [effectiveNegative_value, effectiveNegative_value,
    signedRawLT_value, signedRawLT_value]
  unfold binarySignedValue
  generalize ofBits x.tail = a
  generalize ofBits y.tail = b
  generalize x.headD false = sx
  generalize y.headD false = sy
  have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  have hb0 : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  cases sx <;> cases sy <;> by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp [ha, hb, select, Nat.pos_iff_ne_zero, not_lt_of_ge ha0, not_lt_of_ge hb0];
    omega

@[simp] theorem binarySignedLTFlag_length (x y : List Bool) :
    (binarySignedLTFlag x y).length = 1 := by rw [binarySignedLTFlag_value]; rfl

/-- Negation flips the sign header and preserves all magnitude padding. -/
def binarySignedNeg (x : List Bool) : List Bool := notFlag ([x.headD false]) ++ x.tail

theorem binarySignedNeg_value (x : List Bool) :
    binarySignedValue (binarySignedNeg x) = -binarySignedValue x := by
  rw [binarySignedNeg]
  unfold binarySignedValue
  generalize x.headD false = b
  cases b <;> simp [notFlag]

theorem binarySignedNeg_length (x : List Bool) : (binarySignedNeg x).length ≤ x.length + 1 := by
  have hf : (notFlag ([x.headD false])).length = 1 := by
    generalize x.headD false = b
    cases b <;> rfl
  simp only [binarySignedNeg, List.length_append, hf, List.length_tail]
  omega

/-- Signed multiplication composes uniformly with two certified word producers. -/
@[fun_prop] theorem binarySignedMul_polyTime
    {Input : Type} {input : Input ↪ List Bool} {x y : Input → List Bool}
    (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => binarySignedMul (x a) (y a)) input encBits := by
  have hheadx : ComputableInPolyTime (fun a : Input => (x a).headD false) input encBool :=
    (ComputableInPolyTime.headD false).comp hx
  have hheady : ComputableInPolyTime (fun a : Input => (y a).headD false) input encBool :=
    (ComputableInPolyTime.headD false).comp hy
  have hsign := ComputableInPolyTime.bool_xor.comp (hheadx.prod hheady)
  have hheader := ComputableInPolyTime.bitsCons hsign (ComputableInPolyTime.const [])
  have htailx := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hx
  have htaily := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hy
  exact ComputableInPolyTime.bitsAppend hheader (binaryWordMul_polyTime htailx htaily)

/-- Strict signed comparison retains the complete encoding of both word producers. -/
@[fun_prop] theorem binarySignedLTFlag_polyTime
    {Input : Type} {input : Input ↪ List Bool} {x y : Input → List Bool}
    (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => binarySignedLTFlag (x a) (y a)) input encBits := by
  have hnegx : ComputableInPolyTime (fun a : Input => effectiveNegative (x a))
      input encBits := by
    have hbits : ComputableInPolyTime (fun a : Input => [(x a).headD false]) input encBits :=
      .bitsCons ((ComputableInPolyTime.headD false).comp hx) (.const [])
    have htail : ComputableInPolyTime (fun a : Input => (x a).tail) input encBits :=
      (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hx
    have hcmp := binaryCertificateLE_comp htail (.const [])
    have hraw := notFlag_polyTime.comp hcmp
    exact andFlag_polyTime.comp (hbits.prod hraw)
  have hnegy : ComputableInPolyTime (fun a : Input => effectiveNegative (y a))
      input encBits := by
    have hbits : ComputableInPolyTime (fun a : Input => [(y a).headD false]) input encBits :=
      .bitsCons ((ComputableInPolyTime.headD false).comp hy) (.const [])
    have htail : ComputableInPolyTime (fun a : Input => (y a).tail) input encBits :=
      (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hy
    have hcmp := binaryCertificateLE_comp htail (.const [])
    have hraw := notFlag_polyTime.comp hcmp
    exact andFlag_polyTime.comp (hbits.prod hraw)
  have htx : ComputableInPolyTime (fun a : Input => (x a).tail) input encBits :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hx
  have hty : ComputableInPolyTime (fun a : Input => (y a).tail) input encBits :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hy
  have hxy := binaryCertificateLE_comp htx hty
  have hyx := binaryCertificateLE_comp hty htx
  have hrawxy := notFlag_polyTime.comp hxy
  have hrawyx := notFlag_polyTime.comp hyx
  have htrue : ComputableInPolyTime (fun _ : Input => [true]) input encBits := .const [true]
  have hfalse : ComputableInPolyTime (fun _ : Input => [false]) input encBits := .const [false]
  have hbranchNeg : ComputableInPolyTime (fun a : Input =>
      select (effectiveNegative (y a)) (signedRawLT (y a).tail (x a).tail) [true])
      input encBits := select_polyTime.comp (hnegy.prod (hrawxy.prod htrue))
  have hbranchPos : ComputableInPolyTime (fun a : Input =>
      select (effectiveNegative (y a)) [false] (signedRawLT (x a).tail (y a).tail))
      input encBits := select_polyTime.comp (hnegy.prod (hfalse.prod hrawyx))
  exact select_polyTime.comp (hnegx.prod (hbranchNeg.prod hbranchPos))

/-- Header negation composes with a certified producer on any declared input encoding. -/
@[fun_prop] theorem binarySignedNeg_polyTime
    {Input : Type} {input : Input ↪ List Bool} {x : Input → List Bool}
    (hx : ComputableInPolyTime x input encBits) :
    ComputableInPolyTime (fun a => binarySignedNeg (x a)) input encBits := by
  have hhead := ComputableInPolyTime.bitsCons
    ((ComputableInPolyTime.headD false).comp hx) (ComputableInPolyTime.const [])
  have hnot := notFlag_polyTime.comp hhead
  have htail := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hx
  exact ComputableInPolyTime.bitsAppend hnot htail

end GameTheory.Complexity.Backend
