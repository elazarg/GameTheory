module

public import GameTheoryComplexity.Backend.BinarySignedArithmetic
public import GameTheoryComplexity.Backend.WordOperations
public import GameTheoryComplexity.Backend.BinaryWordSubtraction

@[expose] public section

/-! Exact signed addition using bit-length-bounded magnitude arithmetic.
Opposite signs subtract the smaller magnitude from the larger; equal signs
retain the sign and add magnitudes. Padded and negative-zero inputs are accepted.
-/

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

private def sameSignFlag (x y : List Bool) : List Bool :=
  orFlag (andFlag [x.headD false] [y.headD false])
    (andFlag (notFlag [x.headD false]) (notFlag [y.headD false]))

/-- Add two sign-header, little-endian-magnitude words without numeric-value loops. -/
def binarySignedAdd (x y : List Bool) : List Bool :=
  select (orFlag (andFlag [x.headD false] [y.headD false])
      (andFlag (notFlag [x.headD false]) (notFlag [y.headD false])))
    ([x.headD false] ++ binaryCertificateAdd ![x.tail, y.tail])
    (select (binaryCertificateLE ![y.tail, x.tail])
      ([x.headD false] ++ binaryWordSub x.tail y.tail)
      ([y.headD false] ++ binaryWordSub y.tail x.tail))

private theorem sameSignFlag_value (x y : List Bool) :
    sameSignFlag x y = [decide (x.headD false = y.headD false)] := by
  rw [sameSignFlag]
  generalize x.headD false = a
  generalize y.headD false = b
  cases a <;> cases b <;> rfl

/-- Signed addition is exact for arbitrary padding and either representation of zero. -/
theorem binarySignedAdd_value (x y : List Bool) :
    binarySignedValue (binarySignedAdd x y) = binarySignedValue x + binarySignedValue y := by
  change binarySignedValue (select (sameSignFlag x y)
    ([x.headD false] ++ binaryCertificateAdd ![x.tail, y.tail])
    (select (binaryCertificateLE ![y.tail, x.tail])
      ([x.headD false] ++ binaryWordSub x.tail y.tail)
      ([y.headD false] ++ binaryWordSub y.tail x.tail))) = _
  rw [sameSignFlag_value, binaryCertificateLE_value]
  unfold binarySignedValue
  generalize x.headD false = sx
  generalize y.headD false = sy
  cases sx <;> cases sy <;>
    by_cases h : ofBits y.tail ≤ ofBits x.tail <;>
    simp [select, h, binaryCertificateAdd_value, binaryWordSub_value] <;> omega

/-- The output length is linear in the input word lengths. -/
theorem binarySignedAdd_length (x y : List Bool) :
    (binarySignedAdd x y).length ≤ max x.length y.length + 2 := by
  change (select (sameSignFlag x y)
    ([x.headD false] ++ binaryCertificateAdd ![x.tail, y.tail])
    (select (binaryCertificateLE ![y.tail, x.tail])
      ([x.headD false] ++ binaryWordSub x.tail y.tail)
      ([y.headD false] ++ binaryWordSub y.tail x.tail))).length ≤ _
  rw [sameSignFlag_value, binaryCertificateLE_value]
  have hs := binaryWordSub_length x.tail y.tail
  have ht := binaryWordSub_length y.tail x.tail
  generalize x.headD false = sx
  generalize y.headD false = sy
  cases sx <;> cases sy <;>
    by_cases h : ofBits y.tail ≤ ofBits x.tail <;>
    simp [h, select, binaryCertificateAdd_length] <;>
    simp only [List.length_tail] at * <;> omega

private theorem binaryCertificateAdd_comp {Input : Type} {input : Input ↪ List Bool}
    {x y : Input → List Bool} (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => binaryCertificateAdd ![x a, y a]) input encBits := by
  have htable : ComputableInPolyTime (fun a : Input => ![x a, y a])
      input (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hx
    · exact hy
  exact binaryCertificateAdd_polyTime.comp htable

private theorem binaryCertificateLE_comp {Input : Type} {input : Input ↪ List Bool}
    {x y : Input → List Bool} (hx : ComputableInPolyTime x input encBits)
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

private theorem sameSignFlag_comp {Input : Type} {input : Input ↪ List Bool}
    {x y : Input → List Bool} (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => sameSignFlag (x a) (y a)) input encBits := by
  have hheadx := ComputableInPolyTime.bitsCons
    ((ComputableInPolyTime.headD false).comp hx) (.const [])
  have hheady := ComputableInPolyTime.bitsCons
    ((ComputableInPolyTime.headD false).comp hy) (.const [])
  have hand := andFlag_polyTime.comp (hheadx.prod hheady)
  have hnotx := notFlag_polyTime.comp hheadx
  have hnoty := notFlag_polyTime.comp hheady
  have hboth := andFlag_polyTime.comp (hnotx.prod hnoty)
  exact orFlag_polyTime.comp (hand.prod hboth)

/-- Signed addition composes certified word producers on their original input encoding. -/
@[fun_prop] theorem binarySignedAdd_polyTime {Input : Type} {input : Input ↪ List Bool}
    {x y : Input → List Bool} (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => binarySignedAdd (x a) (y a)) input encBits := by
  have hflag := sameSignFlag_comp hx hy
  have hheadx := ComputableInPolyTime.bitsCons
    ((ComputableInPolyTime.headD false).comp hx) (.const [])
  have hheady := ComputableInPolyTime.bitsCons
    ((ComputableInPolyTime.headD false).comp hy) (.const [])
  have htailx := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hx
  have htaily := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hy
  have hadd := binaryCertificateAdd_comp htailx htaily
  have hle := binaryCertificateLE_comp htaily htailx
  have hsubxy := binaryWordSub_polyTime htailx htaily
  have hsubyx := binaryWordSub_polyTime htaily htailx
  have hsame := ComputableInPolyTime.bitsAppend hheadx hadd
  have hleft := ComputableInPolyTime.bitsAppend hheadx hsubxy
  have hright := ComputableInPolyTime.bitsAppend hheady hsubyx
  have hopp := select_polyTime.comp (hle.prod (hleft.prod hright))
  exact select_polyTime.comp (hflag.prod (hsame.prod hopp))

/-- Subtract signed words by composing addition and header negation. -/
def binarySignedSub (x y : List Bool) : List Bool := binarySignedAdd x (binarySignedNeg y)

theorem binarySignedSub_value (x y : List Bool) :
    binarySignedValue (binarySignedSub x y) = binarySignedValue x - binarySignedValue y := by
  rw [binarySignedSub, binarySignedAdd_value, binarySignedNeg_value, sub_eq_add_neg]

theorem binarySignedSub_length (x y : List Bool) :
    (binarySignedSub x y).length ≤ max x.length y.length + 3 := by
  have h := binarySignedAdd_length x (binarySignedNeg y)
  have hn := binarySignedNeg_length y
  unfold binarySignedSub
  omega

/-- Signed subtraction composes addition and negation without changing either input encoding. -/
@[fun_prop] theorem binarySignedSub_polyTime
    {Input : Type} {input : Input ↪ List Bool} {x y : Input → List Bool}
    (hx : ComputableInPolyTime x input encBits)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => binarySignedSub (x a) (y a)) input encBits :=
  binarySignedAdd_polyTime hx (binarySignedNeg_polyTime hy)

end GameTheory.Complexity.Backend
