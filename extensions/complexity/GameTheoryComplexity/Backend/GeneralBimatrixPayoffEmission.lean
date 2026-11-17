module

public import GameTheoryComplexity.Backend.GeneralBimatrixCodec
public import GameTheoryComplexity.Backend.BinarySignedFixedWidth

@[expose] public section

/-! Rectangular game payoffs store separate fixed-width positive and negative
magnitudes. The writer selects the signed word's appropriate tail and retains
exact truncation and zero padding at every requested width. -/

namespace GameTheory.Complexity.Backend

open Cslib.BitString Turing.MultiTapeTM

/-- Emit one fixed-width magnitude, zeroing the field with the opposite sign. -/
def generalSignedMagnitude (positive : Bool) (ruler word : List Bool) : List Bool :=
  lowBits ruler.length
    (if word.headD false then (if positive then 0 else ofBits word.tail)
     else if positive then ofBits word.tail else 0)

@[simp] theorem generalSignedMagnitude_length (positive : Bool) (ruler word : List Bool) :
    (generalSignedMagnitude positive ruler word).length = ruler.length := by
  simp [generalSignedMagnitude]

/-- The two magnitude fields preserve every signed value fitting the advertised width. -/
theorem generalSignedMagnitude_value (ruler word : List Bool)
    (hfit : (binarySignedValue word).natAbs < 2 ^ ruler.length) :
    (ofBits (generalSignedMagnitude true ruler word) : ℤ) -
      (ofBits (generalSignedMagnitude false ruler word) : ℤ) = binarySignedValue word := by
  have hm : ofBits word.tail < 2 ^ ruler.length := by
    simpa only [binarySignedValue_natAbs] using hfit
  have hvalue : ofBits (lowBits ruler.length (ofBits word.tail)) = ofBits word.tail :=
    Nat.foldr_bit_testBit (Nat.size_le.mpr hm)
  have hzero : ofBits (lowBits ruler.length 0) = 0 :=
    Nat.foldr_bit_testBit (Nat.size_le.mpr (Nat.pow_pos (by decide)))
  cases h : word.head?.getD false <;>
    simp [generalSignedMagnitude, binarySignedValue, h, hvalue, hzero]

/-- Magnitude selection and fixed-width storage charge both actual word producers. -/
@[fun_prop] theorem generalSignedMagnitude_polyTime (positive : Bool)
    {Input : Type} {input : Input ↪ List Bool} {ruler word : Input → List Bool}
    (hr : ComputableInPolyTime ruler input encBits)
    (hw : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => generalSignedMagnitude positive (ruler a) (word a))
      input encBits := by
  have hhead : ComputableInPolyTime (fun a : Input => (word a).headD false) input encBool :=
    (ComputableInPolyTime.headD false).comp hw
  have htail := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hw
  have hmag := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsToNat).comp htail
  cases positive
  · exact ComputableInPolyTime.bitsLow (ComputableInPolyTime.length_bits_comp hr)
      (hhead.ite hmag (ComputableInPolyTime.const 0))
  · exact ComputableInPolyTime.bitsLow (ComputableInPolyTime.length_bits_comp hr)
      (hhead.ite (ComputableInPolyTime.const 0) hmag)

end GameTheory.Complexity.Backend
