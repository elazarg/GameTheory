module

public import GameTheoryComplexity.Backend.BinaryCertificateArithmetic
public import Complexity.Foundations.Data.BitString.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

@[expose] public section

/-! A ruler length has a canonical padded binary encoding. -/
namespace GameTheory.Complexity.Backend

open Cslib.BitString Turing.MultiTapeTM

/-- Encode a ruler length as a little-endian unsigned binary word.

The zero ruler has no bits. Every positive length uses its value plus one bits,
matching the increment-by-one construction of the canonical ruler encoding.
-/
def binaryLengthWord (r : List Bool) : List Bool :=
  if r.isEmpty then [] else lowBits (r.length + 1) r.length

theorem binaryLengthWord_value (r : List Bool) :
    ofBits (binaryLengthWord r) = r.length := by
  cases r with
  | nil => rfl
  | cons b r =>
    change (lowBits (r.length + 1 + 1) (r.length + 1)).foldr Nat.bit 0 = r.length + 1
    rw [← Cslib.BitString.lsbValue_eq_foldr_bit]
    exact Cslib.BitString.lsbValue_lowBits
      ((Nat.lt_succ_self (r.length + 1)).trans Nat.lt_two_pow_self)

theorem binaryLengthWord_length (r : List Bool) :
    (binaryLengthWord r).length ≤ r.length + 1 := by
  cases r with
  | nil => simp [binaryLengthWord]
  | cons b r => simp [binaryLengthWord]

/-- The zero encoding is empty; positive lengths retain their explicit padded width. -/
theorem binaryLengthWord_length_eq (r : List Bool) :
    (binaryLengthWord r).length = if r.length = 0 then 0 else r.length + 1 := by
  cases r with
  | nil => simp [binaryLengthWord]
  | cons b r => simp [binaryLengthWord]

@[fun_prop] theorem binaryLengthWord_polyTime :
    ComputableInPolyTime binaryLengthWord encBits encBits := by
  have hr : ComputableInPolyTime (fun r : List Bool => r) encBits encBits := .id'
  have hlen := ComputableInPolyTime.length_bits_comp hr
  have hwidth := ComputableInPolyTime.unary_add.comp (hlen.prod (.const 1))
  have hbinary := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary).comp hlen
  have hlow := ComputableInPolyTime.bitsLow hwidth hbinary
  have hempty : ComputableInPolyTime List.isEmpty encBits encBool :=
    ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsIsEmpty
  exact (hempty.comp hr).ite (.const []) hlow

end GameTheory.Complexity.Backend
