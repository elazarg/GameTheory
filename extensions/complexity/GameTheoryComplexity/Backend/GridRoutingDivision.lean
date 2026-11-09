module

public import Complexity.Foundations.Data.BitString.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

@[expose] public section

/-! Binary routing quotients and remainders use native binary arithmetic and
explicit finite output widths. Values remain binary in the machine, while the
complete emitted bit widths are charged in unary. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString

/-- Divide by three, retaining the input word's exact width and zero padding. -/
def routingDivThreeBits (bits : List Bool) : List Bool :=
  lowBits bits.length (ofBits bits / 3)

/-- Divide by six by dropping the low bit of the padded quotient by three. -/
def routingDivSixBits (bits : List Bool) : List Bool := (routingDivThreeBits bits).tail

/-- Represent the residue modulo three in exactly two little-endian bits. -/
def routingModThreeBits (bits : List Bool) : List Bool :=
  lowBits 2 (ofBits bits % 3)

@[simp] theorem routingDivThreeBits_length (bits : List Bool) :
    (routingDivThreeBits bits).length = bits.length := by simp [routingDivThreeBits]

private theorem ofBits_eq_lsbValue (bits : List Bool) : ofBits bits = lsbValue bits :=
  (lsbValue_eq_foldr_bit bits).symm

/-- The fixed-width quotient decodes to exact division by three. -/
theorem routingDivThreeBits_value (bits : List Bool) :
    lsbValue (routingDivThreeBits bits) = lsbValue bits / 3 := by
  have hvalue : ofBits bits < 2 ^ bits.length := Nat.foldr_bit_lt bits
  have hquot : ofBits bits / 3 < 2 ^ bits.length :=
    (Nat.div_le_self _ _).trans_lt hvalue
  rw [routingDivThreeBits, lsbValue_lowBits hquot, ofBits_eq_lsbValue]

@[simp] theorem routingDivSixBits_length (bits : List Bool) :
    (routingDivSixBits bits).length = bits.length - 1 := by simp [routingDivSixBits]

private theorem lsbValue_tail (bits : List Bool) : lsbValue bits.tail = lsbValue bits / 2 := by
  cases bits with
  | nil => rfl
  | cons bit bits =>
    cases bit with
    | false => simp [lsbValue]
    | true => simp only [List.tail_cons, lsbValue, Bool.toNat_true]; omega

/-- The shortened quotient decodes to exact division by six. -/
theorem routingDivSixBits_value (bits : List Bool) :
    lsbValue (routingDivSixBits bits) = lsbValue bits / 6 := by
  rw [routingDivSixBits, lsbValue_tail, routingDivThreeBits_value, Nat.div_div_eq_div_mul]

@[simp] theorem routingModThreeBits_length (bits : List Bool) :
    (routingModThreeBits bits).length = 2 := by simp [routingModThreeBits]

theorem routingModThreeBits_value (bits : List Bool) :
    lsbValue (routingModThreeBits bits) = lsbValue bits % 3 := by
  have hrem : ofBits bits % 3 < 2 ^ 2 :=
    (Nat.mod_lt _ (by decide : 0 < 3)).trans_le (by decide)
  rw [routingModThreeBits, lsbValue_lowBits hrem, ofBits_eq_lsbValue]

/-- Native binary division and complete fixed-width output are both charged. -/
@[fun_prop] theorem routingDivThreeBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {bits : α → List Bool}
    (hb : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun a => routingDivThreeBits (bits a)) enc encBits := by
  have hquot : ComputableInPolyTime (fun a => ofBits (bits a) / 3) enc encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_div.comp
      ((ComputableInPolyTime.bitsToNat.comp hb).tidy.prod (.const 3)))
  exact bitsLow (length_bits.comp hb) hquot

@[fun_prop] theorem routingDivSixBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {bits : α → List Bool}
    (hb : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun a => routingDivSixBits (bits a)) enc encBits :=
  bitsTail.comp (routingDivThreeBits_polyTime hb)

@[fun_prop] theorem routingModThreeBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {bits : α → List Bool}
    (hb : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun a => routingModThreeBits (bits a)) enc encBits := by
  have hrem : ComputableInPolyTime (fun a => ofBits (bits a) % 3) enc encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_mod.comp
      ((ComputableInPolyTime.bitsToNat.comp hb).tidy.prod (.const 3)))
  exact bitsLow (const 2) hrem

end GameTheory.Complexity.Backend
