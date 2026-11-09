module

public import Complexity.Foundations.Data.BitString.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Fixed-width routing fields are assembled with binary concatenation, padding,
and shifts. Their arithmetic meaning follows the little-endian bit convention. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString

/-- Dropping low bits divides the represented value by their binary place value. -/
theorem routing_lsbValue_drop (width : ℕ) (bits : List Bool) :
    lsbValue (bits.drop width) = lsbValue bits / 2 ^ width := by
  induction width generalizing bits with
  | zero => simp
  | succ width ih =>
    cases bits with
    | nil => simp [lsbValue]
    | cons bit bits =>
      have hhalf : lsbValue (bit :: bits) / 2 = lsbValue bits := by
        rw [lsbValue]
        cases bit with
        | false => simp
        | true => simp only [Bool.toNat_true]; omega
      rw [List.drop_succ_cons, ih, pow_succ, Nat.mul_comm (2 ^ width) 2,
        ← Nat.div_div_eq_div_mul, hhalf]

/-- Taking low bits reduces the represented value modulo their binary capacity. -/
theorem routing_lsbValue_take (width : ℕ) (bits : List Bool) :
    lsbValue (bits.take width) = lsbValue bits % 2 ^ width := by
  by_cases hw : width ≤ bits.length
  · have hl : (bits.take width).length = width := by simp [List.length_take, hw]
    have hb : lsbValue (bits.take width) < 2 ^ width := by
      simpa only [hl] using lsbValue_lt (bits.take width)
    have he : lsbValue bits = lsbValue (bits.take width) +
        2 ^ width * lsbValue (bits.drop width) := by
      simpa only [hl, List.take_append_drop] using
        lsbValue_append (bits.take width) (bits.drop width)
    rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hb]
  · have hlen : bits.length ≤ width := by omega
    have hb : lsbValue bits < 2 ^ width :=
      lt_of_lt_of_le (lsbValue_lt bits)
        (Nat.pow_le_pow_right (by decide) hlen)
    simp [List.take_of_length_le hlen, Nat.mod_eq_of_lt hb]

/-- Pad with high zero bits and truncate to the word ruler's width. -/
def routingPadBits (ruler bits : List Bool) : List Bool :=
  (bits ++ List.replicate ruler.length false).take ruler.length

/-- Shift left by the word ruler's width by prepending low zero bits. -/
def routingShiftBits (ruler bits : List Bool) : List Bool :=
  List.replicate ruler.length false ++ bits

/-- Padding produces exactly the requested number of bits. -/
@[simp] theorem routingPadBits_length (ruler bits : List Bool) :
    (routingPadBits ruler bits).length = ruler.length := by
  simp [routingPadBits]

/-- Padding preserves precisely the low bits within the requested capacity. -/
theorem routingPadBits_value (ruler bits : List Bool) :
    lsbValue (routingPadBits ruler bits) = lsbValue bits % 2 ^ ruler.length := by
  rw [routingPadBits, routing_lsbValue_take, lsbValue_append, lsbValue_replicate_false]
  simp

/-- Padding is the canonical fixed-width encoding of the original word's value. -/
theorem routingPadBits_eq_lowBits (ruler bits : List Bool) :
    routingPadBits ruler bits = lowBits ruler.length (lsbValue bits) := by
  apply lsbValue_injective (by simp)
  rw [routingPadBits_value]
  have h := lsbValue_lowBits (Nat.mod_lt (lsbValue bits) (by positivity : 0 < 2 ^ ruler.length))
  rw [show lowBits ruler.length (lsbValue bits % 2 ^ ruler.length) =
      lowBits ruler.length (lsbValue bits) by
        unfold lowBits
        apply List.map_congr_left
        intro i hi
        simp [Nat.testBit_mod_two_pow, List.mem_range.mp hi]] at h
  exact h.symm

/-- A shift adds the ruler's width to the existing word length. -/
@[simp] theorem routingShiftBits_length (ruler bits : List Bool) :
    (routingShiftBits ruler bits).length = ruler.length + bits.length := by
  simp [routingShiftBits]

/-- A binary shift multiplies the represented value by the ruler's power of two. -/
theorem routingShiftBits_value (ruler bits : List Bool) :
    lsbValue (routingShiftBits ruler bits) = 2 ^ ruler.length * lsbValue bits := by
  simp [routingShiftBits, lsbValue_append, lsbValue_replicate_false]

/-- Padding charges the complete ruler and both materialized word producers. -/
@[fun_prop] theorem routingPadBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler bits : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hb : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun z => routingPadBits (ruler z) (bits z)) enc encBits := by
  have hz : ComputableInPolyTime (fun z => List.replicate (ruler z).length false)
      enc encBits := (bitsReplicate false).comp (length_bits.comp hr)
  exact bitsTakeWithInput (bitsAppend hb hz) (length_bits.comp hr)

/-- A binary shift charges the low zero field and the complete input word. -/
@[fun_prop] theorem routingShiftBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler bits : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits)
    (hb : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun z => routingShiftBits (ruler z) (bits z)) enc encBits := by
  exact bitsAppend ((bitsReplicate false).comp (length_bits.comp hr)) hb

end GameTheory.Complexity.Backend
