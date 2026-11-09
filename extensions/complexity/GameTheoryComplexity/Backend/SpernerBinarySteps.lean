module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

@[expose] public section

/-! Fixed-width little-endian grid steps ripple through the input bits.
Increment and decrement preserve the word width, with arithmetic wraparound at
the endpoints. Their polynomial-time certificates recurse on bits, never on values. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM Cslib.BitString

/-- Increment a little-endian word at fixed width, discarding the final carry. -/
def gridSuccBits : List Bool → List Bool
  | [] => []
  | false :: bits => true :: bits
  | true :: bits => false :: gridSuccBits bits

/-- Decrement a little-endian word at fixed width, discarding the final borrow. -/
def gridPredBits : List Bool → List Bool
  | [] => []
  | true :: bits => false :: bits
  | false :: bits => true :: gridPredBits bits

/-- Increment preserves the coordinate word's width. -/
@[simp] theorem gridSuccBits_length (bits : List Bool) :
    (gridSuccBits bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [gridSuccBits, ih]

/-- Decrement preserves the coordinate word's width. -/
@[simp] theorem gridPredBits_length (bits : List Bool) :
    (gridPredBits bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [gridPredBits, ih]

private theorem gridSuccBits_eq_increment (bits : List Bool) :
    gridSuccBits bits = Cslib.BitString.increment bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => cases bit <;> simp [gridSuccBits, Cslib.BitString.increment, ih]

private theorem gridPredBits_eq_complement_increment (bits : List Bool) :
    gridPredBits bits = (Cslib.BitString.increment (bits.map Bool.not)).map Bool.not := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    cases bit <;> simp [gridPredBits, Cslib.BitString.increment, ih, List.map_map,
      Function.comp_def]

/-- Fixed-width increment uses the native linear-time counter. -/
@[fun_prop] theorem gridSuccBits_polyTime :
    ComputableInPolyTime gridSuccBits encBits encBits := by
  have heq : gridSuccBits = Cslib.BitString.increment := funext gridSuccBits_eq_increment
  rw [heq]
  exact .of_tidy ComputableTidilyInPolyTime.increment

/-- Complementing around the same counter gives fixed-width decrement. -/
@[fun_prop] theorem gridPredBits_polyTime :
    ComputableInPolyTime gridPredBits encBits encBits := by
  have hnot : ComputableInPolyTime (fun bits : List Bool => bits.map Bool.not)
      encBits encBits :=
    ComputableInPolyTime.bitsMapWithInput ComputableInPolyTime.id'
      (ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.snd encBits encBool))
  have hinc : ComputableInPolyTime Cslib.BitString.increment encBits encBits :=
    .of_tidy ComputableTidilyInPolyTime.increment
  have h := hnot.comp (hinc.comp hnot)
  have heq : gridPredBits = fun bits =>
      (Cslib.BitString.increment (bits.map Bool.not)).map Bool.not :=
    funext gridPredBits_eq_complement_increment
  rw [heq]
  exact h

/-- Increment decodes to ordinary addition when the next value fits the width. -/
theorem gridSuccBits_value_of_lt (bits : List Bool)
    (h : lsbValue bits + 1 < 2 ^ bits.length) :
    lsbValue (gridSuccBits bits) = lsbValue bits + 1 := by
  rw [gridSuccBits_eq_increment]
  exact lsbValue_increment bits h

/-- Decrement decodes to subtraction for every positive coordinate value. -/
theorem gridPredBits_value_of_pos (bits : List Bool) (h : 0 < lsbValue bits) :
    lsbValue (gridPredBits bits) = lsbValue bits - 1 := by
  induction bits with
  | nil => simp [lsbValue] at h
  | cons b bits ih =>
    cases b with
    | false =>
      have ht : 0 < lsbValue bits := by simp [lsbValue] at h; omega
      simp [gridPredBits, lsbValue, ih ht]
      omega
    | true => simp [gridPredBits, lsbValue]

end GameTheory.Complexity.Backend
