import Complexitylib.Mathlib.NatBits
import Complexitylib.Classes.P.Cobham

/-! Fixed-width little-endian grid steps ripple through the input bits.
Increment and decrement preserve the word width, with arithmetic wraparound at
the endpoints. Their polynomial-time certificates recurse on bits, never on values. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

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

private theorem gridSuccBits_rec (bits : List Bool) (v : Fin 0 → List Bool) :
    recNotation (fun _ : Fin 0 → List Bool => [])
      (fun w : Fin 2 → List Bool => true :: w 0)
      (fun w : Fin 2 → List Bool => false :: w 1) bits v = gridSuccBits bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [recNotation_cons, gridSuccBits, ih]

private theorem gridPredBits_rec (bits : List Bool) (v : Fin 0 → List Bool) :
    recNotation (fun _ : Fin 0 → List Bool => [])
      (fun w : Fin 2 → List Bool => true :: w 1)
      (fun w : Fin 2 → List Bool => false :: w 0) bits v = gridPredBits bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [recNotation_cons, gridPredBits, ih]

/-- Fixed-width increment is computed by an actual polynomial-time word machine. -/
theorem gridSuccBits_mem_FP : gridSuccBits ∈ FP := by
  apply CobhamFP_subset_FP
  have h := Cobham.boundedRec (n := 0) Cobham.empty
    (Cobham.comp (Cobham.bit true) (fun _ : Fin 1 => Cobham.proj (0 : Fin 2)))
    (Cobham.comp (Cobham.bit false) (fun _ : Fin 1 => Cobham.proj (1 : Fin 2)))
    (Cobham.proj (0 : Fin 1)) (fun bits v => by
      rw [gridSuccBits_rec, gridSuccBits_length]
      rfl)
  exact h.of_eq fun v => gridSuccBits_rec (v 0) (Fin.tail v)

/-- Fixed-width decrement is computed by an actual polynomial-time word machine. -/
theorem gridPredBits_mem_FP : gridPredBits ∈ FP := by
  apply CobhamFP_subset_FP
  have h := Cobham.boundedRec (n := 0) Cobham.empty
    (Cobham.comp (Cobham.bit true) (fun _ : Fin 1 => Cobham.proj (1 : Fin 2)))
    (Cobham.comp (Cobham.bit false) (fun _ : Fin 1 => Cobham.proj (0 : Fin 2)))
    (Cobham.proj (0 : Fin 1)) (fun bits v => by
      rw [gridPredBits_rec, gridPredBits_length]
      rfl)
  exact h.of_eq fun v => gridPredBits_rec (v 0) (Fin.tail v)

/-- Increment decodes to ordinary addition when the next value fits the width. -/
theorem gridSuccBits_value_of_lt (bits : List Bool)
    (h : Nat.fromBitsLE bits + 1 < 2 ^ bits.length) :
    Nat.fromBitsLE (gridSuccBits bits) = Nat.fromBitsLE bits + 1 := by
  induction bits with
  | nil => simp [Nat.fromBitsLE, Nat.fromBits] at h
  | cons b bits ih =>
    cases b with
    | false => simp [gridSuccBits, Nat.fromBitsLE_cons]; omega
    | true =>
      have ht : Nat.fromBitsLE bits + 1 < 2 ^ bits.length := by
        simp [Nat.fromBitsLE_cons, pow_succ] at h
        omega
      simp [gridSuccBits, Nat.fromBitsLE_cons, ih ht]
      omega

/-- Decrement decodes to subtraction for every positive coordinate value. -/
theorem gridPredBits_value_of_pos (bits : List Bool) (h : 0 < Nat.fromBitsLE bits) :
    Nat.fromBitsLE (gridPredBits bits) = Nat.fromBitsLE bits - 1 := by
  induction bits with
  | nil => simp [Nat.fromBitsLE, Nat.fromBits] at h
  | cons b bits ih =>
    cases b with
    | false =>
      have ht : 0 < Nat.fromBitsLE bits := by simp [Nat.fromBitsLE_cons] at h; omega
      simp [gridPredBits, Nat.fromBitsLE_cons, ih ht]
      omega
    | true => simp [gridPredBits, Nat.fromBitsLE_cons]

end GameTheory.Complexity.Backend
