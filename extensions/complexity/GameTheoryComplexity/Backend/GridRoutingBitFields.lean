import GameTheoryComplexity.Backend.EndOfLineMachineOps
import Complexitylib.Mathlib.NatBits
import Complexitylib.Classes.P.Cobham.Internal.Extract
import Mathlib.Tactic.Ring

/-! Fixed-width routing fields are assembled with binary concatenation, padding,
and shifts. Their arithmetic meaning follows the little-endian bit convention. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps

/-- Appending a high field shifts it by the low field's width. -/
theorem routing_fromBitsLE_append (low high : List Bool) :
    Nat.fromBitsLE (low ++ high) =
      Nat.fromBitsLE low + 2 ^ low.length * Nat.fromBitsLE high := by
  induction low with
  | nil => simp [Nat.fromBitsLE, Nat.fromBits]
  | cons bit low ih =>
    simp only [List.cons_append, Nat.fromBitsLE_cons, List.length_cons, pow_succ, ih]
    ring

/-- Dropping low bits divides the represented value by their binary place value. -/
theorem routing_fromBitsLE_drop (width : ℕ) (bits : List Bool) :
    Nat.fromBitsLE (bits.drop width) = Nat.fromBitsLE bits / 2 ^ width := by
  induction width generalizing bits with
  | zero => simp
  | succ width ih =>
    cases bits with
    | nil => simp [Nat.fromBitsLE, Nat.fromBits]
    | cons bit bits =>
      have hhalf : Nat.fromBitsLE (bit :: bits) / 2 = Nat.fromBitsLE bits := by
        rw [Nat.fromBitsLE_cons]
        cases bit with
        | false => simp
        | true => simp only [ite_true]; omega
      rw [List.drop_succ_cons, ih, pow_succ, Nat.mul_comm (2 ^ width) 2,
        ← Nat.div_div_eq_div_mul, hhalf]

/-- Taking low bits reduces the represented value modulo their binary capacity. -/
theorem routing_fromBitsLE_take (width : ℕ) (bits : List Bool) :
    Nat.fromBitsLE (bits.take width) = Nat.fromBitsLE bits % 2 ^ width := by
  by_cases hw : width ≤ bits.length
  · have hl : (bits.take width).length = width := by simp [List.length_take, hw]
    have hb : Nat.fromBitsLE (bits.take width) < 2 ^ width := by
      simpa only [hl] using Nat.fromBitsLE_lt_pow_length (bits.take width)
    have he : Nat.fromBitsLE bits = Nat.fromBitsLE (bits.take width) +
        2 ^ width * Nat.fromBitsLE (bits.drop width) := by
      simpa only [hl, List.take_append_drop] using
        routing_fromBitsLE_append (bits.take width) (bits.drop width)
    rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hb]
  · have hlen : bits.length ≤ width := by omega
    have hb : Nat.fromBitsLE bits < 2 ^ width :=
      lt_of_lt_of_le (Nat.fromBitsLE_lt_pow_length bits)
        (Nat.pow_le_pow_right (by decide) hlen)
    simp [List.take_of_length_le hlen, Nat.mod_eq_of_lt hb]

private theorem fromBitsLE_zero (width : ℕ) :
    Nat.fromBitsLE (List.replicate width false) = 0 := by
  induction width with
  | zero => rfl
  | succ width ih => simp [List.replicate_succ, Nat.fromBitsLE_cons, ih]

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
    Nat.fromBitsLE (routingPadBits ruler bits) = Nat.fromBitsLE bits % 2 ^ ruler.length := by
  rw [routingPadBits, routing_fromBitsLE_take, routing_fromBitsLE_append, fromBitsLE_zero]
  simp

/-- Padding is the canonical fixed-width encoding of the original word's value. -/
theorem routingPadBits_eq_toBitsLE (ruler bits : List Bool) :
    routingPadBits ruler bits = Nat.toBitsLE ruler.length (Nat.fromBitsLE bits) := by
  apply Nat.fromBitsLE_inj_of_length_eq
  · simp
  · rw [routingPadBits_value, Nat.fromBitsLE_toBitsLE_mod]

/-- A shift adds the ruler's width to the existing word length. -/
@[simp] theorem routingShiftBits_length (ruler bits : List Bool) :
    (routingShiftBits ruler bits).length = ruler.length + bits.length := by
  simp [routingShiftBits]

/-- A binary shift multiplies the represented value by the ruler's power of two. -/
theorem routingShiftBits_value (ruler bits : List Bool) :
    Nat.fromBitsLE (routingShiftBits ruler bits) = 2 ^ ruler.length * Nat.fromBitsLE bits := by
  simp [routingShiftBits, routing_fromBitsLE_append, fromBitsLE_zero]

/-- Padding composes arbitrary polynomial-time ruler and bit producers. -/
theorem routingPadBitsFn_mem_FP {ruler bits : List Bool → List Bool}
    (hr : ruler ∈ FP) (hb : bits ∈ FP) :
    (fun z => routingPadBits (ruler z) (bits z)) ∈ FP := by
  have hz : (fun z => List.replicate (ruler z).length false) ∈ FP := by
    simpa only [List.length_singleton, Nat.one_mul] using
      mulLenFn_mem_FP (constFn_mem_FP [false]) hr
  apply CobhamFP_subset_FP
  exact takeFn (FP_subset_CobhamFP hr) (FP_subset_CobhamFP (appendFn_mem_FP hb hz))

/-- A binary shift composes arbitrary polynomial-time ruler and bit producers. -/
theorem routingShiftBitsFn_mem_FP {ruler bits : List Bool → List Bool}
    (hr : ruler ∈ FP) (hb : bits ∈ FP) :
    (fun z => routingShiftBits (ruler z) (bits z)) ∈ FP := by
  have hz : (fun z => List.replicate (ruler z).length false) ∈ FP := by
    simpa only [List.length_singleton, Nat.one_mul] using
      mulLenFn_mem_FP (constFn_mem_FP [false]) hr
  exact appendFn_mem_FP hz hb

end GameTheory.Complexity.Backend
