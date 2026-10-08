import GameTheoryComplexity.Backend.CircuitCodeShift

/-! Canonical serialized relocation agrees exactly with relocation of raw gates. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.CircuitCode

/-- Relocating a gate stream preserves the exact unconsumed suffix. -/
theorem circuitGateRest_encode (gate : RawGate) (rest : List Bool) :
    circuitGateRest (gate.encode ++ rest) = rest := by
  simp only [circuitGateRest, RawGate.encode, List.append_assoc, List.cons_append, List.nil_append,
    List.drop_succ_cons, List.drop_zero]
  rw [circuitUnaryRest_encode, circuitUnaryRest_encode]

/-- The gate scanner emits precisely the canonical shifted gate code. -/
theorem circuitShiftGate_encode (ruler : List Bool) (gate : RawGate) (rest : List Bool) :
    circuitShiftGate ruler (gate.encode ++ rest) = (gate.shift ruler.length).encode := by
  simp only [circuitShiftGate, RawGate.encode, List.append_assoc, List.cons_append, List.nil_append,
    List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero]
  rw [circuitUnaryRest_encode, circuitUnaryPrefix_encode, circuitUnaryPrefix_encode]
  simp only [List.length_replicate]
  rw [List.take_append_of_le_length (by simp [NatCode.encode]),
    List.take_append_of_le_length (by simp [NatCode.encode])]
  have htake (n : ℕ) : (NatCode.encode n).take (n + 1) = NatCode.encode n := by
    simp [NatCode.encode]
  rw [htake, htake]
  simp only [RawGate.shift, RawGate.opBit, NatCode.encode, List.replicate_add,
    List.append_assoc]

private theorem circuitShiftStep_iterate_encode (ruler : List Bool)
    (gates : RawCircuit) (rest output : List Bool) :
    circuitShiftStep^[gates.length]
      (pair ruler (pair (gates.flatMap RawGate.encode ++ rest) output)) =
      pair ruler (pair rest (output ++ (gates.shift ruler.length).flatMap RawGate.encode)) := by
  induction gates generalizing output with
  | nil => simp [RawCircuit.shift]
  | cons gate gates ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc, circuitShiftStep,
      pairFst_pair, pairSnd_pair, circuitGateRest_encode, circuitShiftGate_encode]
    rw [ih]
    simp [RawCircuit.shift, List.append_assoc]

/-- Serialized relocation agrees with raw relocation, including an empty circuit. -/
theorem shiftCircuitCode_encode (ruler : List Bool) (circuit : RawCircuit) :
    shiftCircuitCode ruler circuit.encode = (circuit.shift ruler.length).encode := by
  simp only [shiftCircuitCode, RawCircuit.encode,
    circuitUnaryPrefix_encode, circuitUnaryRest_encode,
    List.length_replicate]
  rw [show circuit.flatMap RawGate.encode = circuit.flatMap RawGate.encode ++ [] by simp,
    circuitShiftStep_iterate_encode]
  simp [NatCode.encode]

end GameTheory.Complexity.Backend
