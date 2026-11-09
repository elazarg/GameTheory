module

public import GameTheoryComplexity.Backend.CircuitCodeShift

@[expose] public section

/-! Canonical serialized relocation maps the wire numbers in native gate codes
while preserving every operation flag and the exact unconsumed stream suffix.
-/

namespace GameTheory.Complexity.Backend

/-- Skipping a canonical gate preserves the exact following stream. -/
theorem circuitGateRest_encode (op : CircuitFormat.signature.Op) (left right : ℕ)
    (rest : List Bool) :
    circuitGateRest (CircuitFormat.encodeGate op left right ++ rest) = rest := by
  rcases op with ⟨op, negateLeft, negateRight⟩
  simp only [circuitGateRest, CircuitFormat.encodeGate, List.append_assoc, List.cons_append,
    List.nil_append, List.drop_succ_cons, List.drop_zero]
  rw [circuitUnaryRest_encode, circuitUnaryRest_encode]

/-- Relocating one gate preserves its flags and adds the offset to both references. -/
theorem circuitShiftGate_encode (ruler : List Bool) (op : CircuitFormat.signature.Op)
    (left right : ℕ) (rest : List Bool) :
    circuitShiftGate ruler (CircuitFormat.encodeGate op left right ++ rest) =
      CircuitFormat.encodeGate op (ruler.length + left) (ruler.length + right) := by
  rcases op with ⟨op, negateLeft, negateRight⟩
  simp only [circuitShiftGate, CircuitFormat.encodeGate, List.append_assoc, List.cons_append,
    List.nil_append, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero]
  rw [circuitUnaryRest_encode, circuitUnaryPrefix_encode, circuitUnaryPrefix_encode]
  simp only [List.length_replicate]
  rw [List.take_append_of_le_length (by simp [CircuitFormat.encodeUnary]),
    List.take_append_of_le_length (by simp [CircuitFormat.encodeUnary])]
  have htake (n : ℕ) :
      (CircuitFormat.encodeUnary n).take (n + 1) = CircuitFormat.encodeUnary n := by
    simp [CircuitFormat.encodeUnary]
  rw [htake, htake]
  simp only [CircuitFormat.encodeUnary, List.replicate_add, List.append_assoc]

private theorem circuitShiftStep_iterate_encode (ruler : List Bool)
    (gates : List (CircuitFormat.signature.Op × List ℕ))
    (harity : ∀ gate ∈ gates, gate.2.length = 2) (rest output : List Bool) :
    (circuitShiftStep ruler)^[gates.length]
      (gates.flatMap (fun gate => CircuitFormat.encodeGate gate.1
        (gate.2.getD 0 0) (gate.2.getD 1 0)) ++ rest, output) =
      (rest, output ++
        (gates.map (fun gate => (gate.1, gate.2.map (fun ref => ruler.length + ref)))).flatMap
          (fun gate => CircuitFormat.encodeGate gate.1 (gate.2.getD 0 0) (gate.2.getD 1 0))) := by
  induction gates generalizing output with
  | nil => simp
  | cons gate gates ih =>
    rcases gate with ⟨op, args⟩
    obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp (harity (op, args) (by simp))
    have htail : ∀ gate ∈ gates, gate.2.length = 2 :=
      fun gate hg => harity gate (by simp [hg])
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc, circuitShiftStep,
      List.getD_cons_zero, List.getD_cons_succ, circuitGateRest_encode, circuitShiftGate_encode]
    rw [ih htail]
    simp [List.append_assoc]

/-- Serialized relocation agrees with adding the ruler offset to every native
gate reference, including the empty program. -/
theorem shiftCircuitCode_encode (ruler : List Bool)
    (gates : List (CircuitFormat.signature.Op × List ℕ))
    (harity : ∀ gate ∈ gates, gate.2.length = 2) :
    shiftCircuitCode ruler (CircuitFormat.encode gates) =
      CircuitFormat.encode
        (gates.map (fun gate => (gate.1, gate.2.map (fun ref => ruler.length + ref)))) := by
  have hall : gates.all (fun gate => gate.2.length == 2) = true := by
    apply List.all_eq_true.mpr
    intro gate hg
    simp [harity gate hg]
  have hshiftall :
      (gates.map (fun gate => (gate.1, gate.2.map (fun ref => ruler.length + ref)))).all
        (fun gate => gate.2.length == 2) = true := by
    apply List.all_eq_true.mpr
    intro gate hg
    obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hg
    simp [harity source hs]
  have hout := congrArg Prod.snd (circuitShiftStep_iterate_encode ruler gates harity [] [])
  simp only [List.append_nil, List.nil_append] at hout
  simp only [CircuitFormat.encode, hall, hshiftall, ↓reduceIte, shiftCircuitCode,
    circuitUnaryPrefix_encode, circuitUnaryRest_encode, List.length_replicate, List.length_map]
  rw [hout]
  rfl

/-- A relocated gate remains checked when its entire source memo interval fits
inside the destination wire bound. -/
theorem circuitRelocatedGate_valid {width offset bound : ℕ}
    {gates : List (CircuitFormat.signature.Op × List ℕ)}
    (hraw : Cslib.Circuits.Program.IsCodeFrom CircuitFormat.signature width 0 gates)
    (hbound : offset + width + gates.length ≤ bound) (j : Fin gates.length) :
    Cslib.Circuits.Program.IsCodeFrom CircuitFormat.signature bound 0
      [(gates[j.val].1, gates[j.val].2.map (offset + ·))] := by
  have hgate := hraw.getElem j.val j.isLt
  refine ⟨⟨?_, ?_⟩, trivial⟩
  · simpa only [List.length_map] using hgate.1
  · intro reference hreference
    obtain ⟨ref, href, rfl⟩ := List.mem_map.mp hreference
    have hlt := hgate.2 ref href
    have hj := j.isLt
    omega

end GameTheory.Complexity.Backend
