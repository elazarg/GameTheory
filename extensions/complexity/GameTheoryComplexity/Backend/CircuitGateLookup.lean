module

public import GameTheoryComplexity.Backend.CircuitCodeShiftCorrectness

@[expose] public section

/-! Bounded lookup of serialized gates. The scanner strips the count header and
returns the suffix at the requested ordinal. It ignores clock-bit values and
retains its total behavior on malformed fields and exhausted streams.
-/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM

/-- Return the serialized suffix at an ordinal supplied by ruler length. -/
def circuitGateSuffix (code indexRuler : List Bool) : List Bool :=
  circuitGateRest^[indexRuler.length] (circuitUnaryRest code)

private theorem gateRest_iterate_length_le (bits : List Bool) (i : ℕ) :
    (circuitGateRest^[i] bits).length ≤ bits.length := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (circuitGateRest_length_le _).trans ih

/-- Every lookup state is bounded by the original source word. -/
theorem circuitGateSuffix_length_le (code indexRuler : List Bool) :
    (circuitGateSuffix code indexRuler).length ≤ code.length := by
  have h := gateRest_iterate_length_le (circuitUnaryRest code) indexRuler.length
  have hinit : (circuitUnaryRest code).length ≤ code.length := by
    simp only [circuitUnaryRest, List.length_drop]
    omega
  exact h.trans hinit

/-- Uniform suffix lookup charges both the source and its unary ordinal ruler. -/
@[fun_prop] theorem circuitGateSuffix_polyTime {Input : Type} {input : Input ↪ List Bool}
    {code indexRuler : Input → List Bool}
    (hcode : ComputableInPolyTime code input encBits)
    (hindex : ComputableInPolyTime indexRuler input encBits) :
    ComputableInPolyTime (fun a => circuitGateSuffix (code a) (indexRuler a)) input encBits := by
  have h : ComputableInPolyTime
      (fun a => circuitGateRest^[(indexRuler a).length] (circuitUnaryRest (code a)))
      input encBits :=
    ComputableInPolyTime.iterate (step := circuitGateRest)
      (bound := fun a => (code a).length)
      (ComputableInPolyTime.length_bits_comp hindex) (circuitUnaryRest_polyTime hcode)
      (circuitGateRest_polyTime (ComputableInPolyTime.id' (encIn := encBits)))
      hcode.polyBounded_length (by
        intro a i _
        have hinit : (circuitUnaryRest (code a)).length ≤ (code a).length := by
          simp only [circuitUnaryRest, List.length_drop]
          omega
        exact (gateRest_iterate_length_le _ i).trans hinit)
  exact h

private theorem gateRest_iterate_encode (n : ℕ)
    (gates : List (CircuitFormat.signature.Op × List ℕ)) :
    circuitGateRest^[n]
      (gates.flatMap fun gate => CircuitFormat.encodeGate gate.1
        (gate.2.getD 0 0) (gate.2.getD 1 0)) =
      (gates.drop n).flatMap fun gate => CircuitFormat.encodeGate gate.1
        (gate.2.getD 0 0) (gate.2.getD 1 0) := by
  induction n generalizing gates with
  | zero => rfl
  | succ n ih =>
    cases gates with
    | nil =>
      rw [Function.iterate_succ_apply]
      have hnil : circuitGateRest [] = [] := by simp [circuitGateRest, circuitUnaryRest]
      simpa only [List.flatMap_nil, List.drop_nil, hnil] using ih []
    | cons gate gates =>
      rw [Function.iterate_succ_apply]
      simp only [List.flatMap_cons, circuitGateRest_encode]
      simpa only [List.drop_succ_cons] using ih gates

/-- Canonical lookup returns the exact suffix, even beyond the declared gate count. -/
theorem circuitGateSuffix_encode (gates : List (CircuitFormat.signature.Op × List ℕ))
    (harity : ∀ gate ∈ gates, gate.2.length = 2) (indexRuler : List Bool) :
    circuitGateSuffix (CircuitFormat.encode gates) indexRuler =
      (gates.drop indexRuler.length).flatMap fun gate => CircuitFormat.encodeGate gate.1
        (gate.2.getD 0 0) (gate.2.getD 1 0) := by
  have hall : gates.all (fun gate => gate.2.length == 2) = true := by
    apply List.all_eq_true.mpr
    intro gate hg
    simp [harity gate hg]
  simp only [circuitGateSuffix, CircuitFormat.encode, hall, ↓reduceIte, circuitUnaryRest_encode]
  exact gateRest_iterate_encode _ _

/-- A canonical out-of-range lookup returns the empty stream. -/
theorem circuitGateSuffix_encode_of_length_le
    (gates : List (CircuitFormat.signature.Op × List ℕ))
    (harity : ∀ gate ∈ gates, gate.2.length = 2) (ruler : List Bool)
    (h : gates.length ≤ ruler.length) :
    circuitGateSuffix (CircuitFormat.encode gates) ruler = [] := by
  rw [circuitGateSuffix_encode gates harity ruler, List.drop_eq_nil_iff.mpr h]
  rfl

end GameTheory.Complexity.Backend
