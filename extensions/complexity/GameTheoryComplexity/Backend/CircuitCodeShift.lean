module

public import GameTheoryComplexity.Backend.CircuitFormat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

@[expose] public section

/-! Serialized circuit relocation preserves the concrete flags and unary fields.
The total scanner processes only the declared gate count. Its native machine
captures the offset ruler and bounds the accumulated output on arbitrary words.
-/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM

/-- The leading unary field, excluding its terminator. -/
def circuitUnaryPrefix (bits : List Bool) : List Bool :=
  bits.take (bits.idxOf false)

/-- A scanned unary field never exceeds its containing word. -/
theorem circuitUnaryPrefix_length_le (bits : List Bool) :
    (circuitUnaryPrefix bits).length ≤ bits.length := by
  simp only [circuitUnaryPrefix, List.length_take]
  exact Nat.min_le_right _ _

/-- Scan a unary prefix in polynomial time, including an unterminated field. -/
@[fun_prop] theorem circuitUnaryPrefix_polyTime {Input : Type} {input : Input ↪ List Bool}
    {bits : Input → List Bool} (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => circuitUnaryPrefix (bits a)) input encBits :=
  ComputableInPolyTime.bitsTakeWithInput hbits
    (ComputableInPolyTime.idxOfWithInput
      (ComputableInPolyTime.bitsToList.comp hbits) (ComputableInPolyTime.const false))

/-- Skip one unary reference and its terminator, if present. -/
def circuitUnaryRest (bits : List Bool) : List Bool :=
  bits.drop ((circuitUnaryPrefix bits).length + 1)

/-- The shifted serialization of the first gate in a stream. -/
def circuitShiftGate (ruler bits : List Bool) : List Bool :=
  let first := bits.drop 3
  let second := circuitUnaryRest first
  bits.take 3 ++ List.replicate ruler.length true ++
    first.take ((circuitUnaryPrefix first).length + 1) ++
    List.replicate ruler.length true ++
    second.take ((circuitUnaryPrefix second).length + 1)

/-- The unconsumed stream after its first gate. -/
def circuitGateRest (bits : List Bool) : List Bool :=
  circuitUnaryRest (circuitUnaryRest (bits.drop 3))

/-- A scan step consumes one gate and appends its relocated bytes. -/
def circuitShiftStep (ruler : List Bool) (state : List Bool × List Bool) :
    List Bool × List Bool :=
  (circuitGateRest state.1, state.2 ++ circuitShiftGate ruler state.1)

/-- Relocate a declared serialized circuit using a unary wire-offset ruler. -/
def shiftCircuitCode (ruler code : List Bool) : List Bool :=
  let count := circuitUnaryPrefix code
  count ++ [false] ++
    ((circuitShiftStep ruler)^[count.length] (circuitUnaryRest code, [])).2

/-- Skipping a unary field charges the complete containing word. -/
@[fun_prop] theorem circuitUnaryRest_polyTime {Input : Type} {input : Input ↪ List Bool}
    {bits : Input → List Bool} (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => circuitUnaryRest (bits a)) input encBits :=
  ComputableInPolyTime.bitsDropWithInput hbits
    (ComputableInPolyTime.unary_succ.comp
      (ComputableInPolyTime.length_bits_comp (circuitUnaryPrefix_polyTime hbits)))

/-- Gate skipping is polynomial-time on arbitrary, possibly truncated fields. -/
@[fun_prop] theorem circuitGateRest_polyTime {Input : Type} {input : Input ↪ List Bool}
    {bits : Input → List Bool} (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => circuitGateRest (bits a)) input encBits :=
  circuitUnaryRest_polyTime (circuitUnaryRest_polyTime
    (ComputableInPolyTime.bitsDropWithInput hbits (ComputableInPolyTime.const 3)))

/-- Relocating a gate charges the ruler padding and both scanned reference fields. -/
@[fun_prop] theorem circuitShiftGate_polyTime {Input : Type} {input : Input ↪ List Bool}
    {ruler bits : Input → List Bool}
    (hruler : ComputableInPolyTime ruler input encBits)
    (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => circuitShiftGate (ruler a) (bits a)) input encBits := by
  have hhead := ComputableInPolyTime.bitsTakeWithInput hbits (ComputableInPolyTime.const 3)
  have hfirst := ComputableInPolyTime.bitsDropWithInput hbits (ComputableInPolyTime.const 3)
  have hsecond := circuitUnaryRest_polyTime hfirst
  have hpadding := (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.length_bits_comp hruler)
  have hleft := ComputableInPolyTime.bitsTakeWithInput hfirst
    (ComputableInPolyTime.unary_succ.comp
      (ComputableInPolyTime.length_bits_comp (circuitUnaryPrefix_polyTime hfirst)))
  have hright := ComputableInPolyTime.bitsTakeWithInput hsecond
    (ComputableInPolyTime.unary_succ.comp
      (ComputableInPolyTime.length_bits_comp (circuitUnaryPrefix_polyTime hsecond)))
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsAppend hhead hpadding) hleft)
      hpadding) hright

private theorem circuitShiftStep_polyTime :
    ComputableInPolyTime
      (fun p : List Bool × (List Bool × List Bool) => circuitShiftStep p.1 p.2)
      (encPair encBits (encPair encBits encBits)) (encPair encBits encBits) := by
  have hruler := ComputableInPolyTime.fst encBits (encPair encBits encBits)
  have hstream := (ComputableInPolyTime.snd encBits (encPair encBits encBits)).fst'
  have houtput := (ComputableInPolyTime.snd encBits (encPair encBits encBits)).snd'
  exact (circuitGateRest_polyTime hstream).prod
    (ComputableInPolyTime.bitsAppend houtput (circuitShiftGate_polyTime hruler hstream))

/-- Skipping a gate only consumes input, including truncated encodings. -/
theorem circuitGateRest_length_le (bits : List Bool) :
    (circuitGateRest bits).length ≤ bits.length := by
  simp only [circuitGateRest, circuitUnaryRest, List.length_drop]
  omega

private theorem circuitShiftGate_length_le (ruler bits : List Bool) :
    (circuitShiftGate ruler bits).length ≤ 3 + 2 * ruler.length + 2 * bits.length := by
  have hsecond : (circuitUnaryRest (bits.drop 3)).length ≤ bits.length := by
    simp only [circuitUnaryRest, List.length_drop]
    omega
  have hhead := List.length_take_le 3 bits
  have hleft : ((bits.drop 3).take ((circuitUnaryPrefix (bits.drop 3)).length + 1)).length ≤
      bits.length := by
    simp only [List.length_take, List.length_drop]
    omega
  have hright : ((circuitUnaryRest (bits.drop 3)).take
      ((circuitUnaryPrefix (circuitUnaryRest (bits.drop 3))).length + 1)).length ≤
      bits.length := by
    simp only [List.length_take]
    omega
  simp only [circuitShiftGate, List.length_append, List.length_replicate]
  omega

private theorem shiftStep_iterate_bound (ruler stream : List Bool) (i : ℕ) :
    ∃ rest output,
      (circuitShiftStep ruler)^[i] (stream, []) = (rest, output) ∧
      rest.length ≤ stream.length ∧
      output.length ≤ i * (3 + 2 * ruler.length + 2 * stream.length) := by
  induction i with
  | zero => exact ⟨stream, [], rfl, le_rfl, by simp⟩
  | succ i ih =>
    obtain ⟨rest, output, heq, hrest, hout⟩ := ih
    refine ⟨circuitGateRest rest, output ++ circuitShiftGate ruler rest, ?_,
      (circuitGateRest_length_le rest).trans hrest, ?_⟩
    · rw [Function.iterate_succ_apply', heq]
      rfl
    · have hg := circuitShiftGate_length_le ruler rest
      rw [List.length_append, Nat.succ_mul]
      omega

/-- Uniform relocation charges the captured ruler and every accumulated output byte. -/
@[fun_prop] theorem shiftCircuitCode_polyTime {Input : Type} {input : Input ↪ List Bool}
    {ruler code : Input → List Bool}
    (hruler : ComputableInPolyTime ruler input encBits)
    (hcode : ComputableInPolyTime code input encBits) :
    ComputableInPolyTime (fun a => shiftCircuitCode (ruler a) (code a)) input encBits := by
  have hprefix := circuitUnaryPrefix_polyTime hcode
  have hcount := ComputableInPolyTime.length_bits_comp hprefix
  have hinit : ComputableInPolyTime
      (fun a : Input => (circuitUnaryRest (code a), ([] : List Bool)))
      input (encPair encBits encBits) :=
    (circuitUnaryRest_polyTime hcode).prod (ComputableInPolyTime.const [])
  have hr := hruler.polyBounded_length
  have hc := hcode.polyBounded_length
  have hsize : PolyBounded (fun a => (input a).length)
      (fun a => 2 * (code a).length + 1 + (code a).length *
        (3 + 2 * (ruler a).length + 2 * (code a).length)) :=
    (((PolyBounded.const 2).mul hc).add (PolyBounded.const 1)).add
      (hc.mul (((PolyBounded.const 3).add ((PolyBounded.const 2).mul hr)).add
        ((PolyBounded.const 2).mul hc)))
  have hloop : ComputableInPolyTime
      (fun a => (circuitShiftStep (ruler a))^[(circuitUnaryPrefix (code a)).length]
        (circuitUnaryRest (code a), [])) input (encPair encBits encBits) :=
    ComputableInPolyTime.iterateWith hruler hcount hinit circuitShiftStep_polyTime hsize (by
      intro a i hi
      change i ≤ (circuitUnaryPrefix (code a)).length at hi
      obtain ⟨rest, output, heq, hrest, hout⟩ :=
        shiftStep_iterate_bound (ruler a) (circuitUnaryRest (code a)) i
      rw [heq]
      have hs : (circuitUnaryRest (code a)).length ≤ (code a).length := by
        simp only [circuitUnaryRest, List.length_drop]
        omega
      have hclock := circuitUnaryPrefix_length_le (code a)
      have hm : i * (3 + 2 * (ruler a).length + 2 * (circuitUnaryRest (code a)).length) ≤
          (code a).length * (3 + 2 * (ruler a).length + 2 * (code a).length) :=
        Nat.mul_le_mul (hi.trans hclock) (by omega)
      have hout' := hout.trans hm
      simp only [length_encPair, encBits_apply]
      omega)
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend hprefix (ComputableInPolyTime.const [false])) hloop.snd'

/-- Scanning a canonical unary field recovers its true ruler. -/
theorem circuitUnaryPrefix_encode (n : ℕ) (rest : List Bool) :
    circuitUnaryPrefix (CircuitFormat.encodeUnary n ++ rest) = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [CircuitFormat.encodeUnary, List.replicate_succ, circuitUnaryPrefix,
      List.idxOf_cons] using congrArg (List.cons true) ih

/-- Skipping a canonical unary field recovers the exact unconsumed suffix. -/
theorem circuitUnaryRest_encode (n : ℕ) (rest : List Bool) :
    circuitUnaryRest (CircuitFormat.encodeUnary n ++ rest) = rest := by
  rw [circuitUnaryRest, circuitUnaryPrefix_encode]
  simp [CircuitFormat.encodeUnary, List.drop_append]

/-- A canonically encoded native gate list records exactly its gate count. -/
theorem circuitUnaryPrefix_encode_length
    (gates : List (CircuitFormat.signature.Op × List ℕ))
    (harity : ∀ gate ∈ gates, gate.2.length = 2) :
    (circuitUnaryPrefix (CircuitFormat.encode gates)).length = gates.length := by
  have hall : gates.all (fun gate => gate.2.length == 2) = true := by
    apply List.all_eq_true.mpr
    intro gate hg
    simp [harity gate hg]
  rw [CircuitFormat.encode, ite_eq_left hall, circuitUnaryPrefix_encode, List.length_replicate]

private theorem decodedGateCount {count : ℕ} {bits suffix : List Bool}
    {gates : List (CircuitFormat.signature.Op × List ℕ)}
    (h : CircuitFormat.decodeGates? count bits = some (gates, suffix)) :
    gates.length = count := by
  induction count generalizing bits gates suffix with
  | zero =>
    change some ([], bits) = some (gates, suffix) at h
    cases h
    rfl
  | succ count ih =>
    cases hgate : CircuitFormat.decodeGatePrefix? bits with
    | none => simp [CircuitFormat.decodeGates?, hgate] at h
    | some parsed =>
      rcases parsed with ⟨gate, rest⟩
      cases htail : CircuitFormat.decodeGates? count rest with
      | none => simp [CircuitFormat.decodeGates?, hgate, htail] at h
      | some parsed =>
        rcases parsed with ⟨tail, rest'⟩
        have heq : (gate :: tail, rest') = (gates, suffix) := by
          simpa only [CircuitFormat.decodeGates?, hgate, bind, Option.bind_some, htail,
            Option.pure_def, Option.some.injEq] using h
        cases heq
        simpa only [List.length_cons] using congrArg Nat.succ (ih htail)

/-- Successful strict decoding identifies the scanned header with the gate count. -/
theorem circuitUnaryPrefix_length_of_decode (code : List Bool)
    (gates : List (CircuitFormat.signature.Op × List ℕ))
    (hd : CircuitFormat.decode? code = some gates) :
    (circuitUnaryPrefix code).length = gates.length := by
  cases hprefix : CircuitFormat.decodeUnaryPrefix? code with
  | none => simp [CircuitFormat.decode?, hprefix] at hd
  | some parsed =>
    rcases parsed with ⟨count, rest⟩
    cases hscan : CircuitFormat.decodeGates? count rest with
    | none => simp [CircuitFormat.decode?, hprefix, hscan] at hd
    | some parsed =>
      rcases parsed with ⟨decoded, suffix⟩
      cases suffix with
      | nil =>
        have heq : decoded = gates := by
          simpa only [CircuitFormat.decode?, hprefix, hscan, Option.some.injEq] using hd
        subst decoded
        have hlength := decodedGateCount hscan
        have hcode := CircuitFormat.decodeUnaryPrefix?_sound hprefix
        rw [hcode, circuitUnaryPrefix_encode, List.length_replicate]
        exact hlength.symm
      | cons b suffix => simp [CircuitFormat.decode?, hprefix, hscan] at hd

end GameTheory.Complexity.Backend
