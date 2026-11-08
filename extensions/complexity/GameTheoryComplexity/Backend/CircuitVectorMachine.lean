module

public import GameTheoryComplexity.Backend.CircuitFormat
public import GameTheoryComplexity.Backend.CircuitWords
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration

@[expose] public section

/-! Serialized vectors of Boolean circuits are evaluated one output bit at a time.
Each scalar code uses the tagged circuit byte format. Malformed scalar codes
denote the zero bit. The output width is the supplied vertex's bit length, so
evaluation never enumerates the exponentially larger space of vertices. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM
open ComputableInPolyTime

/-- A right-nested list of self-delimiting tagged circuit codewords. -/
def encodeVectorCodes : List (List Bool) → List Bool
  | [] => []
  | code :: codes => CircuitWords.encodePair code (encodeVectorCodes codes)

/-- Serializing a circuit vector adds only linear framing overhead. -/
theorem encodeVectorCodes_length (codes : List (List Bool)) :
    (encodeVectorCodes codes).length = 2 * (codes.map List.length).sum +
      2 * codes.length := by
  induction codes with
  | nil => rfl
  | cons code codes ih =>
    simp only [encodeVectorCodes, CircuitWords.encodePair_length, ih, List.map_cons,
      List.sum_cons, List.length_cons]
    omega

/-- Locate one output circuit using a unary position, defaulting a missing code to empty. -/
def circuitVectorCodeAt (codes : List Bool) (i : ℕ) : List Bool :=
  CircuitWords.first (CircuitWords.rest^[i] codes)

private theorem circuitWords_rest_iterate_nil (i : ℕ) : CircuitWords.rest^[i] [] = [] := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- Indexed decoding agrees exactly with the canonical list encoding. -/
theorem circuitVectorCodeAt_encode (codes : List (List Bool)) (i : ℕ) :
    circuitVectorCodeAt (encodeVectorCodes codes) i = (codes[i]?).getD [] := by
  induction codes generalizing i with
  | nil =>
    simp [circuitVectorCodeAt, encodeVectorCodes, circuitWords_rest_iterate_nil,
      CircuitWords.first, CircuitWords.splitPair]
  | cons code codes ih =>
    cases i with
    | zero => simp [circuitVectorCodeAt, encodeVectorCodes]
    | succ i =>
      simpa only [circuitVectorCodeAt, encodeVectorCodes,
        Function.iterate_succ_apply, CircuitWords.rest_encodePair,
        List.getElem?_cons_succ] using ih i

/-- Total evaluation with exactly one output per vertex bit. -/
def evaluateCircuitVector (codes vertex : List Bool) : List Bool :=
  (List.range vertex.length).map fun i =>
    (CircuitFormat.evalTagged? (circuitVectorCodeAt codes i) vertex).getD false

/-- The output width depends only on the input vertex width. -/
@[simp] theorem evaluateCircuitVector_length (codes vertex : List Bool) :
    (evaluateCircuitVector codes vertex).length = vertex.length := by
  simp [evaluateCircuitVector]

/-- Canonical codewords are evaluated by the exact scalar byte semantics. -/
theorem evaluateCircuitVector_encode (codes : List (List Bool)) (vertex : List Bool) :
    evaluateCircuitVector (encodeVectorCodes codes) vertex =
      (List.range vertex.length).map fun i =>
        (CircuitFormat.evalTagged? ((codes[i]?).getD []) vertex).getD false := by
  simp only [evaluateCircuitVector, circuitVectorCodeAt_encode]

private theorem circuitWords_rest_iterate_length_le (bits : List Bool) (i : ℕ) :
    (CircuitWords.rest^[i] bits).length ≤ bits.length := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (CircuitWords.rest_length_le _).trans ih

/-- Each scalar frame can be concatenated independently. -/
theorem encodeVectorCodes_eq_flatMap (codes : List (List Bool)) :
    encodeVectorCodes codes = codes.flatMap (fun code => CircuitWords.encodePair code []) := by
  induction codes with
  | nil => rfl
  | cons code codes ih =>
    simp only [encodeVectorCodes, List.flatMap_cons, CircuitWords.encodePair, List.append_nil,
      List.append_assoc, ih]

/-- Framing every scalar code is polynomial in the encoded list of codewords. -/
@[fun_prop] theorem encodeVectorCodes_polyTime :
    ComputableInPolyTime encodeVectorCodes (encList encBits) encBits := by
  have hbody : ComputableInPolyTime
      (fun p : List (List Bool) × List Bool => CircuitWords.encodePair p.2 [])
      (encPair (encList encBits) encBits) encBits :=
    CircuitWords.encodePair_polyTime.comp
      ((snd (encList encBits) encBits).prod (const []))
  have h := flatMapToBitsWithInput
    (list := fun codes : List (List Bool) => codes)
    (f := fun (_ : List (List Bool)) (code : List Bool) => CircuitWords.encodePair code [])
    (id' (encIn := encList encBits)) hbody
  have heq : encodeVectorCodes =
      fun codes => codes.flatMap (fun code => CircuitWords.encodePair code []) :=
    funext encodeVectorCodes_eq_flatMap
  rw [heq]
  exact h

/-- Locating a scalar code has polynomial cost in its unary index and codeword. -/
@[fun_prop] theorem circuitVectorCodeAt_polyTime
    {α : Type} {encIn : α ↪ List Bool} {codes : α → List Bool} {index : α → ℕ}
    (hcodes : ComputableInPolyTime codes encIn encBits)
    (hindex : ComputableInPolyTime index encIn encUnary) :
    ComputableInPolyTime (fun a => circuitVectorCodeAt (codes a) (index a)) encIn encBits := by
  have htail : ComputableInPolyTime
      (fun a => CircuitWords.rest^[index a] (codes a)) encIn encBits :=
    iterate hindex hcodes CircuitWords.rest_polyTime
      (bound := fun a => (codes a).length) hcodes.polyBounded_length
      (fun a i _ => circuitWords_rest_iterate_length_le (codes a) i)
  exact CircuitWords.first_polyTime.comp htail

/-- Evaluating a serialized vector charges the vertex-width map and every scalar parser. -/
@[fun_prop] theorem evaluateCircuitVector_polyTime
    {α : Type} {encIn : α ↪ List Bool} {codes vertex : α → List Bool}
    (hcodes : ComputableInPolyTime codes encIn encBits)
    (hvertex : ComputableInPolyTime vertex encIn encBits) :
    ComputableInPolyTime (fun a => evaluateCircuitVector (codes a) (vertex a)) encIn encBits := by
  have hrange : ComputableInPolyTime (fun a => List.range (vertex a).length)
      encIn (encList encUnary) := range.comp (length_bits.comp hvertex)
  have hcodes' : ComputableInPolyTime (fun p : α × ℕ => codes p.1)
      (encPair encIn encUnary) encBits := hcodes.comp (fst encIn encUnary)
  have hvertex' : ComputableInPolyTime (fun p : α × ℕ => vertex p.1)
      (encPair encIn encUnary) encBits := hvertex.comp (fst encIn encUnary)
  have hscalar : ComputableInPolyTime
      (fun p : α × ℕ => circuitVectorCodeAt (codes p.1) p.2)
      (encPair encIn encUnary) encBits :=
    circuitVectorCodeAt_polyTime hcodes' (snd encIn encUnary)
  have hvalue : ComputableInPolyTime
      (fun p : α × ℕ => CircuitFormat.evalTagged?
        (circuitVectorCodeAt (codes p.1) p.2) (vertex p.1))
      (encPair encIn encUnary) (encOption encBool) :=
    CircuitFormat.computableInPolyTime_evalTagged.comp (hscalar.prod hvertex')
  have hbody : ComputableInPolyTime
      (fun p : α × ℕ => (CircuitFormat.evalTagged?
        (circuitVectorCodeAt (codes p.1) p.2) (vertex p.1)).getD false)
      (encPair encIn encUnary) encBool := optionGetDWithInput hvalue (const false)
  exact mapToBitsWithInput
    (f := fun (a : α) (i : ℕ) =>
      (CircuitFormat.evalTagged? (circuitVectorCodeAt (codes a) i) (vertex a)).getD false)
    hrange hbody

end GameTheory.Complexity.Backend
