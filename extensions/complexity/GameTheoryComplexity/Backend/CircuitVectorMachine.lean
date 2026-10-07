import Complexitylib.Circuits.Encoding.Machine.Core
import Complexitylib.Classes.PCP.Internal.BitwiseFP
import Complexitylib.Classes.P.Preimage
import Complexitylib.Classes.P.Pairing
import Mathlib.Data.List.OfFn

/-! Serialized vectors of Boolean circuits are evaluated one output bit at a time.
Every scalar code uses the ordinary tagged circuit codec. Malformed scalar codes
denote the zero bit. The number of outputs is the length of the supplied vertex,
so evaluation never enumerates the exponentially larger space of vertices. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity

/-- A right-nested list of self-delimiting tagged circuit codewords. -/
def encodeVectorCodes : List (List Bool) → List Bool
  | [] => []
  | code :: codes => pair code (encodeVectorCodes codes)

/-- Serializing a circuit vector adds only linear framing overhead. -/
theorem encodeVectorCodes_length (codes : List (List Bool)) :
    (encodeVectorCodes codes).length = 2 * (codes.map List.length).sum +
      2 * codes.length := by
  induction codes with
  | nil => rfl
  | cons code codes ih => simp [encodeVectorCodes, pair_length, ih]; omega

/-- Locate one output circuit using a unary position, defaulting a missing code to empty. -/
def circuitVectorCodeAt (codes : List Bool) (i : ℕ) : List Bool :=
  pairFst (pairSnd^[i] codes)

private theorem pairSnd_iterate_nil (i : ℕ) : pairSnd^[i] [] = [] := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- Indexed decoding agrees exactly with the canonical list encoding. -/
theorem circuitVectorCodeAt_encode (codes : List (List Bool)) (i : ℕ) :
    circuitVectorCodeAt (encodeVectorCodes codes) i = (codes[i]?).getD [] := by
  induction codes generalizing i with
  | nil => simp [circuitVectorCodeAt, encodeVectorCodes, pairSnd_iterate_nil, pairFst]
  | cons code codes ih =>
      cases i with
      | zero => simp [circuitVectorCodeAt, encodeVectorCodes]
      | succ i =>
          simpa only [circuitVectorCodeAt, encodeVectorCodes,
            Function.iterate_succ_apply, pairSnd_pair, List.getElem?_cons_succ] using ih i

/-- Total evaluation with exactly one output per vertex bit. -/
def evaluateCircuitVector (codes vertex : List Bool) : List Bool :=
  (List.range vertex.length).map fun i =>
    (CircuitCode.evalFamilyCode (circuitVectorCodeAt codes i) vertex).getD false

/-- The output width depends only on the input vertex width. -/
@[simp] theorem evaluateCircuitVector_length (codes vertex : List Bool) :
    (evaluateCircuitVector codes vertex).length = vertex.length := by
  simp [evaluateCircuitVector]

/-- Each canonical codeword is evaluated by the exact scalar circuit semantics. -/
theorem evaluateCircuitVector_encode (codes : List (List Bool)) (vertex : List Bool) :
    evaluateCircuitVector (encodeVectorCodes codes) vertex =
      (List.range vertex.length).map fun i =>
        (CircuitCode.evalFamilyCode ((codes[i]?).getD []) vertex).getD false := by
  simp only [evaluateCircuitVector, circuitVectorCodeAt_encode]

/-- A vector of typed circuits yields precisely its vector of semantic answers. -/
theorem evaluateCircuitVector_encode_families {n : ℕ}
    (families : Fin n → CircuitFamily Basis.andOr2) (vertex : BitString n) :
    evaluateCircuitVector
      (encodeVectorCodes (List.ofFn fun i => (families i).encodeAt n)) vertex.toList =
        List.ofFn fun i => (families i).function n vertex := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hin : i < n := by simpa using hj
    simp [evaluateCircuitVector, circuitVectorCodeAt_encode, hin]

private theorem pairSnd_iterate_length_le (bits : List Bool) (i : ℕ) :
    (pairSnd^[i] bits).length ≤ bits.length := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact (pairSnd_length_le _).trans ih

private def vectorCircuitQuery (z : List Bool) : List Bool :=
  pair (circuitVectorCodeAt (pairFst (pairFst z)) (pairSnd z).length)
    (pairSnd (pairFst z))

private theorem vectorCircuitQuery_mem_FP : vectorCircuitQuery ∈ FP := by
  have hcodes : (fun z => pairFst (pairFst z)) ∈ FP :=
    mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have htail : (fun z => pairSnd^[(pairSnd z).length] (pairFst (pairFst z))) ∈ FP :=
    Cobham.iterate_mem_FP pairSnd_mem_FP hcodes pairSnd_mem_FP hcodes
      (fun z i _ => pairSnd_iterate_length_le _ i)
  exact Cobham.pairFn_mem_FP (mem_FP_comp htail pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

private theorem scalarCircuitEval_mem_P : CircuitCode.circuitEvalLanguage ∈ P := by
  apply Set.mem_iUnion.mpr
  exact ⟨2, CircuitCode.Machine.workTapeCount, CircuitCode.Machine.evalFamilyTM,
    CircuitCode.Machine.evalFamilyTime, CircuitCode.Machine.evalFamilyTM_decidesInTime,
    CircuitCode.Machine.evalFamilyTime_bigO_quadratic⟩

/-- The vector evaluator is computed by a polynomial-time string machine.
The machine appends one output bit per input bit, using the verified serialized
circuit evaluator after polynomial-time indexed code selection. -/
theorem evaluateCircuitVector_pair_mem_FP :
    (fun z => evaluateCircuitVector (pairFst z) (pairSnd z)) ∈ FP := by
  have hlength : (fun z => List.replicate (pairSnd z).length true) ∈ FP :=
    mem_FP_comp pairSnd_mem_FP unaryLength_mem_FP
  apply bitwise_mem_FP_of_mem_P hlength
    (mem_P_preimage vectorCircuitQuery_mem_FP scalarCircuitEval_mem_P)
  intro x i
  change vectorCircuitQuery (pair x (List.replicate i true)) ∈
      CircuitCode.circuitEvalLanguage ↔ _
  simp only [vectorCircuitQuery, pairFst_pair, pairSnd_pair, List.length_replicate,
    CircuitCode.circuitEvalLanguage, Set.mem_ofPred_eq, CircuitCode.evalFamilyPair?_pair]
  cases CircuitCode.evalFamilyCode (circuitVectorCodeAt (pairFst x) i) (pairSnd x) with
  | none => simp
  | some b => cases b <;> simp

/-- Circuit vector evaluation can be composed inside bounded word computations. -/
theorem evaluateCircuitVector_cobham :
    Cobham (fun v : Fin 2 → List Bool => evaluateCircuitVector (v 0) (v 1)) := by
  have h := Cobham.comp (FP_subset_CobhamFP evaluateCircuitVector_pair_mem_FP)
    (fun _ : Fin 1 => Cobham.comp₂ Cobham.pairing
      (Cobham.proj (0 : Fin 2)) (Cobham.proj 1))
  exact h.of_eq fun v => by simp

/-- Polynomial-time evaluation of two explicit word arguments, with no conditions
on well-formedness of their encodings. -/
theorem evaluateCircuitVector_mem_FPn :
    Cobham.FPn (fun v : Fin 2 → List Bool => evaluateCircuitVector (v 0) (v 1)) :=
  Cobham.cobham_iff_FPn.mp evaluateCircuitVector_cobham

end GameTheory.Complexity.Backend
