import GameTheoryComplexity.Backend.CircuitCodeShiftCorrectness
import GameTheoryComplexity.Backend.CircuitPrefixEmitter
import GameTheoryComplexity.Backend.CircuitPrefixRestriction

/-! Circuit prefix compilation on serialized raw circuits. The emitter agrees
exactly with the raw hardwiring construction on canonical source codes. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham _root_.Complexity.CircuitCode

/-- Emit a prefix-restricted circuit. Its correctness contract requires a canonical
source code; a separate syntax check handles arbitrary serialized inputs. -/
def emitRestrictedCircuitCode (ruler seed code : List Bool) : List Bool :=
  List.replicate (seed.length + ruler.length) true ++ circuitUnaryPrefix code ++ [false] ++
    seedGateCodes seed ++ liveCopyGateCodes ruler ++
    circuitUnaryRest (shiftCircuitCode ruler code)

/-- The emitted bytes are exactly the canonical raw prefix-restriction code. -/
theorem emitRestrictedCircuitCode_encode (ruler seed : List Bool) (circuit : RawCircuit) :
    emitRestrictedCircuitCode ruler seed circuit.encode =
      (rawPrefixRestriction ruler.length seed circuit).encode := by
  rw [emitRestrictedCircuitCode, shiftCircuitCode_encode]
  simp only [RawCircuit.encode]
  rw [circuitUnaryPrefix_encode, circuitUnaryRest_encode]
  simp only [rawPrefixRestriction, seedGateCodes, liveCopyGateCodes, NatCode.encode,
    List.length_append, List.length_map, List.length_range, RawCircuit.length_shift,
    List.flatMap_append, List.replicate_add, List.append_assoc]

/-- Hardwiring preserves exact optional evaluation of canonical nonempty circuits,
including rejection of forward and out-of-range wire references. -/
theorem emitRestrictedCircuitCode_eval (ruler seed input : List Bool) (circuit : RawCircuit)
    (hn : 0 < ruler.length) (hi : input.length = ruler.length) (hc : circuit ≠ []) :
    evalCode ruler.length (emitRestrictedCircuitCode ruler seed circuit.encode) input =
      evalCode (seed.length + ruler.length) circuit.encode (seed ++ input) := by
  rw [emitRestrictedCircuitCode_encode]
  have hd (c : RawCircuit) : RawCircuit.decode? c.encode = some c :=
    (RawCircuit.decode?_eq_some_iff _ _).mpr rfl
  simp only [evalCode, hi, List.length_append, ↓reduceIte, hd]
  exact rawPrefixRestriction_eval _ _ _ _ hn hi hc

/-- Prefix compilation composes polynomial-time rulers, seeds and source codes. -/
theorem emitRestrictedCircuitCodeFn_mem_FP {r s c : List Bool → List Bool}
    (hr : r ∈ FP) (hs : s ∈ FP) (hc : c ∈ FP) :
    (fun z => emitRestrictedCircuitCode (r z) (s z) (c z)) ∈ FP := by
  have hlen := mem_FP_comp (appendFn_mem_FP hs hr) unaryLength_mem_FP
  have hcount := mem_FP_comp hc circuitUnaryPrefix_mem_FP
  have hprefix := appendFn_mem_FP
    (mem_FP_comp hs seedGateCodes_mem_FP) (mem_FP_comp hr liveCopyGateCodes_mem_FP)
  have hshift := mem_FP_comp (pairFn_mem_FP hr hc) shiftCircuitCode_pair_mem_FP
  have hbody := mem_FP_comp hshift circuitUnaryRest_mem_FP
  have hfull := appendFn_mem_FP
    (appendFn_mem_FP (appendFn_mem_FP hlen hcount) (constFn_mem_FP [false]))
    (appendFn_mem_FP hprefix hbody)
  simpa only [emitRestrictedCircuitCode, Function.comp_def, List.length_append,
    pairFst_pair, pairSnd_pair, List.append_assoc] using hfull

end GameTheory.Complexity.Backend
