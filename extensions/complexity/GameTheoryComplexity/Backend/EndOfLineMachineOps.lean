import GameTheoryComplexity.Backend.EndOfLineProblem
import Complexitylib.Classes.Containments.Internal.FPBridge

/-! Polynomial-time pointer composition and one-bit controls shared by the
End-of-Line verifiers. -/

namespace GameTheory.Complexity.Backend.EndOfLineMachineOps

open _root_.Complexity _root_.Complexity.Cobham

/-- Select between polynomial-time word producers using a computed flag. -/
theorem selectFn_mem_FP {flag yes no : List Bool → List Bool}
    (hf : flag ∈ FP) (hy : yes ∈ FP) (hn : no ∈ FP) :
    (fun z => caseBit₀ (flag z) (yes z) (no z)) ∈ FP :=
  CobhamFP_subset_FP (Cobham.iteFn (FP_subset_CobhamFP hf)
    (FP_subset_CobhamFP hy) (FP_subset_CobhamFP hn))

theorem vectorFn_mem_FP {codes vertex : List Bool → List Bool}
    (hc : codes ∈ FP) (hv : vertex ∈ FP) :
    (fun z => evaluateCircuitVector (codes z) (vertex z)) ∈ FP := by
  have h := mem_FP_comp (pairFn_mem_FP hc hv) evaluateCircuitVector_pair_mem_FP
  simpa only [Function.comp_def, pairFst_pair, pairSnd_pair] using h

theorem predecessorFn_mem_FP {input vertex : List Bool → List Bool}
    (hi : input ∈ FP) (hv : vertex ∈ FP) :
    (fun z => endOfLinePredecessor (input z) (vertex z)) ∈ FP :=
  vectorFn_mem_FP (mem_FP_comp (mem_FP_comp hi pairSnd_mem_FP) pairFst_mem_FP) hv

theorem successorFn_mem_FP {input vertex : List Bool → List Bool}
    (hi : input ∈ FP) (hv : vertex ∈ FP) :
    (fun z => endOfLineSuccessor (input z) (vertex z)) ∈ FP :=
  vectorFn_mem_FP (mem_FP_comp (mem_FP_comp hi pairSnd_mem_FP) pairSnd_mem_FP) hv

theorem originFn_mem_FP {input : List Bool → List Bool} (hi : input ∈ FP) :
    (fun z => endOfLineOrigin (input z)) ∈ FP := by
  have h := mulLenFn_mem_FP (constFn_mem_FP [false]) (mem_FP_comp hi pairFst_mem_FP)
  simpa only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul, Function.comp_def,
    endOfLineOrigin, endOfLineWidth] using h

theorem negFlag_accept {x : List Bool} (hx : x = [true] ∨ x = [false]) :
    notBit x = [true] ↔ ¬x = [true] := by
  rcases hx with rfl | rfl <;> decide

theorem negFlag_flag {x : List Bool} (hx : x = [true] ∨ x = [false]) :
    notBit x = [true] ∨ notBit x = [false] := by
  rcases hx with rfl | rfl <;> decide

theorem zeroWords_eq_iff (a b : ℕ) :
    List.replicate a false = List.replicate b false ↔ a = b := by
  constructor
  · intro h
    simpa only [List.length_replicate] using congrArg List.length h
  · rintro rfl
    rfl

/-- Check a nontrivial outgoing pointer and agreement of its inverse. -/
def successorFlag (input vertex : List Bool) : List Bool :=
  andBit (notBit (eqFlag (endOfLineSuccessor input vertex) vertex))
    (eqFlag (endOfLinePredecessor input (endOfLineSuccessor input vertex)) vertex)

/-- Check a nontrivial incoming pointer and agreement of its inverse. -/
def predecessorFlag (input vertex : List Bool) : List Bool :=
  andBit (notBit (eqFlag (endOfLinePredecessor input vertex) vertex))
    (eqFlag (endOfLineSuccessor input (endOfLinePredecessor input vertex)) vertex)

theorem successorFlag_accept (input vertex : List Bool) :
    successorFlag input vertex = [true] ↔ GameTheory.Math.EndOfLine.HasSuccessor
      (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
  rw [successorFlag, andBit_eq_true_iff (negFlag_flag (eqFlag_flag _ _))
    (eqFlag_flag _ _), negFlag_accept (eqFlag_flag _ _)]
  simp only [eqFlag_eq_true_iff, GameTheory.Math.EndOfLine.HasSuccessor]

theorem predecessorFlag_accept (input vertex : List Bool) :
    predecessorFlag input vertex = [true] ↔ GameTheory.Math.EndOfLine.HasPredecessor
      (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
  rw [predecessorFlag, andBit_eq_true_iff (negFlag_flag (eqFlag_flag _ _))
    (eqFlag_flag _ _), negFlag_accept (eqFlag_flag _ _)]
  simp only [eqFlag_eq_true_iff, GameTheory.Math.EndOfLine.HasPredecessor]

theorem successorFlagFn_mem_FP {input vertex : List Bool → List Bool}
    (hi : input ∈ FP) (hv : vertex ∈ FP) :
    (fun z => successorFlag (input z) (vertex z)) ∈ FP := by
  have hs := successorFn_mem_FP hi hv
  exact andBitFn_mem_FP (notBitFn_mem_FP (eqFlagFn_mem_FP hs hv))
    (eqFlagFn_mem_FP (predecessorFn_mem_FP hi hs) hv)

theorem predecessorFlagFn_mem_FP {input vertex : List Bool → List Bool}
    (hi : input ∈ FP) (hv : vertex ∈ FP) :
    (fun z => predecessorFlag (input z) (vertex z)) ∈ FP := by
  have hp := predecessorFn_mem_FP hi hv
  exact andBitFn_mem_FP (notBitFn_mem_FP (eqFlagFn_mem_FP hp hv))
    (eqFlagFn_mem_FP (successorFn_mem_FP hi hp) hv)

end GameTheory.Complexity.Backend.EndOfLineMachineOps
