import GameTheoryComplexity.Backend.EndOfLineMachineOps
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.P.NormalForm

/-! A polynomial-time verifier for succinct End-of-Line. It evaluates only the
source and the candidate's immediate neighbors, checks the exact witness width,
and rejects noncanonical paired verifier inputs. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open EndOfLineMachineOps

/-- Check the distinguished source and agreement across its first edge. -/
def endOfLineSourceFlag (input : List Bool) : List Bool :=
  andBit
    (eqFlag (endOfLinePredecessor input (endOfLineOrigin input)) (endOfLineOrigin input))
    (andBit
      (notBit (eqFlag (endOfLineSuccessor input (endOfLineOrigin input))
        (endOfLineOrigin input)))
      (eqFlag (endOfLinePredecessor input
        (endOfLineSuccessor input (endOfLineOrigin input))) (endOfLineOrigin input)))

theorem endOfLineSourceFlag_flag (input : List Bool) :
    endOfLineSourceFlag input = [true] ∨ endOfLineSourceFlag input = [false] :=
  andBit_flag _ _

theorem endOfLineSourceFlag_accept (input : List Bool) :
    endOfLineSourceFlag input = [true] ↔ endOfLineSourceValid input := by
  rw [endOfLineSourceFlag, andBit_eq_true_iff (eqFlag_flag _ _) (andBit_flag _ _),
    andBit_eq_true_iff (negFlag_flag (eqFlag_flag _ _)) (eqFlag_flag _ _),
    negFlag_accept (eqFlag_flag _ _)]
  simp only [eqFlag_eq_true_iff, endOfLineSourceValid]

/-- Exactly one consistent incident edge makes a candidate an endpoint. -/
def endOfLineEndpointFlag (input vertex : List Bool) : List Bool :=
  orBit (andBit (successorFlag input vertex) (notBit (predecessorFlag input vertex)))
    (andBit (predecessorFlag input vertex) (notBit (successorFlag input vertex)))

theorem endOfLineEndpointFlag_flag (input vertex : List Bool) :
    endOfLineEndpointFlag input vertex = [true] ∨
      endOfLineEndpointFlag input vertex = [false] :=
  orBit_flag (andBit_flag _ _) (andBit_flag _ _)

theorem endOfLineEndpointFlag_accept (input vertex : List Bool) :
    endOfLineEndpointFlag input vertex = [true] ↔ GameTheory.Math.EndOfLine.IsEndpoint
      (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
  have hs : successorFlag input vertex = [true] ∨
      successorFlag input vertex = [false] := andBit_flag _ _
  have hp : predecessorFlag input vertex = [true] ∨
      predecessorFlag input vertex = [false] := andBit_flag _ _
  rw [endOfLineEndpointFlag, orBit_eq_true_iff (andBit_flag _ _) (andBit_flag _ _),
    andBit_eq_true_iff hs (negFlag_flag hp), andBit_eq_true_iff hp (negFlag_flag hs),
    negFlag_accept hp, negFlag_accept hs]
  simp only [successorFlag_accept, predecessorFlag_accept, GameTheory.Math.EndOfLine.IsEndpoint]

/-- Check an endpoint witness or the designated invalid-source fallback. -/
def endOfLineVerdict (input witness : List Bool) : List Bool :=
  orBit
    (andBit (endOfLineSourceFlag input)
      (andBit (eqFlag (List.replicate witness.length false) (endOfLineOrigin input))
        (andBit (notBit (eqFlag witness (endOfLineOrigin input)))
          (endOfLineEndpointFlag input witness))))
    (andBit (notBit (endOfLineSourceFlag input)) (eqFlag witness []))

theorem endOfLineVerdict_flag (input witness : List Bool) :
    endOfLineVerdict input witness = [true] ∨ endOfLineVerdict input witness = [false] :=
  orBit_flag (andBit_flag _ _) (andBit_flag _ _)

theorem endOfLineVerdict_accept (input witness : List Bool) :
    endOfLineVerdict input witness = [true] ↔ endOfLineRelation input witness := by
  rw [endOfLineVerdict, orBit_eq_true_iff (andBit_flag _ _) (andBit_flag _ _),
    andBit_eq_true_iff (endOfLineSourceFlag_flag _) (andBit_flag _ _),
    andBit_eq_true_iff (eqFlag_flag _ _) (andBit_flag _ _),
    andBit_eq_true_iff (negFlag_flag (eqFlag_flag _ _)) (endOfLineEndpointFlag_flag _ _),
    andBit_eq_true_iff (negFlag_flag (endOfLineSourceFlag_flag _)) (eqFlag_flag _ _),
    negFlag_accept (eqFlag_flag _ _), negFlag_accept (endOfLineSourceFlag_flag _)]
  simp only [eqFlag_eq_true_iff, endOfLineSourceFlag_accept, endOfLineEndpointFlag_accept,
    endOfLineOrigin, zeroWords_eq_iff, endOfLineRelation]

theorem endOfLineSourceFlagFn_mem_FP {input : List Bool → List Bool} (hi : input ∈ FP) :
    (fun z => endOfLineSourceFlag (input z)) ∈ FP := by
  have ho := originFn_mem_FP hi
  have hs := successorFn_mem_FP hi ho
  exact andBitFn_mem_FP (eqFlagFn_mem_FP (predecessorFn_mem_FP hi ho) ho)
    (andBitFn_mem_FP (notBitFn_mem_FP (eqFlagFn_mem_FP hs ho))
      (eqFlagFn_mem_FP (predecessorFn_mem_FP hi hs) ho))

private theorem endpointFlagFn_mem_FP {input vertex : List Bool → List Bool}
    (hi : input ∈ FP) (hv : vertex ∈ FP) :
    (fun z => endOfLineEndpointFlag (input z) (vertex z)) ∈ FP := by
  have hsflag := successorFlagFn_mem_FP hi hv
  have hpflag := predecessorFlagFn_mem_FP hi hv
  exact orBitFn_mem_FP (andBitFn_mem_FP hsflag (notBitFn_mem_FP hpflag))
    (andBitFn_mem_FP hpflag (notBitFn_mem_FP hsflag))

private theorem verdict_pair_mem_FP :
    (fun z => endOfLineVerdict (pairFst z) (pairSnd z)) ∈ FP := by
  have hi := pairFst_mem_FP
  have hv := pairSnd_mem_FP
  have ho := originFn_mem_FP hi
  have hsource := endOfLineSourceFlagFn_mem_FP hi
  have hzero : (fun z => List.replicate (pairSnd z).length false) ∈ FP := by
    simpa only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] using
      mulLenFn_mem_FP (constFn_mem_FP [false]) hv
  exact orBitFn_mem_FP
    (andBitFn_mem_FP hsource
      (andBitFn_mem_FP (eqFlagFn_mem_FP hzero ho)
        (andBitFn_mem_FP (notBitFn_mem_FP (eqFlagFn_mem_FP hv ho))
          (endpointFlagFn_mem_FP hi hv))))
    (andBitFn_mem_FP (notBitFn_mem_FP hsource) (eqFlagFn_mem_FP hv const_nil_mem_FP))

/-- Reject malformed pair encodings before checking the source and witness. -/
def endOfLinePairedVerdict (z : List Bool) : List Bool :=
  andBit (eqFlag z (pair (pairFst z) (pairSnd z)))
    (endOfLineVerdict (pairFst z) (pairSnd z))

/-- The entire verifier is implemented by a polynomial-time string machine. -/
theorem endOfLinePairedVerdict_mem_FP : endOfLinePairedVerdict ∈ FP :=
  andBitFn_mem_FP
    (eqFlagFn_mem_FP id_mem_FP (pairFn_mem_FP pairFst_mem_FP pairSnd_mem_FP))
    verdict_pair_mem_FP

/-- A single deterministic machine checks source promises and endpoint witnesses
with a polynomial bound in the complete serialized verifier input. -/
theorem exists_endOfLinePairedVerdict_machine :
    ∃ (k : ℕ) (machine : TM k) (bound : Polynomial ℕ),
      machine.ComputesInTime endOfLinePairedVerdict bound.eval :=
  mem_FP_iff_computesInTime_polynomial.mp endOfLinePairedVerdict_mem_FP

theorem endOfLinePairedVerdict_accept (z : List Bool) :
    endOfLinePairedVerdict z = [true] ↔ z ∈ pairLang endOfLineRelation := by
  rw [endOfLinePairedVerdict,
    andBit_eq_true_iff (eqFlag_flag _ _) (endOfLineVerdict_flag _ _),
    eqFlag_eq_true_iff, endOfLineVerdict_accept]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨pairFst z, pairSnd z, hz, h⟩
  · rintro ⟨input, witness, rfl, h⟩
    simp only [pairFst_pair, pairSnd_pair]
    exact ⟨trivial, h⟩

/-- Polynomial balance and the verified machine give genuine FNP membership. -/
theorem endOfLineRelation_mem_FNP : endOfLineRelation ∈ FNP := by
  refine ⟨endOfLineRelation_polyBalanced, mem_P_of_decisionFn
    endOfLinePairedVerdict_mem_FP ?_⟩
  intro z
  rw [← endOfLinePairedVerdict_accept]
  rcases andBit_flag (eqFlag z (pair (pairFst z) (pairSnd z)))
    (endOfLineVerdict (pairFst z) (pairSnd z)) with h | h <;>
    simp [endOfLinePairedVerdict, h]

/-- Succinct End-of-Line is a total polynomially verified search problem. -/
theorem endOfLineRelation_mem_TFNP : endOfLineRelation ∈ TFNP :=
  ⟨endOfLineRelation_mem_FNP, endOfLineRelation_total⟩

end GameTheory.Complexity.Backend
