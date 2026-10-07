import GameTheory.Math.EndOfLineNormalization
import GameTheoryComplexity.Backend.EndOfLineMachineOps
import Complexitylib.Classes.P.NormalForm

/-! The usual asymmetric End-of-Line search condition on the shared succinct
pointer encoding. The origin may answer a broken initial link. Weak source
promises are checked, and an invalid promise accepts only the empty witness. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open EndOfLineMachineOps

/-- The standard source promise does not require the first edge to be consistent. -/
def rawEndOfLineSourceValid (input : List Bool) : Prop :=
  endOfLinePredecessor input (endOfLineOrigin input) = endOfLineOrigin input ∧
    endOfLineSuccessor input (endOfLineOrigin input) ≠ endOfLineOrigin input

/-- Exact-width asymmetric pointer inconsistencies; failed source promises
instead accept only the empty word. -/
def rawEndOfLineRelation (input witness : List Bool) : Prop :=
  (rawEndOfLineSourceValid input ∧ witness.length = endOfLineWidth input ∧
    GameTheory.Math.EndOfLine.RawWitness (endOfLinePredecessor input)
      (endOfLineSuccessor input) (endOfLineOrigin input) witness) ∨
    (¬rawEndOfLineSourceValid input ∧ witness = [])

/-- The unary ruler bounds every accepted raw witness. -/
theorem rawEndOfLineRelation_polyBalanced : PolyBalanced rawEndOfLineRelation := by
  refine ⟨Polynomial.X, fun input witness h => ?_⟩
  simp only [Polynomial.eval_X]
  rcases h with ⟨_, hlen, _⟩ | ⟨_, rfl⟩
  · rw [hlen]
    exact endOfLineWidth_le_length input
  · exact Nat.zero_le _

/-- A broken first link is answered by the origin; otherwise finite graph
parity gives an endpoint, which also satisfies the raw condition. -/
theorem rawEndOfLineRelation_total (input : List Bool) :
    ∃ witness, rawEndOfLineRelation input witness := by
  classical
  by_cases hsource : rawEndOfLineSourceValid input
  · by_cases hlink : endOfLinePredecessor input
        (endOfLineSuccessor input (endOfLineOrigin input)) = endOfLineOrigin input
    · obtain ⟨w, hlen, hne, hend⟩ := exists_word_endpoint (endOfLineWidth input)
        (endOfLinePredecessor input) (endOfLineSuccessor input)
        (fun w hw => (evaluateCircuitVector_length _ w).trans hw)
        (fun w hw => (evaluateCircuitVector_length _ w).trans hw)
        hsource.1 hsource.2 hlink
      exact ⟨w, Or.inl ⟨hsource, hlen,
        GameTheory.Math.EndOfLine.endpoint_rawWitness _ _ hne hend⟩⟩
    · exact ⟨endOfLineOrigin input, Or.inl ⟨hsource, List.length_replicate,
        Or.inl hlink⟩⟩
  · exact ⟨[], Or.inr ⟨hsource, rfl⟩⟩

/-- One-bit check of the weak source promise. -/
def rawEndOfLineSourceFlag (input : List Bool) : List Bool :=
  andBit
    (eqFlag (endOfLinePredecessor input (endOfLineOrigin input)) (endOfLineOrigin input))
    (notBit (eqFlag (endOfLineSuccessor input (endOfLineOrigin input))
      (endOfLineOrigin input)))

theorem rawEndOfLineSourceFlag_flag (input : List Bool) :
    rawEndOfLineSourceFlag input = [true] ∨ rawEndOfLineSourceFlag input = [false] :=
  andBit_flag _ _

theorem rawEndOfLineSourceFlag_accept (input : List Bool) :
    rawEndOfLineSourceFlag input = [true] ↔ rawEndOfLineSourceValid input := by
  rw [rawEndOfLineSourceFlag, andBit_eq_true_iff (eqFlag_flag _ _)
    (negFlag_flag (eqFlag_flag _ _)), negFlag_accept (eqFlag_flag _ _)]
  simp only [eqFlag_eq_true_iff, rawEndOfLineSourceValid]

/-- Outgoing inconsistency is accepted at any vertex; incoming inconsistency
is accepted away from the origin. -/
def rawEndOfLineWitnessFlag (input witness : List Bool) : List Bool :=
  orBit
    (notBit (eqFlag (endOfLinePredecessor input (endOfLineSuccessor input witness)) witness))
    (andBit (notBit (eqFlag witness (endOfLineOrigin input)))
      (notBit (eqFlag (endOfLineSuccessor input (endOfLinePredecessor input witness)) witness)))

theorem rawEndOfLineWitnessFlag_flag (input witness : List Bool) :
    rawEndOfLineWitnessFlag input witness = [true] ∨
      rawEndOfLineWitnessFlag input witness = [false] :=
  orBit_flag (negFlag_flag (eqFlag_flag _ _)) (andBit_flag _ _)

theorem rawEndOfLineWitnessFlag_accept (input witness : List Bool) :
    rawEndOfLineWitnessFlag input witness = [true] ↔
      GameTheory.Math.EndOfLine.RawWitness (endOfLinePredecessor input)
        (endOfLineSuccessor input) (endOfLineOrigin input) witness := by
  rw [rawEndOfLineWitnessFlag, orBit_eq_true_iff (negFlag_flag (eqFlag_flag _ _))
    (andBit_flag _ _), andBit_eq_true_iff (negFlag_flag (eqFlag_flag _ _))
    (negFlag_flag (eqFlag_flag _ _)), negFlag_accept (eqFlag_flag _ _),
    negFlag_accept (eqFlag_flag _ _), negFlag_accept (eqFlag_flag _ _)]
  simp only [eqFlag_eq_true_iff, GameTheory.Math.EndOfLine.RawWitness]

/-- Verify source, width and the asymmetric witness condition, or the fallback. -/
def rawEndOfLineVerdict (input witness : List Bool) : List Bool :=
  orBit
    (andBit (rawEndOfLineSourceFlag input)
      (andBit (eqFlag (List.replicate witness.length false) (endOfLineOrigin input))
        (rawEndOfLineWitnessFlag input witness)))
    (andBit (notBit (rawEndOfLineSourceFlag input)) (eqFlag witness []))

theorem rawEndOfLineVerdict_flag (input witness : List Bool) :
    rawEndOfLineVerdict input witness = [true] ∨
      rawEndOfLineVerdict input witness = [false] :=
  orBit_flag (andBit_flag _ _) (andBit_flag _ _)

theorem rawEndOfLineVerdict_accept (input witness : List Bool) :
    rawEndOfLineVerdict input witness = [true] ↔ rawEndOfLineRelation input witness := by
  rw [rawEndOfLineVerdict, orBit_eq_true_iff (andBit_flag _ _) (andBit_flag _ _),
    andBit_eq_true_iff (rawEndOfLineSourceFlag_flag _) (andBit_flag _ _),
    andBit_eq_true_iff (eqFlag_flag _ _) (rawEndOfLineWitnessFlag_flag _ _),
    andBit_eq_true_iff (negFlag_flag (rawEndOfLineSourceFlag_flag _)) (eqFlag_flag _ _),
    negFlag_accept (rawEndOfLineSourceFlag_flag _)]
  simp only [eqFlag_eq_true_iff, rawEndOfLineSourceFlag_accept,
    rawEndOfLineWitnessFlag_accept, endOfLineOrigin, zeroWords_eq_iff, rawEndOfLineRelation]

/-- Weak source checking composes polynomial-time pointer machines. -/
theorem rawEndOfLineSourceFlagFn_mem_FP {input : List Bool → List Bool} (hi : input ∈ FP) :
    (fun z => rawEndOfLineSourceFlag (input z)) ∈ FP := by
  have ho := originFn_mem_FP hi
  exact andBitFn_mem_FP (eqFlagFn_mem_FP (predecessorFn_mem_FP hi ho) ho)
    (notBitFn_mem_FP (eqFlagFn_mem_FP (successorFn_mem_FP hi ho) ho))

private theorem witnessFlagFn_mem_FP {input witness : List Bool → List Bool}
    (hi : input ∈ FP) (hw : witness ∈ FP) :
    (fun z => rawEndOfLineWitnessFlag (input z) (witness z)) ∈ FP := by
  have hs := successorFn_mem_FP hi hw
  have hp := predecessorFn_mem_FP hi hw
  exact orBitFn_mem_FP
    (notBitFn_mem_FP (eqFlagFn_mem_FP (predecessorFn_mem_FP hi hs) hw))
    (andBitFn_mem_FP (notBitFn_mem_FP (eqFlagFn_mem_FP hw (originFn_mem_FP hi)))
      (notBitFn_mem_FP (eqFlagFn_mem_FP (successorFn_mem_FP hi hp) hw)))

private theorem verdict_pair_mem_FP :
    (fun z => rawEndOfLineVerdict (pairFst z) (pairSnd z)) ∈ FP := by
  have hi := pairFst_mem_FP
  have hw := pairSnd_mem_FP
  have ho := originFn_mem_FP hi
  have hsource := rawEndOfLineSourceFlagFn_mem_FP hi
  have hzero : (fun z => List.replicate (pairSnd z).length false) ∈ FP := by
    simpa only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] using
      mulLenFn_mem_FP (constFn_mem_FP [false]) hw
  exact orBitFn_mem_FP
    (andBitFn_mem_FP hsource
      (andBitFn_mem_FP (eqFlagFn_mem_FP hzero ho) (witnessFlagFn_mem_FP hi hw)))
    (andBitFn_mem_FP (notBitFn_mem_FP hsource) (eqFlagFn_mem_FP hw const_nil_mem_FP))

/-- Noncanonical outer pair encodings are rejected. -/
def rawEndOfLinePairedVerdict (z : List Bool) : List Bool :=
  andBit (eqFlag z (pair (pairFst z) (pairSnd z)))
    (rawEndOfLineVerdict (pairFst z) (pairSnd z))

/-- The complete verifier is a polynomial-time string function. -/
theorem rawEndOfLinePairedVerdict_mem_FP : rawEndOfLinePairedVerdict ∈ FP :=
  andBitFn_mem_FP
    (eqFlagFn_mem_FP id_mem_FP (pairFn_mem_FP pairFst_mem_FP pairSnd_mem_FP))
    verdict_pair_mem_FP

/-- A single deterministic machine verifies the complete serialized input in
polynomial time, without enumerating the exponentially many vertices. -/
theorem exists_rawEndOfLinePairedVerdict_machine :
    ∃ (k : ℕ) (machine : TM k) (bound : Polynomial ℕ),
      machine.ComputesInTime rawEndOfLinePairedVerdict bound.eval :=
  mem_FP_iff_computesInTime_polynomial.mp rawEndOfLinePairedVerdict_mem_FP

theorem rawEndOfLinePairedVerdict_accept (z : List Bool) :
    rawEndOfLinePairedVerdict z = [true] ↔ z ∈ pairLang rawEndOfLineRelation := by
  rw [rawEndOfLinePairedVerdict,
    andBit_eq_true_iff (eqFlag_flag _ _) (rawEndOfLineVerdict_flag _ _),
    eqFlag_eq_true_iff, rawEndOfLineVerdict_accept]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨pairFst z, pairSnd z, hz, h⟩
  · rintro ⟨input, witness, rfl, h⟩
    simp only [pairFst_pair, pairSnd_pair]
    exact ⟨trivial, h⟩

/-- Genuine FNP membership uses the canonical paired polynomial-time verifier. -/
theorem rawEndOfLineRelation_mem_FNP : rawEndOfLineRelation ∈ FNP := by
  refine ⟨rawEndOfLineRelation_polyBalanced, mem_P_of_decisionFn
    rawEndOfLinePairedVerdict_mem_FP ?_⟩
  intro z
  rw [← rawEndOfLinePairedVerdict_accept]
  rcases andBit_flag (eqFlag z (pair (pairFst z) (pairSnd z)))
    (rawEndOfLineVerdict (pairFst z) (pairSnd z)) with h | h <;>
    simp [rawEndOfLinePairedVerdict, h]

/-- Standard asymmetric succinct End-of-Line is a total FNP search relation. -/
theorem rawEndOfLineRelation_mem_TFNP : rawEndOfLineRelation ∈ TFNP :=
  ⟨rawEndOfLineRelation_mem_FNP, rawEndOfLineRelation_total⟩

end GameTheory.Complexity.Backend
