module

public import GameTheory.Math.EndOfLineNormalization
public import GameTheoryComplexity.Backend.EndOfLineMachineOps
public import Complexity.Computability.Complexity.Classes.TFNP

@[expose] public section

/-! The usual asymmetric End-of-Line search condition on the shared succinct
pointer encoding. The origin may answer a broken initial link. Weak source
promises are checked, and an invalid promise accepts only the empty witness. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM
open ComputableInPolyTime
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
theorem rawEndOfLineRelation_polyBalanced :
    ∃ p : Polynomial ℕ, ∀ input witness, rawEndOfLineRelation input witness →
      witness.length ≤ p.eval input.length := by
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

/-- Check the weak source promise. -/
def rawEndOfLineSourceFlag (input : List Bool) : Bool :=
  decide (endOfLinePredecessor input (endOfLineOrigin input) = endOfLineOrigin input) &&
    !decide (endOfLineSuccessor input (endOfLineOrigin input) = endOfLineOrigin input)

theorem rawEndOfLineSourceFlag_accept (input : List Bool) :
    rawEndOfLineSourceFlag input = true ↔ rawEndOfLineSourceValid input := by
  simp [rawEndOfLineSourceFlag, rawEndOfLineSourceValid]

/-- Outgoing inconsistency is accepted at any vertex; incoming inconsistency
is accepted away from the origin. -/
def rawEndOfLineWitnessFlag (input witness : List Bool) : Bool :=
  !decide (endOfLinePredecessor input (endOfLineSuccessor input witness) = witness) ||
    (!decide (witness = endOfLineOrigin input) &&
      !decide (endOfLineSuccessor input (endOfLinePredecessor input witness) = witness))

theorem rawEndOfLineWitnessFlag_accept (input witness : List Bool) :
    rawEndOfLineWitnessFlag input witness = true ↔
      GameTheory.Math.EndOfLine.RawWitness (endOfLinePredecessor input)
        (endOfLineSuccessor input) (endOfLineOrigin input) witness := by
  simp [rawEndOfLineWitnessFlag, GameTheory.Math.EndOfLine.RawWitness]

/-- Verify the source, width and asymmetric witness condition, or the fallback. -/
def rawEndOfLineVerdict (input witness : List Bool) : Bool :=
  (rawEndOfLineSourceFlag input &&
    (decide (witness.length = endOfLineWidth input) && rawEndOfLineWitnessFlag input witness)) ||
    (!rawEndOfLineSourceFlag input && decide (witness = []))

theorem rawEndOfLineVerdict_accept (input witness : List Bool) :
    rawEndOfLineVerdict input witness = true ↔ rawEndOfLineRelation input witness := by
  simp only [rawEndOfLineVerdict, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, decide_eq_true_eq, rawEndOfLineSourceFlag_accept,
    rawEndOfLineWitnessFlag_accept, rawEndOfLineRelation]

@[fun_prop] theorem rawEndOfLineSourceFlag_polyTime
    {α : Type} {encIn : α ↪ List Bool} {input : α → List Bool}
    (hi : ComputableInPolyTime input encIn encBits) :
    ComputableInPolyTime (fun a => rawEndOfLineSourceFlag (input a)) encIn encBool := by
  have ho := origin_polyTime hi
  exact bool_and' (decide_eq' (predecessor_polyTime hi ho) ho)
    (bool_not.comp (decide_eq' (successor_polyTime hi ho) ho))

@[fun_prop] theorem rawEndOfLineWitnessFlag_polyTime
    {α : Type} {encIn : α ↪ List Bool} {input witness : α → List Bool}
    (hi : ComputableInPolyTime input encIn encBits)
    (hw : ComputableInPolyTime witness encIn encBits) :
    ComputableInPolyTime (fun a => rawEndOfLineWitnessFlag (input a) (witness a))
      encIn encBool := by
  have hs := successor_polyTime hi hw
  have hp := predecessor_polyTime hi hw
  exact bool_or.comp
    ((bool_not.comp (decide_eq' (predecessor_polyTime hi hs) hw)).prod
      (bool_and' (bool_not.comp (decide_eq' hw (origin_polyTime hi)))
        (bool_not.comp (decide_eq' (successor_polyTime hi hp) hw))))

@[fun_prop] theorem rawEndOfLineVerdict_polyTime
    {α : Type} {encIn : α ↪ List Bool} {input witness : α → List Bool}
    (hi : ComputableInPolyTime input encIn encBits)
    (hw : ComputableInPolyTime witness encIn encBits) :
    ComputableInPolyTime (fun a => rawEndOfLineVerdict (input a) (witness a))
      encIn encBool := by
  have hsource := rawEndOfLineSourceFlag_polyTime hi
  have hwidth := decide_eq' (length_bits.comp hw) (width_polyTime hi)
  have hwitness := rawEndOfLineWitnessFlag_polyTime hi hw
  exact bool_or.comp
    ((bool_and' hsource (bool_and' hwidth hwitness)).prod
      (bool_and' (bool_not.comp hsource) (decide_eq' hw (const []))))

/-- Native FNP membership uses the exact Boolean verifier on an instance/witness pair. -/
theorem rawEndOfLineRelation_mem_FNP :
    rawEndOfLineRelation ∈ Cslib.Complexity.FNP encBits := by
  refine ⟨rawEndOfLineRelation_polyBalanced, ?_⟩
  exact ⟨(fun p : List Bool × List Bool => rawEndOfLineVerdict p.1 p.2),
    rawEndOfLineVerdict_polyTime (fst encBits encBits) (snd encBits encBits),
    fun input witness => (rawEndOfLineVerdict_accept input witness).symm⟩

/-- Standard asymmetric succinct End-of-Line is a total FNP search relation. -/
theorem rawEndOfLineRelation_mem_TFNP :
    rawEndOfLineRelation ∈ Cslib.Complexity.TFNP encBits :=
  ⟨rawEndOfLineRelation_mem_FNP, rawEndOfLineRelation_total⟩

end GameTheory.Complexity.Backend

