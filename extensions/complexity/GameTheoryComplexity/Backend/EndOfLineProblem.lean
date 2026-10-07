import GameTheoryComplexity.Backend.CircuitVectorMachine
import GameTheoryComplexity.Backend.EndOfLineTotality
import Complexitylib.Classes.FNP.Defs

/-! Succinct End-of-Line instances use a width ruler and two serialized circuit
vectors. Every word denotes an instance: malformed scalar circuits give zero bits,
and an invalid initial source has the empty word as its designated witness. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity

/-- The width is encoded in unary, independently of the ruler's bit values. -/
def endOfLineWidth (input : List Bool) : ℕ := (pairFst input).length

/-- The distinguished all-zero vertex. -/
def endOfLineOrigin (input : List Bool) : List Bool :=
  List.replicate (endOfLineWidth input) false

/-- The total predecessor pointer selected by the first circuit vector. -/
def endOfLinePredecessor (input vertex : List Bool) : List Bool :=
  evaluateCircuitVector (pairFst (pairSnd input)) vertex

/-- The total successor pointer selected by the second circuit vector. -/
def endOfLineSuccessor (input vertex : List Bool) : List Bool :=
  evaluateCircuitVector (pairSnd (pairSnd input)) vertex

/-- Canonical serialization of an instance, with a linear-size width ruler. -/
def encodeEndOfLine (width : ℕ) (predecessors successors : List (List Bool)) : List Bool :=
  pair (List.replicate width true)
    (pair (encodeVectorCodes predecessors) (encodeVectorCodes successors))

@[simp] theorem endOfLineWidth_encode (width : ℕ)
    (predecessors successors : List (List Bool)) :
    endOfLineWidth (encodeEndOfLine width predecessors successors) = width := by
  simp [endOfLineWidth, encodeEndOfLine]

/-- The origin is a genuine source, including agreement across its outgoing edge. -/
def endOfLineSourceValid (input : List Bool) : Prop :=
  endOfLinePredecessor input (endOfLineOrigin input) = endOfLineOrigin input ∧
    endOfLineSuccessor input (endOfLineOrigin input) ≠ endOfLineOrigin input ∧
    endOfLinePredecessor input
      (endOfLineSuccessor input (endOfLineOrigin input)) = endOfLineOrigin input

/-- An exact-width endpoint different from the promised source; invalid source
promises instead accept only the empty witness. -/
def endOfLineRelation (input witness : List Bool) : Prop :=
  (endOfLineSourceValid input ∧ witness.length = endOfLineWidth input ∧
    witness ≠ endOfLineOrigin input ∧
    GameTheory.Math.EndOfLine.IsEndpoint
      (endOfLinePredecessor input) (endOfLineSuccessor input) witness) ∨
    (¬endOfLineSourceValid input ∧ witness = [])

private theorem pairFst_length_le : ∀ input : List Bool,
    (pairFst input).length ≤ input.length
  | false :: false :: input => by
      simp only [pairFst, List.length_cons]
      have h := pairFst_length_le input
      omega
  | true :: true :: input => by
      simp only [pairFst, List.length_cons]
      have h := pairFst_length_le input
      omega
  | [] => by decide
  | [b] => by cases b <;> decide
  | false :: true :: input => by simp [pairFst]
  | true :: false :: input => by simp [pairFst]

/-- The unary width ruler bounds every accepted endpoint witness. -/
theorem endOfLineWidth_le_length (input : List Bool) :
    endOfLineWidth input ≤ input.length :=
  pairFst_length_le input

/-- Every accepted endpoint witness has at most the input length. -/
theorem endOfLineRelation_polyBalanced : PolyBalanced endOfLineRelation := by
  refine ⟨Polynomial.X, fun input witness h => ?_⟩
  simp only [Polynomial.eval_X]
  rcases h with ⟨_, hlen, _, _⟩ | ⟨_, rfl⟩
  · rw [hlen]
    exact endOfLineWidth_le_length input
  · exact Nat.zero_le _

/-- Every serialized instance has a witness, including invalid source promises. -/
theorem endOfLineRelation_total (input : List Bool) :
    ∃ witness, endOfLineRelation input witness := by
  classical
  by_cases hsource : endOfLineSourceValid input
  · obtain ⟨w, hlen, hne, hend⟩ := exists_word_endpoint (endOfLineWidth input)
      (endOfLinePredecessor input) (endOfLineSuccessor input)
      (fun w hw => (evaluateCircuitVector_length _ w).trans hw)
      (fun w hw => (evaluateCircuitVector_length _ w).trans hw)
      hsource.1 hsource.2.1 hsource.2.2
    exact ⟨w, Or.inl ⟨hsource, hlen, hne, hend⟩⟩
  · exact ⟨[], Or.inr ⟨hsource, rfl⟩⟩

end GameTheory.Complexity.Backend
