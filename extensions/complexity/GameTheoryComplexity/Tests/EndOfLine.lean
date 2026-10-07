import GameTheoryComplexity.Backend.EndOfLineVerifier

/-! Encoded End-of-Line controls use actual constant circuits. Endpoints have
exactly one mutually consistent nontrivial edge; isolated vertices with two
broken pointers are not accepted merely because a raw pointer equation fails. -/

namespace GameTheory.Complexity.Tests.EndOfLine

open _root_.Complexity
open _root_.Complexity.Cobham
open GameTheory.Complexity.Backend

/-- Constants are actual AND/OR circuits using an input and its negation. -/
def constantFamily (value : Bool) : CircuitFamily Basis.andOr2 where
  emptyOutput := value
  circuits := fun n => ⟨0,
    { gates := Fin.elim0
      outputs := fun _ =>
        { op := if value then .or else .and
          fanIn := 2
          arityOk := by cases value <;> rfl
          inputs := fun _ => ⟨0, by simpa using NeZero.pos n⟩
          negated := fun i => decide (i = 1) }
      acyclic := fun i => Fin.elim0 i }⟩

/-- The two one-bit vertices form the path zero to one. -/
def oneBitPath : List Bool :=
  encodeEndOfLine 1 [(constantFamily false).encodeAt 1]
    [(constantFamily true).encodeAt 1]

theorem oneBitPath_source_valid : endOfLineSourceValid oneBitPath := by
  unfold endOfLineSourceValid
  decide

theorem oneBitPath_accepts_sink : endOfLineVerdict oneBitPath [true] = [true] := by decide

theorem oneBitPath_rejects_origin : endOfLineVerdict oneBitPath [false] = [false] := by decide

theorem oneBitPath_rejects_short : endOfLineVerdict oneBitPath [] = [false] := by decide

theorem oneBitPath_rejects_long :
    endOfLineVerdict oneBitPath [true, false] = [false] := by decide

theorem oneBitPath_paired_accepts_sink :
    endOfLinePairedVerdict (pair oneBitPath [true]) = [true] := by
  rw [endOfLinePairedVerdict, pairFst_pair, pairSnd_pair, oneBitPath_accepts_sink]
  rw [(eqFlag_eq_true_iff _ _).2 rfl]
  rfl

theorem rejects_malformed_outer_pair : endOfLinePairedVerdict [true] = [false] := by decide

/-- Missing circuits denote zero pointers, so the distinguished vertex is not a source. -/
def missingCircuits : List Bool := encodeEndOfLine 1 [] []

theorem missingCircuits_not_source : ¬endOfLineSourceValid missingCircuits := by
  unfold endOfLineSourceValid
  decide

theorem missingCircuits_accepts_only_empty :
    endOfLineVerdict missingCircuits [] = [true] ∧
      endOfLineVerdict missingCircuits [false] = [false] ∧
      endOfLineVerdict missingCircuits [true] = [false] := by decide

/-- A false-tagged empty-input code is malformed at the positive vertex width. -/
def malformedCircuits : List Bool := encodeEndOfLine 1 [[false, true]] [[true]]

theorem malformedCircuits_zero_pointers :
    endOfLinePredecessor malformedCircuits [true] = [false] ∧
      endOfLineSuccessor malformedCircuits [true] = [false] := by decide

theorem malformedCircuits_accepts_empty :
    endOfLineVerdict malformedCircuits [] = [true] := by decide

theorem malformedCircuits_rejects_nonempty :
    endOfLineVerdict malformedCircuits [true] = [false] := by decide

theorem zeroWidth_accepts_empty :
    endOfLineVerdict (encodeEndOfLine 0 [] []) [] = [true] := by decide

theorem zeroWidth_rejects_nonempty :
    endOfLineVerdict (encodeEndOfLine 0 [] []) [true] = [false] := by decide

/-- The same path embedded in two bits leaves isolated vertices off the path. -/
def twoBitPath : List Bool :=
  encodeEndOfLine 2 [(constantFamily false).encodeAt 2, (constantFamily false).encodeAt 2]
    [(constantFamily true).encodeAt 2, (constantFamily false).encodeAt 2]

/-- Two failed raw pointer equations alone do not make an isolated vertex an endpoint. -/
theorem rejects_isolated_broken_pointers :
    endOfLineVerdict twoBitPath [false, true] = [false] ∧
      endOfLinePredecessor twoBitPath (endOfLineSuccessor twoBitPath [false, true]) ≠
        [false, true] ∧
      endOfLineSuccessor twoBitPath (endOfLinePredecessor twoBitPath [false, true]) ≠
        [false, true] := by decide

end GameTheory.Complexity.Tests.EndOfLine
