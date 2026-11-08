module

public import GameTheoryComplexity.Backend.EndOfLineVerifier

@[expose] public section

/-! Encoded End-of-Line controls use actual constant circuits. Endpoints have
exactly one mutually consistent nontrivial edge; isolated vertices with two
broken pointers are not accepted merely because a raw pointer equation fails. -/

namespace GameTheory.Complexity.Tests.EndOfLine

open GameTheory.Complexity.Backend

/-- An input and its negation form an actual AND/OR constant gate. -/
def constantCode (value : Bool) : List Bool :=
  true :: CircuitFormat.encode [((!value, false, true), [0, 0])]

/-- The two one-bit vertices form the path zero to one. -/
def oneBitPath : List Bool :=
  encodeEndOfLine 1 [constantCode false]
    [constantCode true]

theorem oneBitPath_source_valid : endOfLineSourceValid oneBitPath := by
  unfold endOfLineSourceValid
  decide

theorem oneBitPath_accepts_sink : endOfLineVerdict oneBitPath [true] = true := by decide

theorem oneBitPath_rejects_origin : endOfLineVerdict oneBitPath [false] = false := by decide

theorem oneBitPath_rejects_short : endOfLineVerdict oneBitPath [] = false := by decide

theorem oneBitPath_rejects_long :
    endOfLineVerdict oneBitPath [true, false] = false := by decide

/-- Missing circuits denote zero pointers, so the distinguished vertex is not a source. -/
def missingCircuits : List Bool := encodeEndOfLine 1 [] []

theorem missingCircuits_not_source : ¬endOfLineSourceValid missingCircuits := by
  unfold endOfLineSourceValid
  decide

theorem missingCircuits_accepts_only_empty :
    endOfLineVerdict missingCircuits [] = true ∧
      endOfLineVerdict missingCircuits [false] = false ∧
      endOfLineVerdict missingCircuits [true] = false := by decide

/-- A false-tagged empty-input code is malformed at the positive vertex width. -/
def malformedCircuits : List Bool := encodeEndOfLine 1 [[false, true]] [[true]]

theorem malformedCircuits_zero_pointers :
    endOfLinePredecessor malformedCircuits [true] = [false] ∧
      endOfLineSuccessor malformedCircuits [true] = [false] := by decide

theorem malformedCircuits_accepts_empty :
    endOfLineVerdict malformedCircuits [] = true := by decide

theorem malformedCircuits_rejects_nonempty :
    endOfLineVerdict malformedCircuits [true] = false := by decide

theorem zeroWidth_accepts_empty :
    endOfLineVerdict (encodeEndOfLine 0 [] []) [] = true := by decide

theorem zeroWidth_rejects_nonempty :
    endOfLineVerdict (encodeEndOfLine 0 [] []) [true] = false := by decide

/-- The same path embedded in two bits leaves isolated vertices off the path. -/
def twoBitPath : List Bool :=
  encodeEndOfLine 2 [constantCode false, constantCode false]
    [constantCode true, constantCode false]

/-- Two failed raw pointer equations alone do not make an isolated vertex an endpoint. -/
theorem rejects_isolated_broken_pointers :
    endOfLineVerdict twoBitPath [false, true] = false ∧
      endOfLinePredecessor twoBitPath (endOfLineSuccessor twoBitPath [false, true]) ≠
        [false, true] ∧
      endOfLineSuccessor twoBitPath (endOfLinePredecessor twoBitPath [false, true]) ≠
        [false, true] := by decide

end GameTheory.Complexity.Tests.EndOfLine
