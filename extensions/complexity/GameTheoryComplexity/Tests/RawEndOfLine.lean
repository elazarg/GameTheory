import GameTheoryComplexity.Backend.RawEndOfLine
import GameTheoryComplexity.Tests.EndOfLine

/-! Controls distinguish the asymmetric pointer witness relation from filtered
graph endpoints, including the broken initial edge answered by the origin. -/

namespace GameTheory.Complexity.Tests.RawEndOfLine

open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Complexity.Backend
open GameTheory.Complexity.Tests.EndOfLine

/-- A one-bit identity circuit uses the same input at both AND ports. -/
def identityFamily : CircuitFamily Basis.andOr2 where
  emptyOutput := false
  circuits := fun n => ⟨0,
    { gates := Fin.elim0
      outputs := fun _ =>
        { op := .and
          fanIn := 2
          arityOk := rfl
          inputs := fun _ => ⟨0, by simpa using NeZero.pos n⟩
          negated := fun _ => false }
      acyclic := fun i => Fin.elim0 i }⟩

/-- The origin points to one, whose predecessor incorrectly points to itself. -/
def brokenInitialLink : List Bool :=
  encodeEndOfLine 1 [identityFamily.encodeAt 1] [(constantFamily true).encodeAt 1]

theorem brokenInitialLink_weak_source : rawEndOfLineSourceValid brokenInitialLink := by
  unfold rawEndOfLineSourceValid
  decide

theorem brokenInitialLink_not_strong_source : ¬endOfLineSourceValid brokenInitialLink := by
  unfold endOfLineSourceValid
  decide

theorem brokenInitialLink_origin_is_outgoing_inconsistency :
    endOfLinePredecessor brokenInitialLink
        (endOfLineSuccessor brokenInitialLink [false]) ≠ [false] := by decide

theorem brokenInitialLink_accepts_origin :
    rawEndOfLineVerdict brokenInitialLink [false] = [true] := by decide

theorem brokenInitialLink_rejects_empty :
    rawEndOfLineVerdict brokenInitialLink [] = [false] := by decide

theorem brokenInitialLink_rejects_other_vertex :
    rawEndOfLineVerdict brokenInitialLink [true] = [false] := by decide

theorem brokenInitialLink_endpoint_verifier_uses_fallback :
    endOfLineVerdict brokenInitialLink [] = [true] ∧
      endOfLineVerdict brokenInitialLink [false] = [false] := by decide

theorem strong_path_accepts_sink : rawEndOfLineVerdict oneBitPath [true] = [true] := by decide

theorem strong_path_rejects_origin :
    rawEndOfLineVerdict oneBitPath [false] = [false] := by decide

theorem strong_path_rejects_wrong_width :
    rawEndOfLineVerdict oneBitPath [] = [false] ∧
      rawEndOfLineVerdict oneBitPath [true, false] = [false] := by decide

/-- A disconnected malformed vertex is a raw answer even without a consistent edge. -/
theorem accepts_isolated_broken_pointers :
    rawEndOfLineVerdict twoBitPath [false, true] = [true] ∧
      endOfLineVerdict twoBitPath [false, true] = [false] := by decide

theorem paired_accepts_broken_origin :
    rawEndOfLinePairedVerdict (pair brokenInitialLink [false]) = [true] := by
  rw [rawEndOfLinePairedVerdict, pairFst_pair, pairSnd_pair,
    brokenInitialLink_accepts_origin]
  rw [(eqFlag_eq_true_iff _ _).2 rfl]
  rfl

theorem rejects_malformed_outer_pair :
    rawEndOfLinePairedVerdict [true] = [false] := by decide

theorem missing_circuits_use_empty_fallback :
    rawEndOfLineVerdict missingCircuits [] = [true] ∧
      rawEndOfLineVerdict missingCircuits [false] = [false] ∧
      rawEndOfLineVerdict missingCircuits [true] = [false] := by decide

theorem malformed_circuits_use_empty_fallback :
    rawEndOfLineVerdict malformedCircuits [] = [true] ∧
      rawEndOfLineVerdict malformedCircuits [true] = [false] := by decide

theorem zero_width_uses_empty_fallback :
    rawEndOfLineVerdict (encodeEndOfLine 0 [] []) [] = [true] ∧
      rawEndOfLineVerdict (encodeEndOfLine 0 [] []) [true] = [false] := by decide

end GameTheory.Complexity.Tests.RawEndOfLine
