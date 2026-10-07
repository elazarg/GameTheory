import GameTheory.Math.EndOfLineNormalization

/-! Pointer normalization preserves genuine endpoints while rejecting isolated
inconsistencies. Raw witnesses still include a broken outgoing link at the origin. -/

namespace GameTheory.Tests.EndOfLineNormalization

open GameTheory.Math.EndOfLine

private def predecessor (x : Fin 6) : Fin 6 :=
  match x.val with
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | _ => x

private def successor (x : Fin 6) : Fin 6 :=
  match x.val with
  | 0 => 1
  | 2 => 3
  | 3 => 2
  | 5 => 4
  | _ => x

example : predecessor 0 = 0 ∧ successor 0 ≠ 0 ∧ predecessor (successor 0) = 0 := by
  decide

example : ∀ x : Fin 6,
    RawWitness (normalizePredecessor predecessor successor)
      (normalizeSuccessor predecessor successor) 0 x ↔ x = 1 := by
  decide

example : RawWitness predecessor successor 0 5 ∧
    ¬IsEndpoint predecessor successor 5 := by
  decide

example : normalizeSuccessor predecessor successor 5 = 5 ∧
    ¬RawWitness (normalizePredecessor predecessor successor)
      (normalizeSuccessor predecessor successor) 0 5 := by
  decide

example : ∀ x : Fin 6, x = 2 ∨ x = 3 →
    normalizeSuccessor predecessor successor x = successor x ∧
      normalizePredecessor predecessor successor x = predecessor x := by
  decide

private def brokenSuccessor (_ : Bool) : Bool := true

example : id false = false ∧ brokenSuccessor false ≠ false ∧
    RawWitness id brokenSuccessor false false := by
  decide

example : ∀ x : Bool, ¬IsEndpoint id brokenSuccessor x := by
  decide

example : ∃ x : Bool, RawWitness id brokenSuccessor false x :=
  exists_rawWitness id brokenSuccessor false (by decide) (by decide)

example : ¬RawWitness predecessor successor 0 0 := by
  decide

end GameTheory.Tests.EndOfLineNormalization
