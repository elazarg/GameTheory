import GameTheory.Math.GridCrossingAttachment

/-! Closing the original strands yields two cycles; switching their continuations
joins them into one cycle while preserving all endpoints. Arbitrary broken exterior
pointers and aliased attachments are also covered by the general preservation theorem. -/

namespace GameTheory.Tests.GridCrossingAttachment

open GameTheory.Math.GridCrossing GameTheory.Math.EndOfLine

private def closedAttachment (p : Fin 4) : Option (Fin 2) :=
  some (if p = 1 ∨ p = 3 then 0 else 1)

private def closedExternalP (x : Fin 2) : Fin 2 ⊕ CrossingNode :=
  .inr (.port (if x = 0 then 1 else 0))

private def closedExternalS (x : Fin 2) : Fin 2 ⊕ CrossingNode :=
  .inr (.port (if x = 0 then 3 else 2))

private def closedP (switched : Bool) : Fin 2 ⊕ CrossingNode → Fin 2 ⊕ CrossingNode :=
  attachPredecessor (if switched then crossingPredecessor true true
    else straightPredecessor true true) closedExternalP closedAttachment

private def closedS (switched : Bool) : Fin 2 ⊕ CrossingNode → Fin 2 ⊕ CrossingNode :=
  attachSuccessor (if switched then crossingSuccessor true true
    else straightSuccessor true true) closedExternalS closedAttachment

private def fourSteps (S : Fin 2 ⊕ CrossingNode → Fin 2 ⊕ CrossingNode)
    (node : Fin 2 ⊕ CrossingNode) : Fin 2 ⊕ CrossingNode := S (S (S (S node)))

example : fourSteps (closedS false) (.inl 0) = .inl 0 ∧
    fourSteps (closedS false) (.inl 1) = .inl 1 ∧
    fourSteps (closedS true) (.inl 0) = .inl 1 ∧
    fourSteps (closedS true) (.inl 1) = .inl 0 ∧
    fourSteps (closedS true) (fourSteps (closedS true) (.inl 0)) = .inl 0 := by decide

example (node : Fin 2 ⊕ CrossingNode) :
    ¬IsEndpoint (closedP false) (closedS false) node ∧
      ¬IsEndpoint (closedP true) (closedS true) node := by
  cases node with
  | inl x => fin_cases x <;> decide
  | inr inner =>
    cases inner with
    | port p => fin_cases p <;> decide
    | bend p => fin_cases p <;> decide
    | center => decide

example (node : Fin 2 ⊕ CrossingNode) :
    IsEndpoint (closedP true) (closedS true) node ↔
      IsEndpoint (closedP false) (closedS false) node :=
  attached_isEndpoint_iff true true closedExternalP closedExternalS closedAttachment node

example (externalP externalS : ℕ → ℕ ⊕ CrossingNode) (node : ℕ ⊕ CrossingNode) :
    IsEndpoint (attachPredecessor (crossingPredecessor false true) externalP (fun _ => some 0))
      (attachSuccessor (crossingSuccessor false true) externalS (fun _ => some 0)) node ↔
    IsEndpoint (attachPredecessor (straightPredecessor false true) externalP (fun _ => some 0))
      (attachSuccessor (straightSuccessor false true) externalS (fun _ => some 0)) node :=
  attached_isEndpoint_iff false true externalP externalS (fun _ => some 0) node

end GameTheory.Tests.GridCrossingAttachment
