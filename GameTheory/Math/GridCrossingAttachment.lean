import GameTheory.Math.GridCrossing

/-! Crossing switches preserve endpoints even when their ports are attached to
an arbitrary exterior graph. Strand continuations may change; incident edge
roles at every port stay fixed. Unused bends and the center remain isolated. -/

namespace GameTheory.Math.GridCrossing

/-- The abstract comparison path keeps each strand's original outgoing port. -/
def straightSuccessor (rightward upward : Bool) : CrossingNode → CrossingNode
  | .bend p =>
      if p = horizontalBend rightward upward then .port (horizontalOutputPort rightward)
      else if p = verticalBend rightward upward then .port (verticalOutputPort upward)
      else .bend p
  | node => crossingSuccessor rightward upward node

/-- Reverse the comparison paths, leaving unused nodes fixed. -/
def straightPredecessor (rightward upward : Bool) : CrossingNode → CrossingNode
  | .port p =>
      if p = horizontalOutputPort rightward then .bend (horizontalBend rightward upward)
      else if p = verticalOutputPort upward then .bend (verticalBend rightward upward)
      else .port p
  | node => crossingPredecessor rightward upward node

/-- Supply exterior incoming pointers at ports with no local predecessor. -/
def attachPredecessor {α : Type*} (localP : CrossingNode → CrossingNode)
    (externalP : α → α ⊕ CrossingNode) (attachment : Fin 4 → Option α) :
    α ⊕ CrossingNode → α ⊕ CrossingNode
  | .inl x => externalP x
  | .inr (.port p) =>
      if localP (.port p) = .port p then
        match attachment p with
        | none => .inr (.port p)
        | some x => .inl x
      else .inr (localP (.port p))
  | .inr node => .inr (localP node)

/-- Supply exterior outgoing pointers at ports with no local successor. -/
def attachSuccessor {α : Type*} (localS : CrossingNode → CrossingNode)
    (externalS : α → α ⊕ CrossingNode) (attachment : Fin 4 → Option α) :
    α ⊕ CrossingNode → α ⊕ CrossingNode
  | .inl x => externalS x
  | .inr (.port p) =>
      if localS (.port p) = .port p then
        match attachment p with
        | none => .inr (.port p)
        | some x => .inl x
      else .inr (localS (.port p))
  | .inr node => .inr (localS node)

/-- Rerouting preserves valid outgoing-edge presence throughout an arbitrary exterior graph. -/
theorem attached_hasSuccessor_iff {α : Type*} (rightward upward : Bool)
    (externalP externalS : α → α ⊕ CrossingNode) (attachment : Fin 4 → Option α)
    (node : α ⊕ CrossingNode) :
    EndOfLine.HasSuccessor
      (attachPredecessor (crossingPredecessor rightward upward) externalP attachment)
      (attachSuccessor (crossingSuccessor rightward upward) externalS attachment) node ↔
    EndOfLine.HasSuccessor
      (attachPredecessor (straightPredecessor rightward upward) externalP attachment)
      (attachSuccessor (straightSuccessor rightward upward) externalS attachment) node := by
  cases node with
  | inl x =>
    cases he : externalS x with
    | inl y => simp [EndOfLine.HasSuccessor, attachPredecessor, attachSuccessor, he]
    | inr target =>
      cases rightward <;> cases upward <;> cases target with
      | port p =>
        fin_cases p <;> simp [EndOfLine.HasSuccessor, attachPredecessor, attachSuccessor,
          straightPredecessor, crossingPredecessor, horizontalOutputPort, verticalOutputPort,
          horizontalBend, verticalBend, he]
      | bend p =>
        fin_cases p <;> simp [EndOfLine.HasSuccessor, attachPredecessor, attachSuccessor,
          straightPredecessor, crossingPredecessor, horizontalBend, verticalBend,
          horizontalInputPort, verticalInputPort, he]
      | center => simp [EndOfLine.HasSuccessor, attachPredecessor, attachSuccessor,
          straightPredecessor, crossingPredecessor, he]
  | inr inner =>
    cases rightward <;> cases upward <;> cases inner with
    | port p =>
      cases ha : attachment p <;> fin_cases p <;> dsimp at ha <;>
        simp [EndOfLine.HasSuccessor, attachPredecessor, attachSuccessor,
          straightPredecessor, straightSuccessor, crossingPredecessor, crossingSuccessor,
          horizontalInputPort, horizontalOutputPort, verticalInputPort, verticalOutputPort,
          horizontalBend, verticalBend, ha]
    | bend p =>
      fin_cases p <;> simp [EndOfLine.HasSuccessor, attachPredecessor, attachSuccessor,
        straightPredecessor, straightSuccessor, crossingPredecessor, crossingSuccessor,
        horizontalOutputPort, verticalOutputPort, horizontalBend, verticalBend]
    | center => simp [EndOfLine.HasSuccessor, attachPredecessor, attachSuccessor,
        straightPredecessor, straightSuccessor, crossingPredecessor, crossingSuccessor]

/-- Rerouting preserves valid incoming-edge presence throughout an arbitrary exterior graph. -/
theorem attached_hasPredecessor_iff {α : Type*} (rightward upward : Bool)
    (externalP externalS : α → α ⊕ CrossingNode) (attachment : Fin 4 → Option α)
    (node : α ⊕ CrossingNode) :
    EndOfLine.HasPredecessor
      (attachPredecessor (crossingPredecessor rightward upward) externalP attachment)
      (attachSuccessor (crossingSuccessor rightward upward) externalS attachment) node ↔
    EndOfLine.HasPredecessor
      (attachPredecessor (straightPredecessor rightward upward) externalP attachment)
      (attachSuccessor (straightSuccessor rightward upward) externalS attachment) node := by
  cases node with
  | inl x =>
    cases he : externalP x with
    | inl y => simp [EndOfLine.HasPredecessor, attachPredecessor, attachSuccessor, he]
    | inr target =>
      cases rightward <;> cases upward <;> cases target with
      | port p =>
        fin_cases p <;> simp [EndOfLine.HasPredecessor, attachPredecessor, attachSuccessor,
          straightSuccessor, crossingSuccessor, horizontalInputPort, verticalInputPort,
          horizontalBend, verticalBend, he]
      | bend p =>
        fin_cases p <;> simp [EndOfLine.HasPredecessor, attachPredecessor, attachSuccessor,
          straightSuccessor, crossingSuccessor, horizontalBend, verticalBend,
          horizontalOutputPort, verticalOutputPort, he]
      | center => simp [EndOfLine.HasPredecessor, attachPredecessor, attachSuccessor,
          straightSuccessor, crossingSuccessor, he]
  | inr inner =>
    cases rightward <;> cases upward <;> cases inner with
    | port p =>
      cases ha : attachment p <;> fin_cases p <;> dsimp at ha <;>
        simp [EndOfLine.HasPredecessor, attachPredecessor, attachSuccessor,
          straightSuccessor, straightPredecessor, crossingSuccessor, crossingPredecessor,
          horizontalOutputPort, horizontalInputPort, verticalOutputPort, verticalInputPort,
          horizontalBend, verticalBend, ha]
    | bend p =>
      fin_cases p <;> simp [EndOfLine.HasPredecessor, attachPredecessor, attachSuccessor,
        straightSuccessor, straightPredecessor, crossingSuccessor, crossingPredecessor,
        horizontalInputPort, verticalInputPort, horizontalBend, verticalBend]
    | center => simp [EndOfLine.HasPredecessor, attachPredecessor, attachSuccessor,
        straightSuccessor, straightPredecessor, crossingSuccessor, crossingPredecessor]

/-- Switching strand continuations preserves every endpoint under arbitrary attachments. -/
theorem attached_isEndpoint_iff {α : Type*} (rightward upward : Bool)
    (externalP externalS : α → α ⊕ CrossingNode) (attachment : Fin 4 → Option α)
    (node : α ⊕ CrossingNode) :
    EndOfLine.IsEndpoint
      (attachPredecessor (crossingPredecessor rightward upward) externalP attachment)
      (attachSuccessor (crossingSuccessor rightward upward) externalS attachment) node ↔
    EndOfLine.IsEndpoint
      (attachPredecessor (straightPredecessor rightward upward) externalP attachment)
      (attachSuccessor (straightSuccessor rightward upward) externalS attachment) node := by
  simp only [EndOfLine.IsEndpoint, attached_hasSuccessor_iff, attached_hasPredecessor_iff]

/-- Attached crossings create no endpoint at a used or unused bend. -/
theorem attached_bend_not_endpoint {α : Type*} (rightward upward : Bool)
    (externalP externalS : α → α ⊕ CrossingNode) (attachment : Fin 4 → Option α)
    (p : Fin 4) :
    ¬EndOfLine.IsEndpoint
      (attachPredecessor (crossingPredecessor rightward upward) externalP attachment)
      (attachSuccessor (crossingSuccessor rightward upward) externalS attachment)
      (.inr (.bend p)) := by
  cases rightward <;> cases upward <;> fin_cases p <;>
    simp [EndOfLine.IsEndpoint, EndOfLine.HasSuccessor, EndOfLine.HasPredecessor,
      attachPredecessor, attachSuccessor, crossingPredecessor, crossingSuccessor,
      horizontalInputPort, horizontalOutputPort, verticalInputPort, verticalOutputPort,
      horizontalBend, verticalBend]

/-- The removed crossing center remains isolated under arbitrary exterior pointers. -/
theorem attached_center_not_endpoint {α : Type*} (rightward upward : Bool)
    (externalP externalS : α → α ⊕ CrossingNode) (attachment : Fin 4 → Option α) :
    ¬EndOfLine.IsEndpoint
      (attachPredecessor (crossingPredecessor rightward upward) externalP attachment)
      (attachSuccessor (crossingSuccessor rightward upward) externalS attachment)
      (.inr .center) := by
  simp [EndOfLine.IsEndpoint, EndOfLine.HasSuccessor, EndOfLine.HasPredecessor,
    attachPredecessor, attachSuccessor, crossingPredecessor, crossingSuccessor]

/-- Every attached-gadget endpoint belongs to the exterior graph or a boundary port. -/
theorem attached_endpoint_cases {α : Type*} (rightward upward : Bool)
    (externalP externalS : α → α ⊕ CrossingNode) (attachment : Fin 4 → Option α)
    (node : α ⊕ CrossingNode)
    (he : EndOfLine.IsEndpoint
      (attachPredecessor (crossingPredecessor rightward upward) externalP attachment)
      (attachSuccessor (crossingSuccessor rightward upward) externalS attachment) node) :
    (∃ x, node = .inl x) ∨ (∃ p, node = .inr (.port p)) := by
  cases node with
  | inl x => exact Or.inl ⟨x, rfl⟩
  | inr inner =>
    cases inner with
    | port p => exact Or.inr ⟨p, rfl⟩
    | bend p =>
      exact False.elim
        (attached_bend_not_endpoint rightward upward externalP externalS attachment p he)
    | center =>
      exact False.elim
        (attached_center_not_endpoint rightward upward externalP externalS attachment he)

end GameTheory.Math.GridCrossing
