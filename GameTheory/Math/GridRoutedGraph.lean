import GameTheory.Math.GridWireDecoder
import GameTheory.Math.GridWireSwitch
import GameTheory.Math.GridWireImageSteps

/-! Global grid pointers decode a live routed label, exchange crossing tails,
then return its geometric image. Background points are self-loops. Every grid
endpoint belongs to an original vertex, including endpoints on other components. -/

namespace GameTheory.Math.GridWire

open GameTheory.Math.EndOfLine

/-- The globally switched outgoing pointer on grid coordinates. -/
def gridRoutedSuccessor (n : ℕ) (P S : ℕ → ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  match decodeWireNode n P S p with
  | none => p
  | some v => routedCoordinate n P S (switchedRoutedSuccessor n P S v)

/-- The globally switched incoming pointer on grid coordinates. -/
def gridRoutedPredecessor (n : ℕ) (P S : ℕ → ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  match decodeWireNode n P S p with
  | none => p
  | some v => routedCoordinate n P S (switchedRoutedPredecessor n P S v)

theorem gridRoutedSuccessor_encode {n : ℕ} {P S : ℕ → ℕ} {v : WireNode}
    (hl : liveWireNode n P S v) :
    gridRoutedSuccessor n P S (routedCoordinate n P S v) =
      routedCoordinate n P S (switchedRoutedSuccessor n P S v) := by
  simp [gridRoutedSuccessor, decodeWireNode_roundtrip hl]

theorem gridRoutedPredecessor_encode {n : ℕ} {P S : ℕ → ℕ} {v : WireNode}
    (hl : liveWireNode n P S v) :
    gridRoutedPredecessor n P S (routedCoordinate n P S v) =
      routedCoordinate n P S (switchedRoutedPredecessor n P S v) := by
  simp [gridRoutedPredecessor, decodeWireNode_roundtrip hl]

theorem gridRoutedSuccessor_ne_iff {n : ℕ} {P S : ℕ → ℕ} {v : WireNode}
    (hl : liveWireNode n P S v) :
    gridRoutedSuccessor n P S (routedCoordinate n P S v) ≠ routedCoordinate n P S v ↔
      switchedRoutedSuccessor n P S v ≠ v := by
  rw [gridRoutedSuccessor_encode hl]
  constructor
  · intro h he
    exact h (congrArg (routedCoordinate n P S) he)
  · intro h he
    exact h (routedCoordinate_injective_live (switchedRoutedSuccessor_preserves_live hl) hl he)

theorem gridRoutedPredecessor_ne_iff {n : ℕ} {P S : ℕ → ℕ} {v : WireNode}
    (hl : liveWireNode n P S v) :
    gridRoutedPredecessor n P S (routedCoordinate n P S v) ≠ routedCoordinate n P S v ↔
      switchedRoutedPredecessor n P S v ≠ v := by
  rw [gridRoutedPredecessor_encode hl]
  constructor
  · intro h he
    exact h (congrArg (routedCoordinate n P S) he)
  · intro h he
    exact h (routedCoordinate_injective_live (switchedRoutedPredecessor_preserves_live hl) hl he)

/-- Every nontrivial outgoing grid edge has its matching incoming edge. -/
theorem gridRouted_successor_consistent (n : ℕ) (P S : ℕ → ℕ) (p : ℕ × ℕ)
    (hs : gridRoutedSuccessor n P S p ≠ p) :
    gridRoutedPredecessor n P S (gridRoutedSuccessor n P S p) = p := by
  cases hd : decodeWireNode n P S p with
  | none => exact False.elim (hs (by simp [gridRoutedSuccessor, hd]))
  | some v =>
    obtain ⟨hl, rfl⟩ := decodeWireNode_eq_some_iff.mp hd
    have hv := (gridRoutedSuccessor_ne_iff hl).mp hs
    rw [gridRoutedSuccessor_encode hl,
      gridRoutedPredecessor_encode (switchedRoutedSuccessor_preserves_live hl)]
    exact congrArg (routedCoordinate n P S) (switchedRouted_successor_consistent n P S v hv)

/-- Every nontrivial incoming grid edge has its matching outgoing edge. -/
theorem gridRouted_predecessor_consistent (n : ℕ) (P S : ℕ → ℕ) (p : ℕ × ℕ)
    (hp : gridRoutedPredecessor n P S p ≠ p) :
    gridRoutedSuccessor n P S (gridRoutedPredecessor n P S p) = p := by
  cases hd : decodeWireNode n P S p with
  | none => exact False.elim (hp (by simp [gridRoutedPredecessor, hd]))
  | some v =>
    obtain ⟨hl, rfl⟩ := decodeWireNode_eq_some_iff.mp hd
    have hv := (gridRoutedPredecessor_ne_iff hl).mp hp
    rw [gridRoutedPredecessor_encode hl,
      gridRoutedSuccessor_encode (switchedRoutedPredecessor_preserves_live hl)]
    exact congrArg (routedCoordinate n P S) (switchedRouted_predecessor_consistent n P S v hv)

theorem gridRouted_hasSuccessor_iff {n : ℕ} {P S : ℕ → ℕ} {v : WireNode}
    (hl : liveWireNode n P S v) :
    HasSuccessor (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S)
        (routedCoordinate n P S v) ↔
      HasSuccessor (switchedRoutedPredecessor n P S) (switchedRoutedSuccessor n P S) v := by
  constructor
  · intro h
    have hs := (gridRoutedSuccessor_ne_iff hl).mp h.1
    exact ⟨hs, switchedRouted_successor_consistent n P S v hs⟩
  · intro h
    have hs := (gridRoutedSuccessor_ne_iff hl).mpr h.1
    exact ⟨hs, gridRouted_successor_consistent n P S _ hs⟩

theorem gridRouted_hasPredecessor_iff {n : ℕ} {P S : ℕ → ℕ} {v : WireNode}
    (hl : liveWireNode n P S v) :
    HasPredecessor (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S)
        (routedCoordinate n P S v) ↔
      HasPredecessor (switchedRoutedPredecessor n P S) (switchedRoutedSuccessor n P S) v := by
  constructor
  · intro h
    have hp := (gridRoutedPredecessor_ne_iff hl).mp h.1
    exact ⟨hp, switchedRouted_predecessor_consistent n P S v hp⟩
  · intro h
    have hp := (gridRoutedPredecessor_ne_iff hl).mpr h.1
    exact ⟨hp, gridRouted_predecessor_consistent n P S _ hp⟩

theorem gridRouted_endpoint_iff {n : ℕ} {P S : ℕ → ℕ} {v : WireNode}
    (hl : liveWireNode n P S v) :
    IsEndpoint (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S)
        (routedCoordinate n P S v) ↔
      IsEndpoint (switchedRoutedPredecessor n P S) (switchedRoutedSuccessor n P S) v := by
  simp only [IsEndpoint, gridRouted_hasSuccessor_iff hl, gridRouted_hasPredecessor_iff hl]

/-- Points outside the live image have no incident routed edges. -/
theorem gridRouted_background {n : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hd : decodeWireNode n P S p = none) :
    gridRoutedPredecessor n P S p = p ∧ gridRoutedSuccessor n P S p = p := by
  simp [gridRoutedPredecessor, gridRoutedSuccessor, hd]

/-- Every grid endpoint decodes to a bounded original endpoint, on every component. -/
theorem gridRouted_endpoint_decodes {n : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hP : ∀ i, i < n → P i < n) (hS : ∀ i, i < n → S i < n)
    (he : IsEndpoint (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S) p) :
    ∃ i, i < n ∧ p = vertexPoint i ∧ IsEndpoint P S i := by
  cases hd : decodeWireNode n P S p with
  | none =>
    have h := gridRouted_background hd
    rcases he with ⟨hs, _⟩ | ⟨hp, _⟩
    · exact False.elim (hs.1 h.2)
    · exact False.elim (hp.1 h.1)
  | some v =>
    obtain ⟨hl, hcoord⟩ := decodeWireNode_eq_some_iff.mp hd
    rw [← hcoord] at he
    obtain ⟨i, rfl, hi, hend⟩ := switchedRouted_endpoint_decodes hP hS
      ((gridRouted_endpoint_iff hl).mp he)
    exact ⟨i, hi, hcoord.symm, hend⟩

/-- An endpoint's original label is obtained directly from its boundary row. -/
theorem gridRouted_endpoint_label {n : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hP : ∀ i, i < n → P i < n) (hS : ∀ i, i < n → S i < n)
    (he : IsEndpoint (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S) p) :
    p.1 = 0 ∧ p.2 / 6 < n ∧ IsEndpoint P S (p.2 / 6) := by
  obtain ⟨i, hi, rfl, hend⟩ := gridRouted_endpoint_decodes hP hS he
  simpa [vertexPoint] using (show 0 = 0 ∧ i < n ∧ IsEndpoint P S i from ⟨rfl, hi, hend⟩)

/-- Original bounded vertices have exactly their original endpoint status. -/
theorem gridRouted_vertex_endpoint_iff {n i : ℕ} {P S : ℕ → ℕ} (hi : i < n)
    (hP : ∀ j, j < n → P j < n) (hS : ∀ j, j < n → S j < n) :
    IsEndpoint (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S) (vertexPoint i) ↔
      IsEndpoint P S i :=
  (gridRouted_endpoint_iff (show liveWireNode n P S (.inl i) from hi)).trans
    ((switchedRouted_endpoint_iff n P S (.inl i)).trans (routed_vertex_endpoint_iff hi hP hS))

/-- A known bounded source remains a known grid source. -/
theorem gridRouted_source {n origin : ℕ} {P S : ℕ → ℕ} (hi : origin < n)
    (hSi : S origin < n) (hP : P origin = origin) (hS : S origin ≠ origin)
    (hlink : P (S origin) = origin) :
    gridRoutedPredecessor n P S (vertexPoint origin) = vertexPoint origin ∧
      gridRoutedSuccessor n P S (vertexPoint origin) ≠ vertexPoint origin ∧
      gridRoutedPredecessor n P S
        (gridRoutedSuccessor n P S (vertexPoint origin)) = vertexPoint origin := by
  have hl : liveWireNode n P S (.inl origin) := hi
  have h := switchedRouted_source hi hSi hP hS hlink
  have hs := (gridRoutedSuccessor_ne_iff hl).mpr h.2.1
  refine ⟨?_, hs, gridRouted_successor_consistent n P S _ hs⟩
  change gridRoutedPredecessor n P S (routedCoordinate n P S (.inl origin)) = _
  rw [gridRoutedPredecessor_encode hl, h.1]
  rfl

/-- Every nontrivial global successor follows a unit grid edge. -/
theorem gridRoutedSuccessor_adjacent (n : ℕ) (P S : ℕ → ℕ) (p : ℕ × ℕ)
    (hs : gridRoutedSuccessor n P S p ≠ p) :
    GameTheory.Math.GridCrossing.axisUnitAdjacent p (gridRoutedSuccessor n P S p) := by
  cases hd : decodeWireNode n P S p with
  | none => exact False.elim (hs (by simp [gridRoutedSuccessor, hd]))
  | some v =>
    obtain ⟨hl, rfl⟩ := decodeWireNode_eq_some_iff.mp hd
    rw [gridRoutedSuccessor_encode hl]
    exact switchedRoutedSuccessor_adjacent hl ((gridRoutedSuccessor_ne_iff hl).mp hs)

/-- Every nontrivial global predecessor follows a unit grid edge. -/
theorem gridRoutedPredecessor_adjacent (n : ℕ) (P S : ℕ → ℕ) (p : ℕ × ℕ)
    (hp : gridRoutedPredecessor n P S p ≠ p) :
    GameTheory.Math.GridCrossing.axisUnitAdjacent p (gridRoutedPredecessor n P S p) := by
  cases hd : decodeWireNode n P S p with
  | none => exact False.elim (hp (by simp [gridRoutedPredecessor, hd]))
  | some v =>
    obtain ⟨hl, rfl⟩ := decodeWireNode_eq_some_iff.mp hd
    rw [gridRoutedPredecessor_encode hl]
    exact switchedRoutedPredecessor_adjacent hl ((gridRoutedPredecessor_ne_iff hl).mp hp)

end GameTheory.Math.GridWire
