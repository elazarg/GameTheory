import GameTheory.Math.GridWireRealization
import GameTheory.Math.EndOfLineTailSwitch

/-! Crossing switches exchange the two source-indexed wire occurrences at a
crossing center. Their outgoing continuations change; original vertices and
incident edge roles remain fixed. Live labels stay live after every pointer step. -/

namespace GameTheory.Math.GridWire

open GameTheory.Math.GridCrossing GameTheory.Math.EndOfLine

/-- Exchange the two wire occurrences at a genuine crossing center. -/
def routedSwitch (n : ℕ) (P S : ℕ → ℕ) : WireNode → WireNode
  | .inl i => .inl i
  | .inr (a, p) =>
    match crossingOwners n P S p with
    | none => .inr (a, p)
    | some (i, k) =>
      if a = i then .inr (k, p) else if a = k then .inr (i, p) else .inr (a, p)

/-- Swapping crossing occurrences twice restores the original label. -/
theorem routedSwitch_involutive (n : ℕ) (P S : ℕ → ℕ) :
    Function.Involutive (routedSwitch n P S) := by
  intro node
  cases node with
  | inl i => rfl
  | inr ap =>
    rcases ap with ⟨a, p⟩
    cases hc : crossingOwners n P S p with
    | none => simp [routedSwitch, hc]
    | some owners =>
      rcases owners with ⟨i, k⟩
      have hne := (crossingOwners_sound hc).2.2.2.2.1
      by_cases ha : a = i
      · subst a
        simp [routedSwitch, hc, hne.symm]
      · by_cases hk : a = k
        · subst a
          simp [routedSwitch, hc, hne.symm]
        · simp [routedSwitch, hc, ha, hk]

theorem crossingOwners_nodes_live {n i k : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hc : crossingOwners n P S p = some (i, k)) :
    liveWireNode n P S (.inr (i, p)) ∧ liveWireNode n P S (.inr (k, p)) := by
  obtain ⟨hi, hk, hsi, hsk, _, hai, hak, hh, hv⟩ := crossingOwners_sound hc
  have hx := (crossing_clearance hh hv).1
  have hp : ∀ a, p ≠ vertexPoint a := by
    intro a he
    have he' := congrArg Prod.fst he
    simp only [vertexPoint] at he'
    omega
  have hhwire : onWire n i (S i) p := by
    rcases hh.2.2 with h | h
    · exact Or.inl ⟨h, Nat.le_of_lt hh.2.1⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h, Nat.le_of_lt hh.2.1⟩))
  have hvwire : onWire n k (S k) p :=
    Or.inr (Or.inl ⟨hv.1, Nat.le_of_lt hv.2.1, Nat.le_of_lt hv.2.2⟩)
  exact ⟨⟨⟨hi, hsi, hai⟩, hhwire, hp i, hp (S i)⟩,
    ⟨⟨hk, hsk, hak⟩, hvwire, hp k, hp (S k)⟩⟩

/-- Every changed label is a live interior of an active wire. -/
theorem routedSwitch_changes_live {n : ℕ} {P S : ℕ → ℕ} {node : WireNode}
    (h : routedSwitch n P S node ≠ node) : liveWireNode n P S node := by
  cases node with
  | inl i => exact False.elim (h rfl)
  | inr ap =>
    rcases ap with ⟨a, p⟩
    cases hc : crossingOwners n P S p with
    | none => exact False.elim (h (by simp [routedSwitch, hc]))
    | some owners =>
      rcases owners with ⟨i, k⟩
      by_cases ha : a = i
      · subst a
        exact (crossingOwners_nodes_live hc).1
      · by_cases hk : a = k
        · subst a
          exact (crossingOwners_nodes_live hc).2
        · exact False.elim (h (by simp [routedSwitch, hc, ha, hk]))

/-- Crossing swaps preserve liveness in both directions. -/
theorem routedSwitch_live_iff (n : ℕ) (P S : ℕ → ℕ) (node : WireNode) :
    liveWireNode n P S (routedSwitch n P S node) ↔ liveWireNode n P S node := by
  by_cases h : routedSwitch n P S node = node
  · rw [h]
  · have hl := routedSwitch_changes_live h
    have hl' := routedSwitch_changes_live
      (show routedSwitch n P S (routedSwitch n P S node) ≠ routedSwitch n P S node by
        rw [routedSwitch_involutive n P S node]
        exact Ne.symm h)
    exact ⟨fun _ => hl, fun _ => hl'⟩

/-- A changed label has both original routed incident edge roles. -/
theorem routedSwitch_changed_roles {n : ℕ} {P S : ℕ → ℕ} {node : WireNode}
    (h : routedSwitch n P S node ≠ node) :
    HasSuccessor (routedPredecessor n P S) (routedSuccessor n P S) node ∧
      HasPredecessor (routedPredecessor n P S) (routedSuccessor n P S) node := by
  cases node with
  | inl i => exact False.elim (h rfl)
  | inr ap => exact routed_interior_roles (routedSwitch_changes_live h)

private theorem interior_successor_point_moves {n i : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hl : liveWireNode n P S (.inr (i, p))) :
    wireNodePoint (routedSuccessor n P S (.inr (i, p))) ≠ p := by
  rw [routedSuccessor, ite_eq_left hl, wireNodePoint_embedWire]
  exact (wireSuccessor_ne_iff hl.1.1 hl.1.2.2.1.symm p).mpr ⟨hl.2.1, hl.2.2.2⟩

/-- The exchanged pair was not an original directed edge in the routed graph. -/
theorem routedSwitch_no_old_edge {n : ℕ} {P S : ℕ → ℕ} {node : WireNode}
    (h : routedSwitch n P S node ≠ node) :
    routedSuccessor n P S (routedSwitch n P S node) ≠ node := by
  cases node with
  | inl i => exact False.elim (h rfl)
  | inr ap =>
    rcases ap with ⟨a, p⟩
    cases hc : crossingOwners n P S p with
    | none => exact False.elim (h (by simp [routedSwitch, hc]))
    | some owners =>
      rcases owners with ⟨i, k⟩
      by_cases ha : a = i
      · subst a
        simp only [routedSwitch, hc, ↓reduceIte]
        intro he
        exact interior_successor_point_moves (crossingOwners_nodes_live hc).2
          (congrArg wireNodePoint he)
      · by_cases hk : a = k
        · subst a
          simp only [routedSwitch, hc, ite_eq_right ha, ↓reduceIte]
          intro he
          exact interior_successor_point_moves (crossingOwners_nodes_live hc).1
            (congrArg wireNodePoint he)
        · exact False.elim (h (by simp [routedSwitch, hc, ha, hk]))

/-- Follow the outgoing continuation of the exchanged crossing occurrence. -/
def switchedRoutedSuccessor (n : ℕ) (P S : ℕ → ℕ) : WireNode → WireNode :=
  routedSuccessor n P S ∘ routedSwitch n P S

/-- Exchange the arrival occurrence after following the original incoming pointer. -/
def switchedRoutedPredecessor (n : ℕ) (P S : ℕ → ℕ) : WireNode → WireNode :=
  routedSwitch n P S ∘ routedPredecessor n P S

private theorem live_embedWire {n i : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (ha : activeEdge n P S i) (hp : onWire n i (S i) p) :
    liveWireNode n P S (embedWire S i p) := by
  unfold embedWire
  split_ifs with hs ht
  · exact ha.1
  · exact ha.2.1
  · exact ⟨ha, hp, hs, ht⟩

private theorem successor_onWire {n i : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (ha : activeEdge n P S i) (hp : onWire n i (S i) p) :
    onWire n i (S i) (wireSuccessor n i (S i) p) := by
  by_cases hs : wireSuccessor n i (S i) p = p
  · rw [hs]
    exact hp
  · have hb := wire_successor_consistent ha.1 ha.2.2.1.symm p hs
    exact ((wirePredecessor_ne_iff ha.1 ha.2.2.1.symm _).mp
      (by rw [hb]; exact Ne.symm hs)).1

private theorem predecessor_onWire {n i : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (ha : activeEdge n P S i) (hp : onWire n i (S i) p) :
    onWire n i (S i) (wirePredecessor n i (S i) p) := by
  by_cases hs : wirePredecessor n i (S i) p = p
  · rw [hs]
    exact hp
  · have hb := wire_predecessor_consistent ha.1 ha.2.2.1.symm p hs
    exact ((wireSuccessor_ne_iff ha.1 ha.2.2.1.symm _).mp
      (by rw [hb]; exact Ne.symm hs)).1

/-- Original routed successors preserve the valid realization domain. -/
theorem routedSuccessor_preserves_live {n : ℕ} {P S : ℕ → ℕ} {node : WireNode}
    (hl : liveWireNode n P S node) : liveWireNode n P S (routedSuccessor n P S node) := by
  cases node with
  | inl i =>
    by_cases ha : activeEdge n P S i
    · rw [routedSuccessor, ite_eq_left ha]
      exact live_embedWire ha (successor_onWire ha (Or.inl ⟨rfl, Nat.zero_le _⟩))
    · simpa only [routedSuccessor, ite_eq_right ha] using hl
  | inr ap =>
    rw [routedSuccessor, ite_eq_left hl]
    exact live_embedWire hl.1 (successor_onWire hl.1 hl.2.1)

/-- Original routed predecessors preserve the valid realization domain. -/
theorem routedPredecessor_preserves_live {n : ℕ} {P S : ℕ → ℕ} {node : WireNode}
    (hl : liveWireNode n P S node) : liveWireNode n P S (routedPredecessor n P S node) := by
  cases node with
  | inl i =>
    by_cases ha : activeEdge n P S (P i) ∧ S (P i) = i
    · rw [routedPredecessor, ite_eq_left ha]
      have hp : onWire n (P i) (S (P i)) (vertexPoint (S (P i))) :=
        Or.inr (Or.inr (Or.inr ⟨rfl, le_rfl, by simp only [vertexPoint]; omega⟩))
      have h := live_embedWire ha.1 (predecessor_onWire ha.1 hp)
      simpa only [ha.2] using h
    · simpa only [routedPredecessor, ite_eq_right ha] using hl
  | inr ap =>
    rw [routedPredecessor, ite_eq_left hl]
    exact live_embedWire hl.1 (predecessor_onWire hl.1 hl.2.1)

/-- Switched successors preserve the valid realization domain. -/
theorem switchedRoutedSuccessor_preserves_live {n : ℕ} {P S : ℕ → ℕ} {node : WireNode}
    (hl : liveWireNode n P S node) :
    liveWireNode n P S (switchedRoutedSuccessor n P S node) :=
  routedSuccessor_preserves_live ((routedSwitch_live_iff n P S node).mpr hl)

/-- Switched predecessors preserve the valid realization domain. -/
theorem switchedRoutedPredecessor_preserves_live {n : ℕ} {P S : ℕ → ℕ} {node : WireNode}
    (hl : liveWireNode n P S node) :
    liveWireNode n P S (switchedRoutedPredecessor n P S node) :=
  (routedSwitch_live_iff n P S _).mpr (routedPredecessor_preserves_live hl)

private theorem changed_nonself (n : ℕ) (P S : ℕ → ℕ) (node : WireNode)
    (h : routedSwitch n P S node ≠ node) :
    routedPredecessor n P S node ≠ node ∧ routedSuccessor n P S node ≠ node :=
  ⟨(routedSwitch_changed_roles h).2.1, (routedSwitch_changed_roles h).1.1⟩

/-- Every nontrivial switched successor retains its reciprocal predecessor. -/
theorem switchedRouted_successor_consistent (n : ℕ) (P S : ℕ → ℕ) (node : WireNode)
    (h : switchedRoutedSuccessor n P S node ≠ node) :
    switchedRoutedPredecessor n P S (switchedRoutedSuccessor n P S node) = node :=
  tailSwitch_successor_consistent (routedPredecessor n P S) (routedSuccessor n P S)
    (routedSwitch n P S) (routedSwitch_involutive n P S) (routed_successor_consistent n P S)
    (changed_nonself n P S) node h

/-- Every nontrivial switched predecessor retains its reciprocal successor. -/
theorem switchedRouted_predecessor_consistent (n : ℕ) (P S : ℕ → ℕ) (node : WireNode)
    (h : switchedRoutedPredecessor n P S node ≠ node) :
    switchedRoutedSuccessor n P S (switchedRoutedPredecessor n P S node) = node :=
  tailSwitch_predecessor_consistent (routedPredecessor n P S) (routedSuccessor n P S)
    (routedSwitch n P S) (routedSwitch_involutive n P S) (routed_predecessor_consistent n P S)
    (changed_nonself n P S) (fun _ h => routedSwitch_no_old_edge h) node h

/-- Crossing switches preserve outgoing-edge presence at every label. -/
theorem switchedRouted_hasSuccessor_iff (n : ℕ) (P S : ℕ → ℕ) (node : WireNode) :
    HasSuccessor (switchedRoutedPredecessor n P S) (switchedRoutedSuccessor n P S) node ↔
      HasSuccessor (routedPredecessor n P S) (routedSuccessor n P S) node :=
  tailSwitch_hasSuccessor_iff (routedPredecessor n P S) (routedSuccessor n P S)
    (routedSwitch n P S) (routedSwitch_involutive n P S) (routed_successor_consistent n P S)
    (changed_nonself n P S) (fun _ h => routedSwitch_no_old_edge h) node

/-- Crossing switches preserve incoming-edge presence at every label. -/
theorem switchedRouted_hasPredecessor_iff (n : ℕ) (P S : ℕ → ℕ) (node : WireNode) :
    HasPredecessor (switchedRoutedPredecessor n P S) (switchedRoutedSuccessor n P S) node ↔
      HasPredecessor (routedPredecessor n P S) (routedSuccessor n P S) node :=
  tailSwitch_hasPredecessor_iff (routedPredecessor n P S) (routedSuccessor n P S)
    (routedSwitch n P S) (routedSwitch_involutive n P S) (routed_predecessor_consistent n P S)
    (changed_nonself n P S) (fun _ h => routedSwitch_no_old_edge h) node

/-- Simultaneous crossing switches preserve the endpoint predicate at every label. -/
theorem switchedRouted_endpoint_iff (n : ℕ) (P S : ℕ → ℕ) (node : WireNode) :
    IsEndpoint (switchedRoutedPredecessor n P S) (switchedRoutedSuccessor n P S) node ↔
      IsEndpoint (routedPredecessor n P S) (routedSuccessor n P S) node :=
  tailSwitch_isEndpoint_iff (routedPredecessor n P S) (routedSuccessor n P S)
    (routedSwitch n P S) (routedSwitch_involutive n P S)
    (routed_predecessor_consistent n P S) (routed_successor_consistent n P S)
    (changed_nonself n P S) (fun _ h => routedSwitch_no_old_edge h) node

/-- Every endpoint after crossing switches still decodes to an original graph endpoint. -/
theorem switchedRouted_endpoint_decodes {n : ℕ} {P S : ℕ → ℕ}
    (hP : ∀ i, i < n → P i < n) (hS : ∀ i, i < n → S i < n) {node : WireNode}
    (he : IsEndpoint (switchedRoutedPredecessor n P S) (switchedRoutedSuccessor n P S) node) :
    ∃ i, node = .inl i ∧ i < n ∧ IsEndpoint P S i :=
  routed_endpoint_decodes hP hS ((switchedRouted_endpoint_iff n P S node).mp he)

/-- Known sources survive the simultaneous crossing switches. -/
theorem switchedRouted_source {n origin : ℕ} {P S : ℕ → ℕ} (hi : origin < n)
    (hSi : S origin < n) (hP : P origin = origin) (hS : S origin ≠ origin)
    (hlink : P (S origin) = origin) :
    switchedRoutedPredecessor n P S (.inl origin) = .inl origin ∧
      switchedRoutedSuccessor n P S (.inl origin) ≠ .inl origin ∧
      switchedRoutedPredecessor n P S
        (switchedRoutedSuccessor n P S (.inl origin)) = .inl origin := by
  have h := routed_source hi hSi hP hS hlink
  have hs : switchedRoutedSuccessor n P S (.inl origin) ≠ .inl origin := h.2.1
  refine ⟨?_, hs, switchedRouted_successor_consistent n P S (.inl origin) hs⟩
  change routedSwitch n P S (routedPredecessor n P S (.inl origin)) = .inl origin
  rw [h.1]
  rfl

end GameTheory.Math.GridWire
