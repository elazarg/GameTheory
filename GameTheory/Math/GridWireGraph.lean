import GameTheory.Math.GridWireLanes

/-! A whole bounded pointer graph is routed through source-indexed grid wires.
Interiors retain their source labels, so crossings have separate occurrences.
Only the original vertices can be endpoints; rejected labels remain isolated. -/

namespace GameTheory.Math.GridWire

open EndOfLine

/-- Original vertices and source-indexed interior grid points. -/
abbrev WireNode := ℕ ⊕ (ℕ × (ℕ × ℕ))

/-- A bounded, nontrivial, mutually consistent original edge. -/
def activeEdge (n : ℕ) (P S : ℕ → ℕ) (i : ℕ) : Prop :=
  i < n ∧ S i < n ∧ HasSuccessor P S i

instance (n : ℕ) (P S : ℕ → ℕ) (i : ℕ) : Decidable (activeEdge n P S i) :=
  inferInstanceAs (Decidable (i < n ∧ S i < n ∧ HasSuccessor P S i))

/-- Bounded original vertices and active interior wire points are live. -/
def liveWireNode (n : ℕ) (P S : ℕ → ℕ) : WireNode → Prop
  | .inl i => i < n
  | .inr (i, p) => activeEdge n P S i ∧ onWire n i (S i) p ∧
      p ≠ vertexPoint i ∧ p ≠ vertexPoint (S i)

instance (n : ℕ) (P S : ℕ → ℕ) (v : WireNode) : Decidable (liveWireNode n P S v) := by
  cases v with
  | inl i => exact inferInstanceAs (Decidable (i < n))
  | inr ip => exact inferInstanceAs (Decidable
      (activeEdge n P S ip.1 ∧ onWire n ip.1 (S ip.1) ip.2 ∧
        ip.2 ≠ vertexPoint ip.1 ∧ ip.2 ≠ vertexPoint (S ip.1)))

/-- Rejoin the two ends of a source-indexed wire to their original vertices. -/
def embedWire (S : ℕ → ℕ) (i : ℕ) (p : ℕ × ℕ) : WireNode :=
  if p = vertexPoint i then .inl i
  else if p = vertexPoint (S i) then .inl (S i) else .inr (i, p)

/-- The geometric point represented by an original vertex or an interior label. -/
def wireNodePoint : WireNode → ℕ × ℕ
  | .inl i => vertexPoint i
  | .inr (_, p) => p

@[simp] theorem wireNodePoint_embedWire (S : ℕ → ℕ) (i : ℕ) (p : ℕ × ℕ) :
    wireNodePoint (embedWire S i p) = p := by
  unfold embedWire
  split_ifs <;> simp_all [wireNodePoint]

theorem embedWire_injective (S : ℕ → ℕ) (i : ℕ) : Function.Injective (embedWire S i) := by
  intro p q h
  simpa only [wireNodePoint_embedWire] using congrArg wireNodePoint h

/-- Follow the source-indexed outgoing wire, retaining invalid nodes as self-loops. -/
def routedSuccessor (n : ℕ) (P S : ℕ → ℕ) : WireNode → WireNode
  | .inl i => if activeEdge n P S i then
      embedWire S i (wireSuccessor n i (S i) (vertexPoint i)) else .inl i
  | .inr (i, p) => if liveWireNode n P S (.inr (i, p)) then
      embedWire S i (wireSuccessor n i (S i) p) else .inr (i, p)

/-- Follow the predecessor's incoming wire, retaining invalid nodes as self-loops. -/
def routedPredecessor (n : ℕ) (P S : ℕ → ℕ) : WireNode → WireNode
  | .inl i => if activeEdge n P S (P i) ∧ S (P i) = i then
      embedWire S (P i) (wirePredecessor n (P i) i (vertexPoint i)) else .inl i
  | .inr (i, p) => if liveWireNode n P S (.inr (i, p)) then
      embedWire S i (wirePredecessor n i (S i) p) else .inr (i, p)

private theorem source_onWire (n i j : ℕ) : onWire n i j (vertexPoint i) :=
  Or.inl ⟨rfl, Nat.zero_le _⟩

private theorem target_onWire (n i j : ℕ) : onWire n i j (vertexPoint j) :=
  Or.inr (Or.inr (Or.inr ⟨rfl, le_rfl, by simp only [vertexPoint]; omega⟩))

private theorem vertex_ne {i j : ℕ} (h : i ≠ j) : vertexPoint i ≠ vertexPoint j :=
  fun he => h (vertexPoint_injective he)

private theorem embedWire_source (S : ℕ → ℕ) (i : ℕ) :
    embedWire S i (vertexPoint i) = .inl i := by simp [embedWire]

private theorem embedWire_target {S : ℕ → ℕ} {i : ℕ} (hne : S i ≠ i) :
    embedWire S i (vertexPoint (S i)) = .inl (S i) := by
  simp [embedWire, vertex_ne hne]

/-- Along one active wire, outgoing execution commutes with its embedding
until its target vertex is reached. -/
theorem routedSuccessor_embedWire {n i : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (ha : activeEdge n P S i) (hp : onWire n i (S i) p)
    (ht : p ≠ vertexPoint (S i)) :
    routedSuccessor n P S (embedWire S i p) = embedWire S i (wireSuccessor n i (S i) p) := by
  by_cases hi : p = vertexPoint i
  · subst p
    rw [embedWire_source, routedSuccessor, ite_eq_left ha]
  · simp [embedWire, hi, ht, routedSuccessor, liveWireNode, ha, hp]

/-- Incoming execution commutes with one active wire away from its source. -/
theorem routedPredecessor_embedWire {n i : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (ha : activeEdge n P S i) (hp : onWire n i (S i) p) (hs : p ≠ vertexPoint i) :
    routedPredecessor n P S (embedWire S i p) =
      embedWire S i (wirePredecessor n i (S i) p) := by
  by_cases ht : p = vertexPoint (S i)
  · subst p
    rw [embedWire_target ha.2.2.1]
    simp [routedPredecessor, ha.2.2.2, ha]
  · simp [embedWire, hs, ht, routedPredecessor, liveWireNode, ha, hp]

/-- An active local outgoing edge stays reciprocal after its wire ends are joined. -/
theorem routed_hasSuccessor_onWire {n i : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (ha : activeEdge n P S i) (hp : onWire n i (S i) p)
    (ht : p ≠ vertexPoint (S i)) :
    HasSuccessor (routedPredecessor n P S) (routedSuccessor n P S) (embedWire S i p) := by
  have hs := (wireSuccessor_ne_iff ha.1 ha.2.2.1.symm p).mpr ⟨hp, ht⟩
  have hb := wire_successor_consistent ha.1 ha.2.2.1.symm p hs
  have hq := (wirePredecessor_ne_iff ha.1 ha.2.2.1.symm
    (wireSuccessor n i (S i) p)).mp (by rw [hb]; exact hs.symm)
  constructor
  · rw [routedSuccessor_embedWire ha hp ht]
    exact fun h => hs (embedWire_injective S i h)
  · rw [routedSuccessor_embedWire ha hp ht, routedPredecessor_embedWire ha hq.1 hq.2, hb]

/-- An active local incoming edge stays reciprocal after its wire ends are joined. -/
theorem routed_hasPredecessor_onWire {n i : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (ha : activeEdge n P S i) (hp : onWire n i (S i) p) (hs : p ≠ vertexPoint i) :
    HasPredecessor (routedPredecessor n P S) (routedSuccessor n P S) (embedWire S i p) := by
  have ht := (wirePredecessor_ne_iff ha.1 ha.2.2.1.symm p).mpr ⟨hp, hs⟩
  have hb := wire_predecessor_consistent ha.1 ha.2.2.1.symm p ht
  have hq := (wireSuccessor_ne_iff ha.1 ha.2.2.1.symm
    (wirePredecessor n i (S i) p)).mp (by rw [hb]; exact ht.symm)
  constructor
  · rw [routedPredecessor_embedWire ha hp hs]
    exact fun h => ht (embedWire_injective S i h)
  · rw [routedPredecessor_embedWire ha hp hs, routedSuccessor_embedWire ha hq.1 hq.2, hb]

/-- Original vertices retain exactly their active outgoing edge. -/
theorem routed_hasSuccessor_vertex_iff (n i : ℕ) (P S : ℕ → ℕ) :
    HasSuccessor (routedPredecessor n P S) (routedSuccessor n P S) (.inl i) ↔
      activeEdge n P S i := by
  constructor
  · intro h
    by_contra ha
    exact h.1 (by simp [routedSuccessor, ha])
  · intro ha
    have h := routed_hasSuccessor_onWire ha (source_onWire n i (S i))
      (vertex_ne ha.2.2.1.symm)
    simpa only [embedWire_source] using h

private theorem incoming_active_iff (n i : ℕ) (P S : ℕ → ℕ) :
    (activeEdge n P S (P i) ∧ S (P i) = i) ↔
      i < n ∧ P i < n ∧ HasPredecessor P S i := by
  constructor
  · intro h
    have hne : i ≠ P i := by simpa only [h.2] using h.1.2.2.1
    exact ⟨by simpa only [h.2] using h.1.2.1, h.1.1, hne.symm, h.2⟩
  · rintro ⟨hi, hp, hne, he⟩
    exact ⟨⟨hp, by simpa only [he] using hi,
      by simpa only [he] using hne.symm, by rw [he]⟩, he⟩

/-- Original vertices retain exactly their bounded incoming edge. -/
theorem routed_hasPredecessor_vertex_iff (n i : ℕ) (P S : ℕ → ℕ) :
    HasPredecessor (routedPredecessor n P S) (routedSuccessor n P S) (.inl i) ↔
      i < n ∧ P i < n ∧ HasPredecessor P S i := by
  rw [← incoming_active_iff]
  constructor
  · intro h
    by_contra ha
    exact h.1 (by simp [routedPredecessor, ha])
  · intro ha
    have h := routed_hasPredecessor_onWire ha.1 (target_onWire n (P i) (S (P i)))
      (vertex_ne ha.1.2.2.1)
    rw [embedWire_target ha.1.2.2.1] at h
    simpa only [ha.2] using h

/-- Every live interior has both incident edge roles. -/
theorem routed_interior_roles {n i : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hl : liveWireNode n P S (.inr (i, p))) :
    HasSuccessor (routedPredecessor n P S) (routedSuccessor n P S) (.inr (i, p)) ∧
      HasPredecessor (routedPredecessor n P S) (routedSuccessor n P S) (.inr (i, p)) := by
  have he : embedWire S i p = .inr (i, p) := by simp [embedWire, hl.2.2.1, hl.2.2.2]
  rw [← he]
  exact ⟨routed_hasSuccessor_onWire hl.1 hl.2.1 hl.2.2.2,
    routed_hasPredecessor_onWire hl.1 hl.2.1 hl.2.2.1⟩

/-- No live or rejected interior label can be an endpoint. -/
theorem routed_interior_not_endpoint (n i : ℕ) (P S : ℕ → ℕ) (p : ℕ × ℕ) :
    ¬IsEndpoint (routedPredecessor n P S) (routedSuccessor n P S) (.inr (i, p)) := by
  by_cases hl : liveWireNode n P S (.inr (i, p))
  · have h := routed_interior_roles hl
    rintro (⟨_, hn⟩ | ⟨_, hn⟩)
    · exact hn h.2
    · exact hn h.1
  · simp [IsEndpoint, HasSuccessor, HasPredecessor, routedSuccessor, routedPredecessor, hl]

/-- Every nontrivial global successor has the matching global predecessor. -/
theorem routed_successor_consistent (n : ℕ) (P S : ℕ → ℕ) (node : WireNode)
    (hs : routedSuccessor n P S node ≠ node) :
    routedPredecessor n P S (routedSuccessor n P S node) = node := by
  cases node with
  | inl i =>
    have ha : activeEdge n P S i := by
      by_contra h
      exact hs (by simp [routedSuccessor, h])
    exact ((routed_hasSuccessor_vertex_iff n i P S).mpr ha).2
  | inr ip =>
    have hl : liveWireNode n P S (.inr ip) := by
      by_contra h
      exact hs (by simp [routedSuccessor, h])
    exact (routed_interior_roles hl).1.2

/-- Every nontrivial global predecessor has the matching global successor. -/
theorem routed_predecessor_consistent (n : ℕ) (P S : ℕ → ℕ) (node : WireNode)
    (hp : routedPredecessor n P S node ≠ node) :
    routedSuccessor n P S (routedPredecessor n P S node) = node := by
  cases node with
  | inl i =>
    have ha : activeEdge n P S (P i) ∧ S (P i) = i := by
      by_contra h
      exact hp (by simp [routedPredecessor, h])
    exact ((routed_hasPredecessor_vertex_iff n i P S).mpr
      ((incoming_active_iff n i P S).mp ha)).2
  | inr ip =>
    have hl : liveWireNode n P S (.inr ip) := by
      by_contra h
      exact hp (by simp [routedPredecessor, h])
    exact (routed_interior_roles hl).2.2

/-- Routing preserves the endpoint predicate at every bounded original vertex
when both original pointers preserve the bounded vertex set. -/
theorem routed_vertex_endpoint_iff {n i : ℕ} {P S : ℕ → ℕ} (hi : i < n)
    (hP : ∀ j, j < n → P j < n) (hS : ∀ j, j < n → S j < n) :
    IsEndpoint (routedPredecessor n P S) (routedSuccessor n P S) (.inl i) ↔
      IsEndpoint P S i := by
  simp only [IsEndpoint, routed_hasSuccessor_vertex_iff, routed_hasPredecessor_vertex_iff,
    activeEdge, hi, hP i hi, hS i hi, true_and]

/-- Every routed endpoint is a bounded original vertex and an original endpoint. -/
theorem routed_endpoint_decodes {n : ℕ} {P S : ℕ → ℕ}
    (hP : ∀ j, j < n → P j < n) (hS : ∀ j, j < n → S j < n)
    {node : WireNode} (he : IsEndpoint (routedPredecessor n P S) (routedSuccessor n P S) node) :
    ∃ i, node = .inl i ∧ i < n ∧ IsEndpoint P S i := by
  cases node with
  | inr ip => exact False.elim (routed_interior_not_endpoint n ip.1 P S ip.2 he)
  | inl i =>
    have hi : i < n := by
      rcases he with ⟨hs, _⟩ | ⟨hp, _⟩
      · exact ((routed_hasSuccessor_vertex_iff n i P S).mp hs).1
      · exact ((routed_hasPredecessor_vertex_iff n i P S).mp hp).1
    exact ⟨i, rfl, hi, (routed_vertex_endpoint_iff hi hP hS).mp he⟩

/-- A known bounded source remains a known source after routing. -/
theorem routed_source {n origin : ℕ} {P S : ℕ → ℕ} (hi : origin < n)
    (hSi : S origin < n) (hP : P origin = origin) (hS : S origin ≠ origin)
    (hlink : P (S origin) = origin) :
    routedPredecessor n P S (.inl origin) = .inl origin ∧
      routedSuccessor n P S (.inl origin) ≠ .inl origin ∧
      routedPredecessor n P S (routedSuccessor n P S (.inl origin)) = .inl origin := by
  have h := (routed_hasSuccessor_vertex_iff n origin P S).mpr ⟨hi, hSi, hS, hlink⟩
  exact ⟨by simp [routedPredecessor, hP, hS], h⟩

end GameTheory.Math.GridWire
