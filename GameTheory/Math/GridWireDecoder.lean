import GameTheory.Math.GridWireRealization

/-! The inverse grid map validates at most six locally computed labels. It
recovers ordinary wire points and displaced crossing centers without scanning
edges, and rejects points outside the live geometric image. -/

namespace GameTheory.Math.GridWire

open GameTheory.Math.GridCrossing GameTheory.Math.EndOfLine

/-- Vertex, horizontal, vertical and incoming-hook candidates at one grid point. -/
def ordinaryCandidates (n : ℕ) (P : ℕ → ℕ) (p : ℕ × ℕ) : List WireNode :=
  [.inl (p.2 / 6), .inr (horizontalOwner P p, p),
    .inr (verticalOwner n p, p), .inr (P (p.2 / 6), p)]

/-- Two virtual crossing-center labels supplement the four ordinary candidates. -/
def wireCandidates (n : ℕ) (P S : ℕ → ℕ) (p : ℕ × ℕ) : List WireNode :=
  let center := crossingCenter p
  match crossingOwners n P S center with
  | none => ordinaryCandidates n P p
  | some (i, k) => .inr (i, center) :: .inr (k, center) :: ordinaryCandidates n P p

theorem wireCandidates_length (n : ℕ) (P S : ℕ → ℕ) (p : ℕ × ℕ) :
    (wireCandidates n P S p).length ≤ 6 := by
  dsimp only [wireCandidates]
  split <;> simp [ordinaryCandidates]

private theorem ordinaryCandidates_mem {n : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    {v : WireNode} (h : v ∈ ordinaryCandidates n P p) : v ∈ wireCandidates n P S p := by
  dsimp only [wireCandidates]
  split <;> simp_all

private theorem ordinaryCandidates_wire {n i : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hs : S i < n) (ha : HasSuccessor P S i) (hp : onWire n i (S i) p) :
    Sum.inr (i, p) ∈ ordinaryCandidates n P p := by
  rcases hp with hp | hp | hp | hp
  · have ho : horizontalOwner P p = i := by simp [horizontalOwner, hp.1]
    simp [ordinaryCandidates, ho]
  · have hn : 0 < n := by omega
    have ho : verticalOwner n p = i := by
      simp [verticalOwner, hp.1, wireColumn, Nat.mul_add_div hn, Nat.div_eq_of_lt hs]
    simp [ordinaryCandidates, ho]
  · have hd : (6 * S i + 3) / 6 = S i := by omega
    have ho : horizontalOwner P p = i := by simp [horizontalOwner, hp.1, hd, ha.2]
    simp [ordinaryCandidates, ho]
  · have hd : p.2 / 6 = S i := by omega
    simp [ordinaryCandidates, hd, ha.2]

/-- Every live label occurs among the candidates for its geometric image. -/
theorem wireCandidates_complete {n : ℕ} {P S : ℕ → ℕ} {v : WireNode}
    (hl : liveWireNode n P S v) : v ∈ wireCandidates n P S (routedCoordinate n P S v) := by
  cases v with
  | inl i =>
    apply ordinaryCandidates_mem
    simp [ordinaryCandidates, routedCoordinate, vertexPoint]
  | inr ip =>
    rcases ip with ⟨a, p⟩
    obtain ⟨ha, hp, _, _⟩ := hl
    cases hc : crossingOwners n P S p with
    | none =>
      simp only [routedCoordinate, wireImagePoint, hc]
      exact ordinaryCandidates_mem (ordinaryCandidates_wire ha.2.1 ha.2.2 hp)
    | some owners =>
      rcases owners with ⟨i, k⟩
      obtain ⟨_, _, _, _, _, _, _, hh, hv⟩ := crossingOwners_sound hc
      have hcenter : crossingCenter (routedCoordinate n P S (.inr (a, p))) = p :=
        crossingCenter_eq (crossing_coordinates hh hv) (wireImagePoint_neighborhood hc)
      obtain rfl | rfl := crossingOwners_onWire hc ha.2.1 ha.2.2 hp <;>
        dsimp only [wireCandidates] <;> rw [hcenter, hc] <;> simp

/-- Select the first live label with exactly the requested coordinates. -/
def chooseWireNode (n : ℕ) (P S : ℕ → ℕ) (p : ℕ × ℕ) : List WireNode → Option WireNode
  | [] => none
  | v :: vs => if liveWireNode n P S v ∧ routedCoordinate n P S v = p then some v
      else chooseWireNode n P S p vs

theorem chooseWireNode_sound {n : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    {vs : List WireNode} {v : WireNode} (h : chooseWireNode n P S p vs = some v) :
    liveWireNode n P S v ∧ routedCoordinate n P S v = p := by
  induction vs with
  | nil => cases h
  | cons w ws ih =>
    dsimp only [chooseWireNode] at h
    split_ifs at h with hw
    · cases Option.some.inj h
      exact hw
    · exact ih h

theorem chooseWireNode_complete {n : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    {vs : List WireNode} {v : WireNode} (hl : liveWireNode n P S v)
    (he : routedCoordinate n P S v = p) (hm : v ∈ vs) :
    chooseWireNode n P S p vs = some v := by
  induction vs with
  | nil => cases hm
  | cons w ws ih =>
    dsimp only [chooseWireNode]
    split_ifs with hw
    · have h := routedCoordinate_injective_live hw.1 hl (hw.2.trans he.symm)
      rw [h]
    · have hmem : v ∈ ws := by
        rcases List.mem_cons.mp hm with h | h
        · subst w
          exact False.elim (hw ⟨hl, he⟩)
        · exact h
      exact ih hmem

/-- Decode one grid point using the bounded local candidate list. -/
def decodeWireNode (n : ℕ) (P S : ℕ → ℕ) (p : ℕ × ℕ) : Option WireNode :=
  chooseWireNode n P S p (wireCandidates n P S p)

theorem decodeWireNode_roundtrip {n : ℕ} {P S : ℕ → ℕ} {v : WireNode}
    (hl : liveWireNode n P S v) :
    decodeWireNode n P S (routedCoordinate n P S v) = some v :=
  chooseWireNode_complete hl rfl (wireCandidates_complete hl)

theorem decodeWireNode_eq_some_iff {n : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ} {v : WireNode} :
    decodeWireNode n P S p = some v ↔
      liveWireNode n P S v ∧ routedCoordinate n P S v = p := by
  constructor
  · exact chooseWireNode_sound
  · rintro ⟨hl, rfl⟩
    exact decodeWireNode_roundtrip hl

end GameTheory.Math.GridWire
