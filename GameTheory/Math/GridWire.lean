import GameTheory.Math.GridCrossingGeometry

/-! A routed edge uses a private vertical column, two horizontal segments, and
a short downward hook into its target vertex. Successor and predecessor inspect
only the current point. Points outside the route remain isolated. -/

namespace GameTheory.Math.GridWire

/-- The grid location of a graph vertex. -/
def vertexPoint (i : ℕ) : ℕ × ℕ := (0, 6 * i)

/-- The vertical routing column allocated to an ordered pair of vertices. -/
def wireColumn (n i j : ℕ) : ℕ := 3 * (n * i + j)

/-- The four closed segments of the routed edge from vertex `i` to vertex `j`. -/
def onWire (n i j : ℕ) (p : ℕ × ℕ) : Prop :=
  (p.2 = 6 * i ∧ p.1 ≤ wireColumn n i j) ∨
    (p.1 = wireColumn n i j ∧ min (6 * i) (6 * j + 3) ≤ p.2 ∧
      p.2 ≤ max (6 * i) (6 * j + 3)) ∨
    (p.2 = 6 * j + 3 ∧ p.1 ≤ wireColumn n i j) ∨
    (p.1 = 0 ∧ 6 * j ≤ p.2 ∧ p.2 ≤ 6 * j + 3)

/-- Membership in the four finite route segments is computably decidable. -/
instance (n i j : ℕ) (p : ℕ × ℕ) : Decidable (onWire n i j p) :=
  inferInstanceAs (Decidable
    ((p.2 = 6 * i ∧ p.1 ≤ wireColumn n i j) ∨
      (p.1 = wireColumn n i j ∧ min (6 * i) (6 * j + 3) ≤ p.2 ∧
        p.2 ≤ max (6 * i) (6 * j + 3)) ∨
      (p.2 = 6 * j + 3 ∧ p.1 ≤ wireColumn n i j) ∨
      (p.1 = 0 ∧ 6 * j ≤ p.2 ∧ p.2 ≤ 6 * j + 3)))

/-- Move east, along the vertical column, west, then down the final hook. -/
def wireSuccessor (n i j : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  let col := wireColumn n i j
  if p.2 = 6 * i ∧ p.1 < col then (p.1 + 1, p.2)
  else if p.1 = col ∧ min (6 * i) (6 * j + 3) ≤ p.2 ∧
      p.2 ≤ max (6 * i) (6 * j + 3) ∧ p.2 ≠ 6 * j + 3 then
    (p.1, if 6 * i < 6 * j + 3 then p.2 + 1 else p.2 - 1)
  else if p.2 = 6 * j + 3 ∧ 0 < p.1 ∧ p.1 ≤ col then (p.1 - 1, p.2)
  else if p.1 = 0 ∧ 6 * j < p.2 ∧ p.2 ≤ 6 * j + 3 then (p.1, p.2 - 1)
  else p

/-- Reverse the local steps of the routed edge. -/
def wirePredecessor (n i j : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  let col := wireColumn n i j
  if p.2 = 6 * i ∧ 0 < p.1 ∧ p.1 ≤ col then (p.1 - 1, p.2)
  else if p.1 = col ∧ min (6 * i) (6 * j + 3) ≤ p.2 ∧
      p.2 ≤ max (6 * i) (6 * j + 3) ∧ p.2 ≠ 6 * i then
    (p.1, if 6 * i < 6 * j + 3 then p.2 - 1 else p.2 + 1)
  else if p.2 = 6 * j + 3 ∧ p.1 < col then (p.1 + 1, p.2)
  else if p.1 = 0 ∧ 6 * j ≤ p.2 ∧ p.2 < 6 * j + 3 then (p.1, p.2 + 1)
  else p

/-- Distinct vertex endpoints allocate a strictly positive routing column. -/
theorem wireColumn_pos {n i j : ℕ} (hi : i < n) (hne : i ≠ j) :
    0 < wireColumn n i j := by
  have hn : 0 < n := by omega
  by_cases hzero : i = 0
  · simp [wireColumn, hzero]
    omega
  · have hm : 0 < n * i := Nat.mul_pos hn (Nat.pos_of_ne_zero hzero)
    unfold wireColumn
    omega

/-- Every nontrivial successor step has the matching predecessor step. -/
theorem wire_successor_consistent {n i j : ℕ} (hi : i < n)
    (hne : i ≠ j) (p : ℕ × ℕ) (hs : wireSuccessor n i j p ≠ p) :
    wirePredecessor n i j (wireSuccessor n i j p) = p := by
  have hc := wireColumn_pos hi hne
  have hsep : 6 * i < 6 * j ∨ 6 * j + 3 < 6 * i := by omega
  by_cases hdir : 6 * i < 6 * j + 3
  all_goals rcases p with ⟨x, y⟩
  all_goals dsimp only [wireSuccessor] at hs ⊢
  all_goals split_ifs at hs ⊢ <;> simp_all only [wirePredecessor]
  all_goals split_ifs <;> simp_all [Prod.mk.injEq] <;> omega

/-- Every nontrivial predecessor step has the matching successor step. -/
theorem wire_predecessor_consistent {n i j : ℕ} (hi : i < n)
    (hne : i ≠ j) (p : ℕ × ℕ) (hp : wirePredecessor n i j p ≠ p) :
    wireSuccessor n i j (wirePredecessor n i j p) = p := by
  have hc := wireColumn_pos hi hne
  have hsep : 6 * i < 6 * j ∨ 6 * j + 3 < 6 * i := by omega
  by_cases hdir : 6 * i < 6 * j + 3
  all_goals rcases p with ⟨x, y⟩
  all_goals dsimp only [wirePredecessor] at hp ⊢
  all_goals split_ifs at hp ⊢ <;> simp_all only [wireSuccessor]
  all_goals split_ifs <;> first | omega | (simp_all [Prod.mk.injEq] <;> omega)

/-- Every point outside the four route segments is a successor self-loop. -/
theorem wireSuccessor_off_wire (n i j : ℕ) (p : ℕ × ℕ) (h : ¬onWire n i j p) :
    wireSuccessor n i j p = p := by
  rcases p with ⟨x, y⟩
  dsimp only [wireSuccessor]
  split_ifs <;> simp_all [onWire] <;> omega

/-- Every point outside the four route segments is a predecessor self-loop. -/
theorem wirePredecessor_off_wire (n i j : ℕ) (p : ℕ × ℕ) (h : ¬onWire n i j p) :
    wirePredecessor n i j p = p := by
  rcases p with ⟨x, y⟩
  dsimp only [wirePredecessor]
  split_ifs <;> simp_all [onWire] <;> omega

/-- A successor moves exactly on the route away from its final vertex. -/
theorem wireSuccessor_ne_iff {n i j : ℕ} (hi : i < n) (hne : i ≠ j) (p : ℕ × ℕ) :
    wireSuccessor n i j p ≠ p ↔ onWire n i j p ∧ p ≠ vertexPoint j := by
  have hc := wireColumn_pos hi hne
  have hsep : 6 * i < 6 * j ∨ 6 * j + 3 < 6 * i := by omega
  rcases p with ⟨x, y⟩
  dsimp only [wireSuccessor]
  split_ifs <;> simp only [onWire, vertexPoint]
  all_goals simp only [ne_eq, Prod.ext_iff, not_true_eq_false, false_iff]
  all_goals omega

/-- A predecessor moves exactly on the route away from its first vertex. -/
theorem wirePredecessor_ne_iff {n i j : ℕ} (hi : i < n) (hne : i ≠ j) (p : ℕ × ℕ) :
    wirePredecessor n i j p ≠ p ↔ onWire n i j p ∧ p ≠ vertexPoint i := by
  have hc := wireColumn_pos hi hne
  have hsep : 6 * i < 6 * j ∨ 6 * j + 3 < 6 * i := by omega
  rcases p with ⟨x, y⟩
  dsimp only [wirePredecessor]
  split_ifs <;> simp only [onWire, vertexPoint]
  all_goals simp only [ne_eq, Prod.ext_iff, not_true_eq_false, false_iff]
  all_goals omega

/-- The outgoing graph edges are exactly the route points other than its target. -/
theorem wire_hasSuccessor_iff {n i j : ℕ} (hi : i < n) (hne : i ≠ j)
    (p : ℕ × ℕ) :
    EndOfLine.HasSuccessor (wirePredecessor n i j) (wireSuccessor n i j) p ↔
      onWire n i j p ∧ p ≠ vertexPoint j := by
  constructor
  · intro h
    exact (wireSuccessor_ne_iff hi hne p).mp h.1
  · intro h
    have hs := (wireSuccessor_ne_iff hi hne p).mpr h
    exact ⟨hs, wire_successor_consistent hi hne p hs⟩

/-- The incoming graph edges are exactly the route points other than its source. -/
theorem wire_hasPredecessor_iff {n i j : ℕ} (hi : i < n) (hne : i ≠ j)
    (p : ℕ × ℕ) :
    EndOfLine.HasPredecessor (wirePredecessor n i j) (wireSuccessor n i j) p ↔
      onWire n i j p ∧ p ≠ vertexPoint i := by
  constructor
  · intro h
    exact (wirePredecessor_ne_iff hi hne p).mp h.1
  · intro h
    have hp := (wirePredecessor_ne_iff hi hne p).mpr h
    exact ⟨hp, wire_predecessor_consistent hi hne p hp⟩

/-- A single routed non-loop edge has precisely its source and target as endpoints. -/
theorem wire_endpoint_iff {n i j : ℕ} (hi : i < n) (hne : i ≠ j) (p : ℕ × ℕ) :
    EndOfLine.IsEndpoint (wirePredecessor n i j) (wireSuccessor n i j) p ↔
      p = vertexPoint i ∨ p = vertexPoint j := by
  have hsource : onWire n i j (vertexPoint i) := Or.inl ⟨rfl, Nat.zero_le _⟩
  have htarget : onWire n i j (vertexPoint j) :=
    Or.inr (Or.inr (Or.inr ⟨rfl, le_rfl, by
      dsimp only [vertexPoint]
      omega⟩))
  have hdistinct : vertexPoint i ≠ vertexPoint j := by
    simp only [vertexPoint, ne_eq, Prod.mk.injEq]
    omega
  unfold EndOfLine.IsEndpoint
  rw [wire_hasSuccessor_iff hi hne, wire_hasPredecessor_iff hi hne]
  by_cases hpi : p = vertexPoint i
  · subst p
    simp [hsource, hdistinct]
  · by_cases hpj : p = vertexPoint j
    · subst p
      simp [htarget, hdistinct.symm]
    · simp [hpi, hpj]

/-- Every nontrivial successor follows one unit axis-aligned grid edge. -/
theorem wireSuccessor_adjacent (n i j : ℕ) (p : ℕ × ℕ)
    (h : wireSuccessor n i j p ≠ p) :
    GridCrossing.axisUnitAdjacent p (wireSuccessor n i j p) := by
  rcases p with ⟨x, y⟩
  dsimp only [wireSuccessor] at h ⊢
  split_ifs at h ⊢ <;> simp_all [GridCrossing.axisUnitAdjacent] <;> omega

/-- Every nontrivial predecessor follows one unit axis-aligned grid edge. -/
theorem wirePredecessor_adjacent (n i j : ℕ) (p : ℕ × ℕ)
    (h : wirePredecessor n i j p ≠ p) :
    GridCrossing.axisUnitAdjacent p (wirePredecessor n i j p) := by
  rcases p with ⟨x, y⟩
  dsimp only [wirePredecessor] at h ⊢
  split_ifs at h ⊢ <;> simp_all [GridCrossing.axisUnitAdjacent] <;> omega

end GameTheory.Math.GridWire
