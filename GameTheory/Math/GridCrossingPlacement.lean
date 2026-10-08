import GameTheory.Math.GridWireCrossings

/-! Translation places a crossing switch in its existing grid neighborhood.
The coordinate decoder identifies exactly the nine nodes of the switch. -/

namespace GameTheory.Math.GridCrossing

/-- Place the three-by-three switch around the given center. -/
def placedCoordinate (center : ℕ × ℕ) (node : CrossingNode) : ℕ × ℕ :=
  (center.1 - 1 + (crossingCoordinate node).1,
    center.2 - 1 + (crossingCoordinate node).2)

/-- Translation preserves the distinction between all switch nodes. -/
theorem placedCoordinate_injective (center : ℕ × ℕ) :
    Function.Injective (placedCoordinate center) := by
  intro a b h
  apply crossingCoordinate_injective
  have hxy := Prod.mk.inj h
  apply Prod.ext <;> omega

private theorem coordinate_bounds (node : CrossingNode) :
    (crossingCoordinate node).1 ≤ 2 ∧ (crossingCoordinate node).2 ≤ 2 := by
  cases node with
  | port p => fin_cases p <;> decide
  | bend p => fin_cases p <;> decide
  | center => decide

/-- Every placed node belongs to the canonical radius-one crossing neighborhood. -/
theorem placedCoordinate_mem_neighborhood {center : ℕ × ℕ}
    (hx : 1 ≤ center.1) (hy : 1 ≤ center.2) (node : CrossingNode) :
    GridWire.crossingNeighborhood center (placedCoordinate center node) := by
  have hb := coordinate_bounds node
  dsimp only [GridWire.crossingNeighborhood, placedCoordinate]
  omega

/-- The isolated switch center is placed at the requested positive center. -/
theorem placedCoordinate_center {center : ℕ × ℕ}
    (hx : 1 ≤ center.1) (hy : 1 ≤ center.2) :
    placedCoordinate center .center = center := by
  apply Prod.ext <;> dsimp only [placedCoordinate, crossingCoordinate] <;> omega

private theorem translated_adjacent (center a b : ℕ × ℕ)
    (h : axisUnitAdjacent a b) :
    axisUnitAdjacent (center.1 - 1 + a.1, center.2 - 1 + a.2)
      (center.1 - 1 + b.1, center.2 - 1 + b.2) := by
  dsimp only [axisUnitAdjacent] at h ⊢
  omega

/-- Every placed nontrivial successor still follows a unit grid edge. -/
theorem placedSuccessor_adjacent (center : ℕ × ℕ) (rightward upward : Bool)
    (node : CrossingNode) (h : crossingSuccessor rightward upward node ≠ node) :
    axisUnitAdjacent (placedCoordinate center node)
      (placedCoordinate center (crossingSuccessor rightward upward node)) :=
  translated_adjacent center _ _ (crossingSuccessor_adjacent rightward upward node h)

/-- Every placed nontrivial predecessor still follows a unit grid edge. -/
theorem placedPredecessor_adjacent (center : ℕ × ℕ) (rightward upward : Bool)
    (node : CrossingNode) (h : crossingPredecessor rightward upward node ≠ node) :
    axisUnitAdjacent (placedCoordinate center node)
      (placedCoordinate center (crossingPredecessor rightward upward node)) :=
  translated_adjacent center _ _ (crossingPredecessor_adjacent rightward upward node h)

/-- A switch whose center is at least three columns out contains no graph vertex. -/
theorem placedCoordinate_ne_vertexPoint {center : ℕ × ℕ} (hx : 3 ≤ center.1)
    (node : CrossingNode) (i : ℕ) : placedCoordinate center node ≠ GridWire.vertexPoint i := by
  simp only [placedCoordinate, GridWire.vertexPoint, ne_eq, Prod.mk.injEq]
  omega

/-- Decode the nine translated node coordinates, rejecting all other grid points. -/
def decodePlacedCoordinate (center point : ℕ × ℕ) : Option CrossingNode :=
  if point = placedCoordinate center (.port 0) then some (.port 0)
  else if point = placedCoordinate center (.port 1) then some (.port 1)
  else if point = placedCoordinate center (.port 2) then some (.port 2)
  else if point = placedCoordinate center (.port 3) then some (.port 3)
  else if point = placedCoordinate center (.bend 0) then some (.bend 0)
  else if point = placedCoordinate center (.bend 1) then some (.bend 1)
  else if point = placedCoordinate center (.bend 2) then some (.bend 2)
  else if point = placedCoordinate center (.bend 3) then some (.bend 3)
  else if point = placedCoordinate center .center then some .center
  else none

/-- Every encoded switch node decodes exactly, even at a truncated boundary center. -/
theorem decodePlacedCoordinate_placedCoordinate (center : ℕ × ℕ) (node : CrossingNode) :
    decodePlacedCoordinate center (placedCoordinate center node) = some node := by
  cases node with
  | port p => fin_cases p <;>
      simp [decodePlacedCoordinate, (placedCoordinate_injective center).eq_iff]
  | bend p => fin_cases p <;>
      simp [decodePlacedCoordinate, (placedCoordinate_injective center).eq_iff]
  | center => simp [decodePlacedCoordinate, (placedCoordinate_injective center).eq_iff]

/-- A successful decoding certifies the exact translated node coordinate. -/
theorem decodePlacedCoordinate_eq_some_iff (center point : ℕ × ℕ) (node : CrossingNode) :
    decodePlacedCoordinate center point = some node ↔ point = placedCoordinate center node := by
  constructor
  · intro h
    unfold decodePlacedCoordinate at h
    split_ifs at h <;> simp_all
  · intro h
    rw [h]
    exact decodePlacedCoordinate_placedCoordinate center node

/-- Decoder success is exactly membership in the image of the placed switch. -/
theorem decodePlacedCoordinate_isSome_iff (center point : ℕ × ℕ) :
    (decodePlacedCoordinate center point).isSome = true ↔
      ∃ node, point = placedCoordinate center node := by
  cases h : decodePlacedCoordinate center point with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists]
    intro node hnode
    have heq := (decodePlacedCoordinate_eq_some_iff center point node).mpr hnode
    rw [h] at heq
    contradiction
  | some node =>
    simp only [Option.isSome_some, true_iff]
    exact ⟨node, (decodePlacedCoordinate_eq_some_iff center point node).mp h⟩

/-- At a positive center, decoder success covers exactly the entire switch box. -/
theorem decodePlacedCoordinate_isSome_iff_neighborhood {center point : ℕ × ℕ}
    (hx : 1 ≤ center.1) (hy : 1 ≤ center.2) :
    (decodePlacedCoordinate center point).isSome = true ↔
      GridWire.crossingNeighborhood center point := by
  constructor
  · intro h
    obtain ⟨node, rfl⟩ := (decodePlacedCoordinate_isSome_iff center point).mp h
    exact placedCoordinate_mem_neighborhood hx hy node
  · intro hbox
    cases h : decodePlacedCoordinate center point with
    | some node => rfl
    | none =>
      unfold decodePlacedCoordinate at h
      split_ifs at h
      all_goals
        simp only [placedCoordinate, crossingCoordinate, Prod.ext_iff,
          GridWire.crossingNeighborhood] at *
        simp_all
        omega

/-- The two used bends are distinct for every pair of strand orientations. -/
theorem horizontalBend_ne_verticalBend (rightward upward : Bool) :
    horizontalBend rightward upward ≠ verticalBend rightward upward := by
  cases rightward <;> cases upward <;> decide

/-- Corners of a switch on the spacing-three lattice lie off both coordinate lanes. -/
theorem placed_bend_mod_three {center : ℕ × ℕ}
    (hx : 3 ≤ center.1) (hy : 3 ≤ center.2)
    (hxm : center.1 % 3 = 0) (hym : center.2 % 3 = 0) (k : Fin 4) :
    (placedCoordinate center (.bend k)).1 % 3 ≠ 0 ∧
      (placedCoordinate center (.bend k)).2 % 3 ≠ 0 := by
  fin_cases k <;> simp [placedCoordinate, crossingCoordinate] <;> omega

private theorem onWire_mod_three {n i j : ℕ} {point : ℕ × ℕ}
    (h : GridWire.onWire n i j point) : point.1 % 3 = 0 ∨ point.2 % 3 = 0 := by
  rcases h with h | h | h | h
  · right
    simp [h.1, Nat.mul_mod]
  · left
    simp [h.1, GridWire.wireColumn]
  · right
    simp [h.1, Nat.mul_mod]
  · left
    simp [h.1]

/-- A placed bend at a lattice crossing is outside every original routed wire. -/
theorem placed_bend_not_onWire {center : ℕ × ℕ}
    (hx : 3 ≤ center.1) (hy : 3 ≤ center.2)
    (hxm : center.1 % 3 = 0) (hym : center.2 % 3 = 0)
    (k : Fin 4) (n i j : ℕ) : ¬GridWire.onWire n i j (placedCoordinate center (.bend k)) := by
  intro h
  have hb := placed_bend_mod_three hx hy hxm hym k
  rcases onWire_mod_three h with h | h
  · exact hb.1 h
  · exact hb.2 h

end GameTheory.Math.GridCrossing
