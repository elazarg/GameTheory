import GameTheory.Math.GridWireImage
import GameTheory.Math.GridWireSwitch

/-! The switch ports coincide with the adjacent points of the original strands.
These coordinate agreements connect routed wire execution to placed switch edges. -/

namespace GameTheory.Math.GridWire

open GridCrossing EndOfLine

private theorem horizontal_successor {n i j : ℕ} {c : ℕ × ℕ}
    (hh : horizontalInterior n i j c) :
    wireSuccessor n i j c = if c.2 = 6 * i then (c.1 + 1, c.2) else (c.1 - 1, c.2) := by
  dsimp only [wireSuccessor]
  split_ifs
  all_goals simp_all [horizontalInterior]
  all_goals omega

private theorem horizontal_predecessor {n i j : ℕ} {c : ℕ × ℕ}
    (hh : horizontalInterior n i j c) :
    wirePredecessor n i j c = if c.2 = 6 * i then (c.1 - 1, c.2) else (c.1 + 1, c.2) := by
  dsimp only [wirePredecessor]
  split_ifs <;> simp_all [horizontalInterior] <;> omega

private theorem vertical_successor {n i j : ℕ} {c : ℕ × ℕ}
    (hv : verticalInterior n i j c) :
    wireSuccessor n i j c =
      (c.1, if 6 * i < 6 * j + 3 then c.2 + 1 else c.2 - 1) := by
  dsimp only [wireSuccessor]
  split_ifs <;> simp_all [verticalInterior] <;> omega

private theorem vertical_predecessor {n i j : ℕ} {c : ℕ × ℕ}
    (hv : verticalInterior n i j c) :
    wirePredecessor n i j c =
      (c.1, if 6 * i < 6 * j + 3 then c.2 - 1 else c.2 + 1) := by
  dsimp only [wirePredecessor]
  split_ifs <;> simp_all [verticalInterior] <;> omega

/-- The horizontal input port is the strand's original predecessor of the crossing. -/
theorem placed_horizontalInput_eq_predecessor {n i j k l : ℕ} {c : ℕ × ℕ}
    (hh : horizontalInterior n i j c) (hv : verticalInterior n k l c) :
    placedCoordinate c (.port (horizontalInputPort (decide (c.2 = 6 * i)))) =
      wirePredecessor n i j c := by
  obtain ⟨hx, hy⟩ := crossing_clearance hh hv
  rw [horizontal_predecessor hh]
  by_cases h : c.2 = 6 * i <;>
    simp [h, placedCoordinate, horizontalInputPort, crossingCoordinate, Prod.ext_iff] <;> omega

/-- The horizontal output port is the strand's original successor of the crossing. -/
theorem placed_horizontalOutput_eq_successor {n i j k l : ℕ} {c : ℕ × ℕ}
    (hh : horizontalInterior n i j c) (hv : verticalInterior n k l c) :
    placedCoordinate c (.port (horizontalOutputPort (decide (c.2 = 6 * i)))) =
      wireSuccessor n i j c := by
  obtain ⟨hx, hy⟩ := crossing_clearance hh hv
  rw [horizontal_successor hh]
  by_cases h : c.2 = 6 * i <;>
    simp [h, placedCoordinate, horizontalOutputPort, crossingCoordinate, Prod.ext_iff] <;> omega

/-- The vertical input port is the strand's original predecessor of the crossing. -/
theorem placed_verticalInput_eq_predecessor {n i j k l : ℕ} {c : ℕ × ℕ}
    (hh : horizontalInterior n i j c) (hv : verticalInterior n k l c) :
    placedCoordinate c (.port (verticalInputPort (decide (6 * k < 6 * l + 3)))) =
      wirePredecessor n k l c := by
  obtain ⟨hx, hy⟩ := crossing_clearance hh hv
  rw [vertical_predecessor hv]
  by_cases h : 6 * k < 6 * l + 3 <;>
    simp [h, placedCoordinate, verticalInputPort, crossingCoordinate, Prod.ext_iff] <;> omega

/-- The vertical output port is the strand's original successor of the crossing. -/
theorem placed_verticalOutput_eq_successor {n i j k l : ℕ} {c : ℕ × ℕ}
    (hh : horizontalInterior n i j c) (hv : verticalInterior n k l c) :
    placedCoordinate c (.port (verticalOutputPort (decide (6 * k < 6 * l + 3)))) =
      wireSuccessor n k l c := by
  obtain ⟨hx, hy⟩ := crossing_clearance hh hv
  rw [vertical_successor hv]
  by_cases h : 6 * k < 6 * l + 3 <;>
    simp [h, placedCoordinate, verticalOutputPort, crossingCoordinate, Prod.ext_iff] <;> omega

/-- Original vertices are never crossing centers. -/
theorem crossingOwners_vertexPoint_none (n i : ℕ) (P S : ℕ → ℕ) :
    crossingOwners n P S (vertexPoint i) = none := by
  cases h : crossingOwners n P S (vertexPoint i) with
  | none => rfl
  | some owners =>
    obtain ⟨_, _, _, _, _, _, _, hh, _⟩ := crossingOwners_sound h
    have hx := hh.1
    simp only [vertexPoint] at hx
    omega

/-- A unit neighbor of a crossing center cannot be another crossing center. -/
theorem crossingOwners_adjacent_none {n i k : ℕ} {P S : ℕ → ℕ} {c p : ℕ × ℕ}
    (hc : crossingOwners n P S c = some (i, k)) (hp : axisUnitAdjacent c p) :
    crossingOwners n P S p = none := by
  obtain ⟨_, _, _, _, _, _, _, hh, hv⟩ := crossingOwners_sound hc
  have hm := crossing_coordinates hh hv
  cases h : crossingOwners n P S p with
  | none => rfl
  | some owners =>
    obtain ⟨_, _, _, _, _, _, _, hh', hv'⟩ := crossingOwners_sound h
    have hm' := crossing_coordinates hh' hv'
    dsimp only [axisUnitAdjacent] at hp
    omega

/-- Rejoining a wire endpoint commutes with its geometric realization. -/
theorem routedCoordinate_embedWire (n i : ℕ) (P S : ℕ → ℕ) (p : ℕ × ℕ) :
    routedCoordinate n P S (embedWire S i p) = wireImagePoint n P S i p := by
  unfold embedWire
  split_ifs with hs ht
  · rw [hs]
    simp [routedCoordinate, wireImagePoint, crossingOwners_vertexPoint_none]
  · rw [ht]
    simp [routedCoordinate, wireImagePoint, crossingOwners_vertexPoint_none]
  · rfl

private theorem horizontal_step_ne {n i j : ℕ} {c : ℕ × ℕ}
    (hh : horizontalInterior n i j c) : wireSuccessor n i j c ≠ c := by
  rw [horizontal_successor hh]
  have hx := hh.1
  split_ifs <;> simp only [ne_eq, Prod.ext_iff] <;> omega

private theorem vertical_step_ne {n i j : ℕ} {c : ℕ × ℕ}
    (hv : verticalInterior n i j c) : wireSuccessor n i j c ≠ c := by
  rw [vertical_successor hv]
  have hb := hv.2
  split_ifs <;> simp only [ne_eq, Prod.ext_iff] <;> omega

private theorem horizontal_input_adjacent (c : ℕ × ℕ) (r u : Bool) :
    axisUnitAdjacent (placedCoordinate c (.port (horizontalInputPort r)))
      (placedCoordinate c (.bend (horizontalBend r u))) := by
  have hs : crossingSuccessor r u (.port (horizontalInputPort r)) ≠
      .port (horizontalInputPort r) := by rw [(horizontal_route r u).1]; intro h; cases h
  simpa only [(horizontal_route r u).1] using placedSuccessor_adjacent c r u _ hs

private theorem vertical_input_adjacent (c : ℕ × ℕ) (r u : Bool) :
    axisUnitAdjacent (placedCoordinate c (.port (verticalInputPort u)))
      (placedCoordinate c (.bend (verticalBend r u))) := by
  have hs : crossingSuccessor r u (.port (verticalInputPort u)) ≠
      .port (verticalInputPort u) := by rw [(vertical_route r u).1]; intro h; cases h
  simpa only [(vertical_route r u).1] using placedSuccessor_adjacent c r u _ hs

private theorem horizontal_output_adjacent (c : ℕ × ℕ) (r u : Bool) :
    axisUnitAdjacent (placedCoordinate c (.bend (horizontalBend r u)))
      (placedCoordinate c (.port (verticalOutputPort u))) := by
  have hs : crossingSuccessor r u (.bend (horizontalBend r u)) ≠
      .bend (horizontalBend r u) := by rw [(horizontal_route r u).2.1]; intro h; cases h
  simpa only [(horizontal_route r u).2.1] using placedSuccessor_adjacent c r u _ hs

private theorem vertical_output_adjacent (c : ℕ × ℕ) (r u : Bool) :
    axisUnitAdjacent (placedCoordinate c (.bend (verticalBend r u)))
      (placedCoordinate c (.port (horizontalOutputPort r))) := by
  have hs : crossingSuccessor r u (.bend (verticalBend r u)) ≠
      .bend (verticalBend r u) := by rw [(vertical_route r u).2.1]; intro h; cases h
  simpa only [(vertical_route r u).2.1] using placedSuccessor_adjacent c r u _ hs

/-- The horizontal crossing occurrence now takes a unit step to the vertical continuation. -/
theorem wireImagePoint_horizontal_crossing_step {n i k : ℕ} {P S : ℕ → ℕ}
    {c : ℕ × ℕ} (hc : crossingOwners n P S c = some (i, k)) :
    axisUnitAdjacent (wireImagePoint n P S i c)
      (wireImagePoint n P S k (wireSuccessor n k (S k) c)) := by
  obtain ⟨_, _, _, _, _, _, _, hh, hv⟩ := crossingOwners_sound hc
  have hq := crossingOwners_adjacent_none hc
    (wireSuccessor_adjacent n k (S k) c (vertical_step_ne hv))
  simp only [wireImagePoint, hc, hq, ↓reduceIte]
  rw [← placed_verticalOutput_eq_successor hh hv]
  exact horizontal_output_adjacent c _ _

/-- The vertical crossing occurrence now takes a unit step to the horizontal continuation. -/
theorem wireImagePoint_vertical_crossing_step {n i k : ℕ} {P S : ℕ → ℕ}
    {c : ℕ × ℕ} (hc : crossingOwners n P S c = some (i, k)) :
    axisUnitAdjacent (wireImagePoint n P S k c)
      (wireImagePoint n P S i (wireSuccessor n i (S i) c)) := by
  obtain ⟨_, _, _, _, hik, _, _, hh, hv⟩ := crossingOwners_sound hc
  have hq := crossingOwners_adjacent_none hc
    (wireSuccessor_adjacent n i (S i) c (horizontal_step_ne hh))
  simp only [wireImagePoint, hc, hq, ite_eq_right hik.symm, ↓reduceIte]
  rw [← placed_horizontalOutput_eq_successor hh hv]
  exact vertical_output_adjacent c _ _

/-- The horizontal input strand takes a unit step into its assigned bend. -/
theorem wireImagePoint_horizontal_crossing_arrival {n i k : ℕ} {P S : ℕ → ℕ}
    {c : ℕ × ℕ} (hc : crossingOwners n P S c = some (i, k)) :
    axisUnitAdjacent (wireImagePoint n P S i (wirePredecessor n i (S i) c))
      (wireImagePoint n P S i c) := by
  obtain ⟨hi, _, _, _, _, hai, _, hh, hv⟩ := crossingOwners_sound hc
  have hl := (crossingOwners_nodes_live hc).1
  have hn := (wirePredecessor_ne_iff hi hai.1.symm c).mpr ⟨hl.2.1, hl.2.2.1⟩
  have hq := crossingOwners_adjacent_none hc (wirePredecessor_adjacent n i (S i) c hn)
  simp only [wireImagePoint, hc, hq, ↓reduceIte]
  rw [← placed_horizontalInput_eq_predecessor hh hv]
  exact horizontal_input_adjacent c _ _

/-- The vertical input strand takes a unit step into its assigned bend. -/
theorem wireImagePoint_vertical_crossing_arrival {n i k : ℕ} {P S : ℕ → ℕ}
    {c : ℕ × ℕ} (hc : crossingOwners n P S c = some (i, k)) :
    axisUnitAdjacent (wireImagePoint n P S k (wirePredecessor n k (S k) c))
      (wireImagePoint n P S k c) := by
  obtain ⟨_, hk, _, _, hik, _, hak, hh, hv⟩ := crossingOwners_sound hc
  have hl := (crossingOwners_nodes_live hc).2
  have hn := (wirePredecessor_ne_iff hk hak.1.symm c).mpr ⟨hl.2.1, hl.2.2.1⟩
  have hq := crossingOwners_adjacent_none hc (wirePredecessor_adjacent n k (S k) c hn)
  simp only [wireImagePoint, hc, hq, ite_eq_right hik.symm, ↓reduceIte]
  rw [← placed_verticalInput_eq_predecessor hh hv]
  exact vertical_input_adjacent c _ _

private theorem ordinary_image_step {n a : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (ha : activeEdge n P S a) (hp : onWire n a (S a) p)
    (ht : p ≠ vertexPoint (S a)) (hc : crossingOwners n P S p = none) :
    axisUnitAdjacent (wireImagePoint n P S a p)
      (wireImagePoint n P S a (wireSuccessor n a (S a) p)) := by
  have hn := (wireSuccessor_ne_iff ha.1 ha.2.2.1.symm p).mpr ⟨hp, ht⟩
  have hb := wire_successor_consistent ha.1 ha.2.2.1.symm p hn
  cases hq : crossingOwners n P S (wireSuccessor n a (S a) p) with
  | none =>
    simp only [wireImagePoint, hc, hq]
    exact wireSuccessor_adjacent n a (S a) p hn
  | some owners =>
    rcases owners with ⟨i, k⟩
    have hqwire := (wirePredecessor_ne_iff ha.1 ha.2.2.1.symm
      (wireSuccessor n a (S a) p)).mp (by rw [hb]; exact hn.symm)
    obtain h | h := crossingOwners_onWire hq ha.2.1 ha.2.2 hqwire.1
    · subst a
      simpa only [hb] using wireImagePoint_horizontal_crossing_arrival hq
    · subst a
      simpa only [hb] using wireImagePoint_vertical_crossing_arrival hq

/-- Every nontrivial live switched successor is realized by a unit grid edge. -/
theorem switchedRoutedSuccessor_adjacent {n : ℕ} {P S : ℕ → ℕ} {node : WireNode}
    (hl : liveWireNode n P S node) (hs : switchedRoutedSuccessor n P S node ≠ node) :
    axisUnitAdjacent (routedCoordinate n P S node)
      (routedCoordinate n P S (switchedRoutedSuccessor n P S node)) := by
  cases node with
  | inl i =>
    have ha : activeEdge n P S i := by
      by_contra h
      exact hs (by simp [switchedRoutedSuccessor, routedSwitch, routedSuccessor, h])
    have hp : onWire n i (S i) (vertexPoint i) := Or.inl ⟨rfl, Nat.zero_le _⟩
    have ht : vertexPoint i ≠ vertexPoint (S i) :=
      fun h => ha.2.2.1.symm (vertexPoint_injective h)
    have h := ordinary_image_step ha hp ht (crossingOwners_vertexPoint_none n i P S)
    change axisUnitAdjacent (vertexPoint i)
      (routedCoordinate n P S (routedSuccessor n P S (.inl i)))
    rw [routedSuccessor, ite_eq_left ha, routedCoordinate_embedWire]
    simpa only [wireImagePoint, crossingOwners_vertexPoint_none] using h
  | inr ap =>
    rcases ap with ⟨a, p⟩
    change axisUnitAdjacent (wireImagePoint n P S a p)
      (routedCoordinate n P S (routedSuccessor n P S (routedSwitch n P S (.inr (a, p)))))
    cases hc : crossingOwners n P S p with
    | none =>
      simp only [routedSwitch, hc]
      rw [routedSuccessor, ite_eq_left hl, routedCoordinate_embedWire]
      exact ordinary_image_step hl.1 hl.2.1 hl.2.2.2 hc
    | some owners =>
      rcases owners with ⟨i, k⟩
      have hne := (crossingOwners_sound hc).2.2.2.2.1
      have hother := crossingOwners_nodes_live hc
      obtain h | h := crossingOwners_onWire hc hl.1.2.1 hl.1.2.2 hl.2.1
      · subst a
        simp only [routedSwitch, hc, ↓reduceIte]
        rw [routedSuccessor, ite_eq_left hother.2, routedCoordinate_embedWire]
        exact wireImagePoint_horizontal_crossing_step hc
      · subst a
        simp only [routedSwitch, hc, ite_eq_right hne.symm, ↓reduceIte]
        rw [routedSuccessor, ite_eq_left hother.1, routedCoordinate_embedWire]
        exact wireImagePoint_vertical_crossing_step hc

/-- Every nontrivial live switched predecessor is realized by a unit grid edge. -/
theorem switchedRoutedPredecessor_adjacent {n : ℕ} {P S : ℕ → ℕ} {node : WireNode}
    (hl : liveWireNode n P S node) (hp : switchedRoutedPredecessor n P S node ≠ node) :
    axisUnitAdjacent (routedCoordinate n P S node)
      (routedCoordinate n P S (switchedRoutedPredecessor n P S node)) := by
  have hb := switchedRouted_predecessor_consistent n P S node hp
  have hs : switchedRoutedSuccessor n P S (switchedRoutedPredecessor n P S node) ≠
      switchedRoutedPredecessor n P S node := by rw [hb]; exact hp.symm
  have ha := switchedRoutedSuccessor_adjacent (switchedRoutedPredecessor_preserves_live hl) hs
  rw [hb] at ha
  dsimp only [axisUnitAdjacent] at ha ⊢
  omega

end GameTheory.Math.GridWire
