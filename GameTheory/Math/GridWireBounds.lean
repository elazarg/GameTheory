import GameTheory.Math.GridRoutedGraph

/-! Every live routed point fits inside a quadratic-width, linear-height grid.
Crossing bends retain a one-step margin within this rectangle. Global pointers
therefore preserve any coordinate capacity that contains the routed rectangle. -/

namespace GameTheory.Math.GridWire

open GameTheory.Math.GridCrossing

/-- The four wire segments stay within the routing rectangle for bounded labels. -/
theorem onWire_bounds {n i j : ℕ} {p : ℕ × ℕ} (hi : i < n) (hj : j < n)
    (hp : onWire n i j p) : p.1 < 3 * n * n ∧ p.2 < 6 * n := by
  have hc := wireColumn_lt hi hj
  rw [← Nat.mul_assoc] at hc
  have hy : max (6 * i) (6 * j + 3) < 6 * n := by omega
  rcases hp with hp | hp | hp | hp <;> omega

/-- Displacing a crossing center to its assigned bend stays inside the rectangle. -/
theorem wireImagePoint_bounds {n i : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (ha : activeEdge n P S i) (hp : onWire n i (S i) p) :
    (wireImagePoint n P S i p).1 < 3 * n * n ∧
      (wireImagePoint n P S i p).2 < 6 * n := by
  have hb := onWire_bounds ha.1 ha.2.1 hp
  cases hc : crossingOwners n P S p with
  | none => simpa only [wireImagePoint, hc] using hb
  | some owners =>
    obtain ⟨_, _, _, _, _, _, _, hh, hv⟩ := crossingOwners_sound hc
    have hm := crossing_coordinates hh hv
    have hxcap : (3 * n * n) % 3 = 0 := by simp [Nat.mul_mod]
    have hycap : (6 * n) % 3 = 0 := by omega
    have hn := wireImagePoint_neighborhood (a := i) hc
    unfold crossingNeighborhood at hn
    omega

/-- Every live vertex or interior image fits inside the routing rectangle. -/
theorem routedCoordinate_bounds {n : ℕ} {P S : ℕ → ℕ} {node : WireNode}
    (hl : liveWireNode n P S node) :
    (routedCoordinate n P S node).1 < 3 * n * n ∧
      (routedCoordinate n P S node).2 < 6 * n := by
  cases node with
  | inl i => exact onWire_bounds hl hl (Or.inl ⟨rfl, Nat.zero_le _⟩)
  | inr ip => exact wireImagePoint_bounds hl.1 hl.2.1

/-- Both global pointers preserve any input capacity containing the routed rectangle. -/
theorem gridRouted_pointer_bounds {n X Y : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hX : 3 * n * n ≤ X) (hY : 6 * n ≤ Y) (hp : p.1 < X ∧ p.2 < Y) :
    ((gridRoutedPredecessor n P S p).1 < X ∧ (gridRoutedPredecessor n P S p).2 < Y) ∧
      ((gridRoutedSuccessor n P S p).1 < X ∧ (gridRoutedSuccessor n P S p).2 < Y) := by
  cases hd : decodeWireNode n P S p with
  | none =>
    have h := gridRouted_background hd
    rw [h.1, h.2]
    exact ⟨hp, hp⟩
  | some node =>
    have hl := (decodeWireNode_eq_some_iff.mp hd).1
    have hpred := routedCoordinate_bounds (switchedRoutedPredecessor_preserves_live hl)
    have hsucc := routedCoordinate_bounds (switchedRoutedSuccessor_preserves_live hl)
    simp only [gridRoutedPredecessor, gridRoutedSuccessor, hd]
    exact ⟨⟨hpred.1.trans_le hX, hpred.2.trans_le hY⟩,
      ⟨hsucc.1.trans_le hX, hsucc.2.trans_le hY⟩⟩

end GameTheory.Math.GridWire
