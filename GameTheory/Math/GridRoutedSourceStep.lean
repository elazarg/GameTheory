import GameTheory.Math.GridRoutedGraph

/-! The routed zero source starts with one eastward grid step. This exact
orientation supports attaching a boundary entrance to the interior grid path. -/

namespace GameTheory.Math.GridWire

open EndOfLine GridCrossing

/-- The zero source retains its predecessor loop and starts eastward. -/
theorem gridRouted_origin_step {n : ℕ} {P S : ℕ → ℕ}
    (hi : 0 < n) (hSi : S 0 < n) (hP : P 0 = 0) (hS : S 0 ≠ 0)
    (hlink : P (S 0) = 0) :
    gridRoutedPredecessor n P S (0, 0) = (0, 0) ∧
      gridRoutedSuccessor n P S (0, 0) = (1, 0) := by
  refine ⟨(gridRouted_source hi hSi hP hS hlink).1, ?_⟩
  have ha : activeEdge n P S 0 := ⟨hi, hSi, hS, hlink⟩
  have hc : 0 < wireColumn n 0 (S 0) := wireColumn_pos hi (Ne.symm hS)
  have hw : wireSuccessor n 0 (S 0) (vertexPoint 0) = (1, 0) := by
    simp only [wireSuccessor, vertexPoint]
    rw [ite_eq_left (show True ∧ 0 < wireColumn n 0 (S 0) from ⟨trivial, hc⟩)]
  have hs0 : (1, 0) ≠ vertexPoint 0 := by simp [vertexPoint]
  have hst : (1, 0) ≠ vertexPoint (S 0) := by simp [vertexPoint]
  have hcross : crossingOwners n P S (1, 0) = none := by
    cases he : crossingOwners n P S (1, 0) with
    | none => rfl
    | some owners =>
      rcases owners with ⟨i,k⟩
      obtain ⟨_, _, _, _, _, _, _, hh, hv⟩ := crossingOwners_sound he
      have hm : (1 : ℕ) % 3 = 0 := (crossing_coordinates hh hv).1
      contradiction
  change gridRoutedSuccessor n P S (routedCoordinate n P S (.inl 0)) = (1, 0)
  rw [gridRoutedSuccessor_encode (show liveWireNode n P S (.inl 0) from hi)]
  simp only [switchedRoutedSuccessor, Function.comp_apply, routedSwitch,
    routedSuccessor, ite_eq_left ha, hw, embedWire, ite_eq_right hs0,
    ite_eq_right hst, routedCoordinate, wireImagePoint, hcross]

end GameTheory.Math.GridWire
