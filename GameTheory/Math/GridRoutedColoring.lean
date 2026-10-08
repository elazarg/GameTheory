import GameTheory.Math.GridWireColoring
import GameTheory.Math.GridWireColoringPorts
import GameTheory.Math.GridRoutedGraph

/-! The endpoint-preserving routed graph admits a local three-color thickening.
Every trichromatic triangle identifies an original endpoint by two row divisions.
The construction here colors the interior grid; a canonical outer boundary must
supply the known-source entrance separately. -/

namespace GameTheory.Math.GridWire

open Sperner EndOfLine

/-- Thicken each routed grid vertex into a fixed size-six color tile. -/
def gridRoutedColor (n : ℕ) (P S : ℕ → ℕ) : ℕ → ℕ → Fin 3 :=
  wireGridColor
    (fun i j => gridIncomingPort (gridRoutedPredecessor n P S)
      (gridRoutedSuccessor n P S) (i, j))
    (fun i j => gridOutgoingPort (gridRoutedPredecessor n P S)
      (gridRoutedSuccessor n P S) (i, j))

/-- All trichromatic triangles are exactly the fixed local witnesses of routed
endpoints. This includes endpoints in components unrelated to the known source. -/
theorem gridRoutedColor_trichromatic_iff (n : ℕ) (P S : ℕ → ℕ) (t : GridTriangle) :
    Trichromatic (gridRoutedColor n P S (corner t 0).1 (corner t 0).2)
      (gridRoutedColor n P S (corner t 1).1 (corner t 1).2)
      (gridRoutedColor n P S (corner t 2).1 (corner t 2).2) ↔
      IsEndpoint (gridRoutedPredecessor n P S) (gridRoutedSuccessor n P S)
        (t.x / 6, t.y / 6) ∧ t.x % 6 = 2 ∧ t.y % 6 = 2 ∧ t.upper = false := by
  have h := wireGridColor_corner_trichromatic_iff
    (fun i j => gridIncomingPort (gridRoutedPredecessor n P S)
      (gridRoutedSuccessor n P S) (i, j))
    (fun i j => gridOutgoingPort (gridRoutedPredecessor n P S)
      (gridRoutedSuccessor n P S) (i, j))
    (fun i j => gridPorts_valid _ _ (gridRoutedPredecessor_adjacent n P S) (i, j))
    (fun i j k _ => gridPorts_east_seam _ _ (gridRouted_predecessor_consistent n P S)
      (gridRouted_successor_consistent n P S) i j k)
    (fun i j k _ => gridPorts_north_seam _ _ (gridRouted_predecessor_consistent n P S)
      (gridRouted_successor_consistent n P S) i j k) t
  rw [gridPorts_endpoint_iff _ _ (gridRouted_predecessor_consistent n P S)
    (gridRouted_successor_consistent n P S) (gridRoutedPredecessor_adjacent n P S)
    (gridRoutedSuccessor_adjacent n P S)] at h
  exact h

/-- Recover a bounded original endpoint by dividing the witness row by thirty-six. -/
theorem gridRoutedColor_endpoint_label {n : ℕ} {P S : ℕ → ℕ} {t : GridTriangle}
    (hP : ∀ i, i < n → P i < n) (hS : ∀ i, i < n → S i < n)
    (ht : Trichromatic (gridRoutedColor n P S (corner t 0).1 (corner t 0).2)
      (gridRoutedColor n P S (corner t 1).1 (corner t 1).2)
      (gridRoutedColor n P S (corner t 2).1 (corner t 2).2)) :
    t.x = 2 ∧ t.y / 36 < n ∧ IsEndpoint P S (t.y / 36) := by
  obtain ⟨he, hx, _, _⟩ := (gridRoutedColor_trichromatic_iff n P S t).mp ht
  have h := gridRouted_endpoint_label hP hS he
  simp only [Nat.div_div_eq_div_mul] at h
  exact ⟨by omega, h.2⟩

/-- Every bounded original endpoint has its own explicit trichromatic witness. -/
theorem gridRoutedColor_vertex_triangle_iff {n i : ℕ} {P S : ℕ → ℕ}
    (hi : i < n) (hP : ∀ j, j < n → P j < n) (hS : ∀ j, j < n → S j < n) :
    let t : GridTriangle := ⟨2, 36 * i + 2, false⟩
    Trichromatic (gridRoutedColor n P S (corner t 0).1 (corner t 0).2)
      (gridRoutedColor n P S (corner t 1).1 (corner t 1).2)
      (gridRoutedColor n P S (corner t 2).1 (corner t 2).2) ↔ IsEndpoint P S i := by
  dsimp only
  rw [gridRoutedColor_trichromatic_iff]
  have hdiv : (36 * i + 2) / 6 = 6 * i := by omega
  have hmod : (36 * i + 2) % 6 = 2 := by omega
  simp only [hdiv, hmod, Nat.reduceDiv, Nat.reduceMod, and_true]
  exact gridRouted_vertex_endpoint_iff hi hP hS

end GameTheory.Math.GridWire
