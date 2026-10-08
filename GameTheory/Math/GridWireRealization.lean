import GameTheory.Math.GridWireGraph
import GameTheory.Math.GridWireImage

/-! Coordinates realize the source-indexed routed graph. Its two crossing
occurrences use different switch bends, and no live interior occupies an
original vertex. Injectivity concerns live labels; rejected labels stay outside
this realization contract. -/

namespace GameTheory.Math.GridWire

open GameTheory.Math.GridCrossing

/-- Locate an original vertex or a routed interior occurrence in the grid. -/
def routedCoordinate (n : ℕ) (P S : ℕ → ℕ) : WireNode → ℕ × ℕ
  | .inl i => vertexPoint i
  | .inr (i, p) => wireImagePoint n P S i p

/-- A live interior realization cannot occupy any original graph vertex. -/
theorem routedCoordinate_interior_ne_vertex {n i : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hl : liveWireNode n P S (.inr (i, p))) (j : ℕ) :
    routedCoordinate n P S (.inr (i, p)) ≠ vertexPoint j := by
  change wireImagePoint n P S i p ≠ vertexPoint j
  cases hc : crossingOwners n P S p with
  | none =>
    simp only [wireImagePoint, hc]
    intro he
    have hv := (onWire_vertexPoint_iff hl.1.1 hl.1.2.2.1.symm j).mp
      (by simpa only [he] using hl.2.1)
    rcases hv with rfl | rfl
    · exact hl.2.2.1 he
    · exact hl.2.2.2 he
  | some owners =>
    intro he
    have h := wireImagePoint_not_onWire hc hl.1.2.1 hl.1.2.2 hl.2.1
      (m := 0) (b := j) (d := j)
    apply h
    rw [he]
    exact Or.inl ⟨rfl, Nat.zero_le _⟩

/-- Coordinates distinguish all live original vertices and interior occurrences. -/
theorem routedCoordinate_injective_live {n : ℕ} {P S : ℕ → ℕ} {a b : WireNode}
    (ha : liveWireNode n P S a) (hb : liveWireNode n P S b)
    (he : routedCoordinate n P S a = routedCoordinate n P S b) : a = b := by
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (vertexPoint_injective he)
    | inr jp =>
      exact False.elim (routedCoordinate_interior_ne_vertex hb i he.symm)
  | inr ip =>
    cases b with
    | inl j => exact False.elim (routedCoordinate_interior_ne_vertex ha j he)
    | inr jp =>
      obtain ⟨hi, hp⟩ := wireImagePoint_injective ha.1.1 hb.1.1 ha.1.2.1 hb.1.2.1
        ha.1.2.2 hb.1.2.2 ha.2.1 hb.2.1 ha.2.2.1 ha.2.2.2 he
      exact congrArg Sum.inr (Prod.ext hi hp)

end GameTheory.Math.GridWire
