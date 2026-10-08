import GameTheory.Math.GridCrossingLocator

/-! A wire occurrence at a crossing center moves to its assigned gadget bend.
All other points keep their coordinates. This separates the two wire copies
of a crossing while retaining original graph vertices. -/

namespace GameTheory.Math.GridWire

open GameTheory.Math.GridCrossing GameTheory.Math.EndOfLine

/-- Place the two occurrences of a crossing at its two distinct bends. -/
def wireImagePoint (n : ℕ) (P S : ℕ → ℕ) (owner : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  match crossingOwners n P S p with
  | none => p
  | some (i, k) =>
    let rightward := decide (p.2 = 6 * i)
    let upward := decide (6 * k < 6 * S k + 3)
    if owner = i then placedCoordinate p (.bend (horizontalBend rightward upward))
    else if owner = k then placedCoordinate p (.bend (verticalBend rightward upward))
    else p

/-- Only the two crossing owners can have a consistent wire through its center. -/
theorem crossingOwners_onWire {n i k a : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hc : crossingOwners n P S p = some (i, k)) (hsa : S a < n)
    (ha : HasSuccessor P S a) (hp : onWire n a (S a) p) : a = i ∨ a = k := by
  obtain ⟨_, _, _, hsk, _, hai, _, hh, hv⟩ := crossingOwners_sound hc
  by_contra h
  push Not at h
  exact activeWire_crossing_exclusion hsa hsk hai ha h.1 h.2 hh hv
    (by unfold crossingNeighborhood; omega) hp

/-- A moved wire point lies in its unique crossing box. -/
theorem wireImagePoint_neighborhood {n i k a : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hc : crossingOwners n P S p = some (i, k)) :
    crossingNeighborhood p (wireImagePoint n P S a p) := by
  obtain ⟨_, _, _, _, _, _, _, hh, hv⟩ := crossingOwners_sound hc
  obtain ⟨hx, hy⟩ := crossing_clearance hh hv
  unfold wireImagePoint
  rw [hc]
  dsimp only
  split_ifs
  · exact placedCoordinate_mem_neighborhood (by omega) (by omega) _
  · exact placedCoordinate_mem_neighborhood (by omega) (by omega) _
  · unfold crossingNeighborhood
    omega

/-- A moved crossing occurrence cannot collide with any ordinary wire point. -/
theorem wireImagePoint_not_onWire {n i k a m b d : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hc : crossingOwners n P S p = some (i, k)) (hsa : S a < n)
    (ha : HasSuccessor P S a) (hp : onWire n a (S a) p) :
    ¬onWire m b d (wireImagePoint n P S a p) := by
  obtain ⟨_, _, _, _, _, _, _, hh, hv⟩ := crossingOwners_sound hc
  obtain ⟨hx, hy⟩ := crossing_clearance hh hv
  obtain ⟨hxm, hym⟩ := crossing_coordinates hh hv
  obtain h | h := crossingOwners_onWire hc hsa ha hp
  · subst a
    simp only [wireImagePoint, hc]
    exact placed_bend_not_onWire hx hy hxm hym _ m b d
  · subst a
    obtain ⟨_, _, _, _, hik, _⟩ := crossingOwners_sound hc
    simp only [wireImagePoint, hc, ite_eq_right hik.symm]
    exact placed_bend_not_onWire hx hy hxm hym _ m b d

/-- The two occurrences of a crossing have different geometric images. -/
theorem wireImagePoint_crossing_ne {n i k : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hc : crossingOwners n P S p = some (i, k)) :
    wireImagePoint n P S i p ≠ wireImagePoint n P S k p := by
  obtain ⟨_, _, _, _, hik, _⟩ := crossingOwners_sound hc
  intro h
  simp only [wireImagePoint, hc, ite_eq_right hik.symm] at h
  exact horizontalBend_ne_verticalBend _ _
    (CrossingNode.bend.inj (placedCoordinate_injective p h))

/-- A non-vertex wire occurrence cannot collide with any other consistent wire
occurrence. Moving just the crossing centers makes the entire live image injective. -/
theorem wireImagePoint_injective {n a b : ℕ} {P S : ℕ → ℕ} {p q : ℕ × ℕ}
    (ha : a < n) (hb : b < n) (hsa : S a < n) (hsb : S b < n)
    (haa : HasSuccessor P S a) (hab : HasSuccessor P S b)
    (hpa : onWire n a (S a) p) (hqb : onWire n b (S b) q)
    (hps : p ≠ vertexPoint a) (hpt : p ≠ vertexPoint (S a))
    (he : wireImagePoint n P S a p = wireImagePoint n P S b q) : a = b ∧ p = q := by
  cases hp : crossingOwners n P S p with
  | none =>
    cases hq : crossingOwners n P S q with
    | none =>
      simp only [wireImagePoint, hp, hq] at he
      subst q
      by_cases habNe : a = b
      · exact ⟨habNe, rfl⟩
      · obtain h | h | h | h := activeWire_intersection_cases
          ha hb hsa hsb habNe haa hab hpa hqb
        · exact False.elim (hps h.1)
        · exact False.elim (hpt h.1)
        · have hc := crossingOwners_complete ha hb hsa hsb habNe haa hab h.1 h.2
          rw [hp] at hc
          cases hc
        · have hc := crossingOwners_complete hb ha hsb hsa (Ne.symm habNe) hab haa h.2 h.1
          rw [hp] at hc
          cases hc
    | some owners =>
      rcases owners with ⟨i, k⟩
      have hn := wireImagePoint_not_onWire hq hsb hab hqb (m := n) (b := a) (d := S a)
      simp only [wireImagePoint, hp] at he
      change p = wireImagePoint n P S b q at he
      rw [← he] at hn
      exact False.elim (hn hpa)
  | some owners =>
    rcases owners with ⟨i, k⟩
    cases hq : crossingOwners n P S q with
    | none =>
      have hn := wireImagePoint_not_onWire hp hsa haa hpa (m := n) (b := b) (d := S b)
      simp only [wireImagePoint, hq] at he
      change wireImagePoint n P S a p = q at he
      rw [he] at hn
      exact False.elim (hn hqb)
    | some others =>
      rcases others with ⟨j, l⟩
      obtain ⟨_, _, _, _, _, _, _, hh, hv⟩ := crossingOwners_sound hp
      obtain ⟨_, _, _, _, _, _, _, hh', hv'⟩ := crossingOwners_sound hq
      have hpq : p = q := by
        by_contra h
        have hbox := wireImagePoint_neighborhood hq (a := b)
        rw [← he] at hbox
        exact crossingNeighborhood_disjoint (crossing_coordinates hh hv)
          (crossing_coordinates hh' hv') h (wireImagePoint_neighborhood hp)
          hbox
      subst q
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hp.symm.trans hq))
      obtain h | h := crossingOwners_onWire hp hsa haa hpa <;>
        obtain h' | h' := crossingOwners_onWire hp hsb hab hqb
      · subst a; subst b
        exact ⟨rfl, rfl⟩
      · subst a; subst b
        exact False.elim (wireImagePoint_crossing_ne hp he)
      · subst a; subst b
        exact False.elim (wireImagePoint_crossing_ne hp he.symm)
      · subst a; subst b
        exact ⟨rfl, rfl⟩

end GameTheory.Math.GridWire
