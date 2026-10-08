import GameTheory.Math.GridWireColoringTile
import GameTheory.Math.GridCrossingGeometry
import GameTheory.Math.EndOfLineTwoCycle

/-! Reciprocal unit grid pointers determine compatible tile ports. Isolated
two-cycles are erased so an incoming and outgoing port never coincide. -/

namespace GameTheory.Math.Sperner

open GridCrossing EndOfLine

/-- Direction of a unit grid step: north, east, south, west, or no unit step. -/
def gridDirection (p q : ℕ × ℕ) : Option (Fin 4) :=
  if p.1 = q.1 ∧ p.2 + 1 = q.2 then some 0
  else if p.1 + 1 = q.1 ∧ p.2 = q.2 then some 1
  else if p.1 = q.1 ∧ q.2 + 1 = p.2 then some 2
  else if q.1 + 1 = p.1 ∧ p.2 = q.2 then some 3 else none

/-- Each direction records its exact coordinate displacement. -/
theorem gridDirection_eq_some_iff (p q : ℕ × ℕ) (d : Fin 4) :
    gridDirection p q = some d ↔
      if d = 0 then p.1 = q.1 ∧ p.2 + 1 = q.2
      else if d = 1 then p.1 + 1 = q.1 ∧ p.2 = q.2
      else if d = 2 then p.1 = q.1 ∧ q.2 + 1 = p.2
      else q.1 + 1 = p.1 ∧ p.2 = q.2 := by
  fin_cases d <;> simp only [gridDirection] <;> split_ifs <;> simp_all <;> omega

/-- A stationary pointer has no direction. -/
@[simp] theorem gridDirection_self (p : ℕ × ℕ) : gridDirection p p = none := by
  simp [gridDirection]

/-- Among stationary and unit pointers, absence of a direction means stationary. -/
theorem gridDirection_eq_none_iff (p q : ℕ × ℕ)
    (h : q = p ∨ axisUnitAdjacent p q) : gridDirection p q = none ↔ q = p := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨u, v⟩
  simp only [axisUnitAdjacent, Prod.mk.injEq] at h
  simp only [gridDirection]
  split_ifs <;> simp_all <;> omega

/-- A direction uniquely determines the neighboring grid point. -/
theorem gridDirection_some_injective {p q r : ℕ × ℕ} {d : Fin 4}
    (hq : gridDirection p q = some d) (hr : gridDirection p r = some d) : q = r := by
  rw [gridDirection_eq_some_iff] at hq hr
  fin_cases d <;> simp at hq hr
    <;> apply Prod.ext <;> omega

/-- Reversing a unit step rotates its direction by two ports. -/
theorem gridDirection_reverse (p q : ℕ × ℕ) (d : Fin 4) :
    gridDirection p q = some d ↔ gridDirection q p = some (d + 2) := by
  rw [gridDirection_eq_some_iff, gridDirection_eq_some_iff]
  fin_cases d <;> simp <;> omega

/-- Incoming port after deleting isolated two-cycles. -/
def gridIncomingPort (P S : (ℕ × ℕ) → ℕ × ℕ) (p : ℕ × ℕ) : Option (Fin 4) :=
  gridDirection p (eraseTwoCyclePredecessor P S p)

/-- Outgoing port after deleting isolated two-cycles. -/
def gridOutgoingPort (P S : (ℕ × ℕ) → ℕ × ℕ) (p : ℕ × ℕ) : Option (Fin 4) :=
  gridDirection p (eraseTwoCycleSuccessor P S p)

private theorem erased_predecessor_local (P S : (ℕ × ℕ) → ℕ × ℕ)
    (hP : ∀ p, P p ≠ p → axisUnitAdjacent p (P p)) (p : ℕ × ℕ) :
    eraseTwoCyclePredecessor P S p = p ∨
      axisUnitAdjacent p (eraseTwoCyclePredecessor P S p) := by
  by_cases h : P p = S p
  · simp [eraseTwoCyclePredecessor, h]
  · simp only [eraseTwoCyclePredecessor, ite_eq_right h]
    by_cases hp : P p = p
    · exact Or.inl hp
    · exact Or.inr (hP p hp)

private theorem erased_successor_local (P S : (ℕ × ℕ) → ℕ × ℕ)
    (hS : ∀ p, S p ≠ p → axisUnitAdjacent p (S p)) (p : ℕ × ℕ) :
    eraseTwoCycleSuccessor P S p = p ∨
      axisUnitAdjacent p (eraseTwoCycleSuccessor P S p) := by
  by_cases h : P p = S p
  · simp [eraseTwoCycleSuccessor, h]
  · simp only [eraseTwoCycleSuccessor, ite_eq_right h]
    by_cases hs : S p = p
    · exact Or.inl hs
    · exact Or.inr (hS p hs)

/-- Incoming port absence is precisely a stationary normalized predecessor. -/
theorem gridIncomingPort_eq_none_iff (P S : (ℕ × ℕ) → ℕ × ℕ)
    (hP : ∀ p, P p ≠ p → axisUnitAdjacent p (P p)) (p : ℕ × ℕ) :
    gridIncomingPort P S p = none ↔ eraseTwoCyclePredecessor P S p = p :=
  gridDirection_eq_none_iff p _ (erased_predecessor_local P S hP p)

/-- Outgoing port absence is precisely a stationary normalized successor. -/
theorem gridOutgoingPort_eq_none_iff (P S : (ℕ × ℕ) → ℕ × ℕ)
    (hS : ∀ p, S p ≠ p → axisUnitAdjacent p (S p)) (p : ℕ × ℕ) :
    gridOutgoingPort P S p = none ↔ eraseTwoCycleSuccessor P S p = p :=
  gridDirection_eq_none_iff p _ (erased_successor_local P S hS p)

/-- Two-cycle removal makes the incoming and outgoing tile ports valid. -/
theorem gridPorts_valid (P S : (ℕ × ℕ) → ℕ × ℕ)
    (hP : ∀ p, P p ≠ p → axisUnitAdjacent p (P p)) (p : ℕ × ℕ) :
    ValidTilePorts (gridIncomingPort P S p) (gridOutgoingPort P S p) := by
  by_cases hn : gridIncomingPort P S p = none
  · exact Or.inr hn
  · apply Or.inl
    intro he
    cases hi : gridIncomingPort P S p with
    | none => exact hn hi
    | some d =>
      have ho : gridOutgoingPort P S p = some d := he.symm.trans hi
      have hp : eraseTwoCyclePredecessor P S p ≠ p := by
        intro hp
        exact hn ((gridIncomingPort_eq_none_iff P S hP p).mpr hp)
      exact eraseTwoCycle_distinct_neighbors P S p (Or.inl hp)
        (gridDirection_some_injective hi ho)

/-- Tile endpoints coincide with original graph endpoints in every component. -/
theorem gridPorts_endpoint_iff (P S : (ℕ × ℕ) → ℕ × ℕ)
    (hP : ∀ p, P p ≠ p → S (P p) = p)
    (hS : ∀ p, S p ≠ p → P (S p) = p)
    (hPa : ∀ p, P p ≠ p → axisUnitAdjacent p (P p))
    (hSa : ∀ p, S p ≠ p → axisUnitAdjacent p (S p)) (p : ℕ × ℕ) :
    TileEndpoint (gridIncomingPort P S p) (gridOutgoingPort P S p) ↔
      IsEndpoint P S p := by
  rw [← eraseTwoCycle_isEndpoint_iff P S hP hS p]
  have hp : HasPredecessor (eraseTwoCyclePredecessor P S)
      (eraseTwoCycleSuccessor P S) p ↔ eraseTwoCyclePredecessor P S p ≠ p :=
    ⟨fun h => h.1, fun h => ⟨h, eraseTwoCycle_predecessor_consistent P S hP p h⟩⟩
  have hs : HasSuccessor (eraseTwoCyclePredecessor P S)
      (eraseTwoCycleSuccessor P S) p ↔ eraseTwoCycleSuccessor P S p ≠ p :=
    ⟨fun h => h.1, fun h => ⟨h, eraseTwoCycle_successor_consistent P S hS p h⟩⟩
  simp only [TileEndpoint, IsEndpoint, hp, hs, ne_eq,
    gridIncomingPort_eq_none_iff P S hPa, gridOutgoingPort_eq_none_iff P S hSa]
  tauto

private theorem direction_pointer_eq {p q r : ℕ × ℕ} {d : Fin 4}
    (hq : gridDirection p q = some d) : gridDirection p r = some d ↔ r = q := by
  constructor
  · intro hr
    exact gridDirection_some_injective hr hq
  · rintro rfl
    exact hq

/-- Reciprocal normalized pointers use opposite incoming and outgoing ports. -/
theorem gridPorts_reverse (P S : (ℕ × ℕ) → ℕ × ℕ)
    (hP : ∀ p, P p ≠ p → S (P p) = p)
    (hS : ∀ p, S p ≠ p → P (S p) = p)
    {p q : ℕ × ℕ} {d : Fin 4} (hd : gridDirection p q = some d) :
    gridIncomingPort P S p = some d ↔ gridOutgoingPort P S q = some (d + 2) := by
  have hrev := (gridDirection_reverse p q d).mp hd
  have hne : q ≠ p := by
    rintro rfl
    simp at hd
  simp only [gridIncomingPort, gridOutgoingPort, direction_pointer_eq hd,
    direction_pointer_eq hrev]
  constructor
  · intro hp
    have hn : eraseTwoCyclePredecessor P S p ≠ p := by rw [hp]; exact hne
    simpa only [hp] using eraseTwoCycle_predecessor_consistent P S hP p hn
  · intro hs
    have hn : eraseTwoCycleSuccessor P S q ≠ q := by rw [hs]; exact hne.symm
    simpa only [hs] using eraseTwoCycle_successor_consistent P S hS q hn

private theorem portColor_east_west (a b c d : Option (Fin 4))
    (hab : ¬(a = some 1 ∧ b = some 1))
    (ha : a = some 1 ↔ d = some 3) (hb : b = some 1 ↔ c = some 3) (k : ℕ) :
    wireTilePortColor a b 1 k = wireTilePortColor c d 3 k := by
  by_cases hka : k = 2 <;> by_cases hkb : k = 3
    <;> by_cases hea : a = some 1 <;> by_cases heb : b = some 1
    <;> simp_all [wireTilePortColor, wireTileOutwardFirst]

private theorem portColor_north_south (a b c d : Option (Fin 4))
    (hab : ¬(a = some 0 ∧ b = some 0))
    (ha : a = some 0 ↔ d = some 2) (hb : b = some 0 ↔ c = some 2) (k : ℕ) :
    wireTilePortColor a b 0 k = wireTilePortColor c d 2 k := by
  by_cases hka : k = 2 <;> by_cases hkb : k = 3
    <;> by_cases hea : a = some 0 <;> by_cases heb : b = some 0
    <;> simp_all [wireTilePortColor, wireTileOutwardFirst]

private theorem gridPorts_not_same_direction (P S : (ℕ × ℕ) → ℕ × ℕ)
    (p : ℕ × ℕ) (d : Fin 4) :
    ¬(gridIncomingPort P S p = some d ∧ gridOutgoingPort P S p = some d) := by
  rintro ⟨hi, ho⟩
  have hp : eraseTwoCyclePredecessor P S p ≠ p := by
    intro hp
    have h : gridIncomingPort P S p = none := by
      unfold gridIncomingPort
      rw [hp, gridDirection_self]
    rw [h] at hi
    cases hi
  exact eraseTwoCycle_distinct_neighbors P S p (Or.inl hp)
    (gridDirection_some_injective hi ho)

/-- Reciprocal unit pointers give identical colors on an east-west tile seam. -/
theorem gridPorts_east_seam (P S : (ℕ × ℕ) → ℕ × ℕ)
    (hP : ∀ p, P p ≠ p → S (P p) = p)
    (hS : ∀ p, S p ≠ p → P (S p) = p) (i j k : ℕ) :
    wireTilePortColor (gridIncomingPort P S (i, j))
        (gridOutgoingPort P S (i, j)) 1 k =
      wireTilePortColor (gridIncomingPort P S (i + 1, j))
        (gridOutgoingPort P S (i + 1, j)) 3 k := by
  have hd : gridDirection (i, j) (i + 1, j) = some 1 := by
    rw [gridDirection_eq_some_iff]; simp
  have hr : gridDirection (i + 1, j) (i, j) = some 3 := by
    rw [gridDirection_eq_some_iff]; simp
  apply portColor_east_west
  · exact gridPorts_not_same_direction P S (i, j) 1
  · simpa using gridPorts_reverse P S hP hS hd
  · simpa using (gridPorts_reverse P S hP hS hr).symm

/-- Reciprocal unit pointers give identical colors on a north-south tile seam. -/
theorem gridPorts_north_seam (P S : (ℕ × ℕ) → ℕ × ℕ)
    (hP : ∀ p, P p ≠ p → S (P p) = p)
    (hS : ∀ p, S p ≠ p → P (S p) = p) (i j k : ℕ) :
    wireTilePortColor (gridIncomingPort P S (i, j))
        (gridOutgoingPort P S (i, j)) 0 k =
      wireTilePortColor (gridIncomingPort P S (i, j + 1))
        (gridOutgoingPort P S (i, j + 1)) 2 k := by
  have hd : gridDirection (i, j) (i, j + 1) = some 0 := by
    rw [gridDirection_eq_some_iff]; simp
  have hr : gridDirection (i, j + 1) (i, j) = some 2 := by
    rw [gridDirection_eq_some_iff]; simp
  apply portColor_north_south
  · exact gridPorts_not_same_direction P S (i, j) 0
  · simpa using gridPorts_reverse P S hP hS hd
  · simpa using (gridPorts_reverse P S hP hS hr).symm

end GameTheory.Math.Sperner


