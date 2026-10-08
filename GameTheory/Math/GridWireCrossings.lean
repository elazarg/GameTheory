import GameTheory.Math.GridWireLanes

/-! Distinct directed edges with distinct sources and targets can share an
interior grid point only at a strict horizontal/vertical crossing. The private
columns and separate incoming and outgoing rows keep crossings away from bends. -/

namespace GameTheory.Math.GridWire

/-- A point strictly inside either horizontal segment of a routed edge. -/
def horizontalInterior (n i j : ℕ) (p : ℕ × ℕ) : Prop :=
  0 < p.1 ∧ p.1 < wireColumn n i j ∧ (p.2 = 6 * i ∨ p.2 = 6 * j + 3)

/-- A point strictly inside the long vertical segment of a routed edge. -/
def verticalInterior (n i j : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 = wireColumn n i j ∧ min (6 * i) (6 * j + 3) < p.2 ∧
    p.2 < max (6 * i) (6 * j + 3)

instance (n i j : ℕ) (p : ℕ × ℕ) : Decidable (horizontalInterior n i j p) :=
  inferInstanceAs (Decidable
    (0 < p.1 ∧ p.1 < wireColumn n i j ∧ (p.2 = 6 * i ∨ p.2 = 6 * j + 3)))

instance (n i j : ℕ) (p : ℕ × ℕ) : Decidable (verticalInterior n i j p) :=
  inferInstanceAs (Decidable
    (p.1 = wireColumn n i j ∧ min (6 * i) (6 * j + 3) < p.2 ∧
      p.2 < max (6 * i) (6 * j + 3)))

/-- A shared positive-column point is a proper crossing, rather than a bend
or overlapping segment, when both sources, targets and allocated columns differ. -/
theorem onWire_intersection {n i j k l : ℕ} {p : ℕ × ℕ}
    (hi : i ≠ k) (hj : j ≠ l)
    (hc : wireColumn n i j ≠ wireColumn n k l) (hx : 0 < p.1)
    (ha : onWire n i j p) (hb : onWire n k l p) :
    (horizontalInterior n i j p ∧ verticalInterior n k l p) ∨
      (verticalInterior n i j p ∧ horizontalInterior n k l p) := by
  rcases ha with ha | ha | ha | ha <;>
    rcases hb with hb | hb | hb | hb <;>
    simp only [horizontalInterior, verticalInterior] <;> omega

/-- At the vertex boundary, distinct source and target lanes can meet only
where the target of one edge is the source of the other. -/
theorem onWire_boundary_intersection {n i j k l : ℕ} {p : ℕ × ℕ}
    (hi : i ≠ k) (hj : j ≠ l)
    (haColumn : 0 < wireColumn n i j) (hbColumn : 0 < wireColumn n k l)
    (hx : p.1 = 0) (ha : onWire n i j p) (hb : onWire n k l p) :
    (p = vertexPoint i ∧ i = l) ∨ (p = vertexPoint j ∧ j = k) := by
  rcases p with ⟨x, y⟩
  rcases ha with ha | ha | ha | ha <;>
    rcases hb with hb | hb | hb | hb <;>
    simp only [vertexPoint, Prod.mk.injEq] <;> omega

/-- Proper crossings occur on the spacing-three subgrid. -/
theorem crossing_coordinates {n i j k l : ℕ} {p : ℕ × ℕ}
    (hh : horizontalInterior n i j p) (hv : verticalInterior n k l p) :
    p.1 % 3 = 0 ∧ p.2 % 3 = 0 := by
  rcases hh with ⟨_, _, hy | hy⟩ <;>
    rcases hv with ⟨hx, _, _⟩ <;>
    simp [hx, hy, wireColumn, Nat.mul_mod]

/-- A proper crossing leaves room for a radius-one switch on either axis. -/
theorem crossing_clearance {n i j k l : ℕ} {p : ℕ × ℕ}
    (hh : horizontalInterior n i j p) (hv : verticalInterior n k l p) :
    3 ≤ p.1 ∧ 3 ≤ p.2 := by
  have hm := crossing_coordinates hh hv
  rcases hh with ⟨hx, _, _⟩
  rcases hv with ⟨_, hy, _⟩
  omega

/-- The center is at least three grid steps from the horizontal and vertical
bends. The switch and its exterior neighbors therefore fit inside the strands. -/
theorem crossing_segment_clearance {n i j k l : ℕ} {p : ℕ × ℕ}
    (hh : horizontalInterior n i j p) (hv : verticalInterior n k l p) :
    p.1 + 3 ≤ wireColumn n i j ∧
      min (6 * k) (6 * l + 3) + 3 ≤ p.2 ∧
      p.2 + 3 ≤ max (6 * k) (6 * l + 3) := by
  have hm := crossing_coordinates hh hv
  have hc : wireColumn n i j % 3 = 0 := by simp [wireColumn]
  rcases hh with ⟨_, hx, _⟩
  rcases hv with ⟨_, hy, hz⟩
  simp only [Nat.min_def, Nat.max_def] at hy hz ⊢
  split_ifs at hy hz ⊢ <;> omega

/-- The three-by-three grid box used to replace a crossing. -/
def crossingNeighborhood (center p : ℕ × ℕ) : Prop :=
  center.1 ≤ p.1 + 1 ∧ p.1 ≤ center.1 + 1 ∧
    center.2 ≤ p.2 + 1 ∧ p.2 ≤ center.2 + 1

/-- Distinct spacing-three centers have disjoint switch boxes. Their boundary
ports may be adjacent, so no extra empty row or column is assumed. -/
theorem crossingNeighborhood_disjoint {a b p : ℕ × ℕ}
    (ha : a.1 % 3 = 0 ∧ a.2 % 3 = 0)
    (hb : b.1 % 3 = 0 ∧ b.2 % 3 = 0) (hne : a ≠ b)
    (hpa : crossingNeighborhood a p) (hpb : crossingNeighborhood b p) : False := by
  apply hne
  apply Prod.ext
  all_goals unfold crossingNeighborhood at hpa hpb
  all_goals omega

/-- A third edge cannot enter a switch box if it shares neither horizontal
lane with the horizontal edge nor a column with the vertical edge. -/
theorem crossingNeighborhood_wire_exclusion {n i j k l a b : ℕ} {center p : ℕ × ℕ}
    (hh : horizontalInterior n i j center) (hv : verticalInterior n k l center)
    (hi : a ≠ i) (hj : b ≠ j)
    (hc : wireColumn n a b ≠ wireColumn n k l)
    (hp : crossingNeighborhood center p) (hw : onWire n a b p) : False := by
  have hm := crossing_coordinates hh hv
  have hclear := crossing_clearance hh hv
  have hcol : wireColumn n a b % 3 = 0 := by simp [wireColumn]
  rcases hh with ⟨_, _, hy | hy⟩ <;>
    rcases hv with ⟨hx, _, _⟩ <;>
    rcases hw with hw | hw | hw | hw <;>
    unfold crossingNeighborhood at hp <;> omega

/-- Two distinct consistent End-of-Line edges meet only at a common original
vertex or at a proper horizontal/vertical crossing. Reciprocal pointers supply
the uniqueness of their target lanes. -/
theorem activeWire_intersection_cases {n i k : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hi : i < n) (hk : k < n) (hsi : S i < n) (hsk : S k < n) (hne : i ≠ k)
    (hai : GameTheory.Math.EndOfLine.HasSuccessor P S i)
    (hak : GameTheory.Math.EndOfLine.HasSuccessor P S k)
    (ha : onWire n i (S i) p) (hb : onWire n k (S k) p) :
    (p = vertexPoint i ∧ i = S k) ∨ (p = vertexPoint (S i) ∧ S i = k) ∨
      (horizontalInterior n i (S i) p ∧ verticalInterior n k (S k) p) ∨
      (verticalInterior n i (S i) p ∧ horizontalInterior n k (S k) p) := by
  have ht : S i ≠ S k := by
    intro h
    exact hne (hai.2.symm.trans ((congrArg P h).trans hak.2))
  by_cases hx : p.1 = 0
  · obtain h | h := onWire_boundary_intersection hne ht
      (wireColumn_pos hi hai.1.symm) (wireColumn_pos hk hak.1.symm) hx ha hb
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hc : wireColumn n i (S i) ≠ wireColumn n k (S k) := by
      intro h
      exact hne ((wireColumn_eq_iff hsi hsk).mp h).1
    exact Or.inr (Or.inr (onWire_intersection hne ht hc (by omega) ha hb))

/-- No third consistent edge enters the switch box of two crossing edges. -/
theorem activeWire_crossing_exclusion {n i k a : ℕ} {P S : ℕ → ℕ}
    {center p : ℕ × ℕ} (hsa : S a < n) (hsk : S k < n)
    (hai : GameTheory.Math.EndOfLine.HasSuccessor P S i)
    (haa : GameTheory.Math.EndOfLine.HasSuccessor P S a) (haiNe : a ≠ i) (hakNe : a ≠ k)
    (hh : horizontalInterior n i (S i) center) (hv : verticalInterior n k (S k) center)
    (hp : crossingNeighborhood center p) : ¬onWire n a (S a) p := by
  have ht : S a ≠ S i := by
    intro h
    exact haiNe (haa.2.symm.trans ((congrArg P h).trans hai.2))
  have hc : wireColumn n a (S a) ≠ wireColumn n k (S k) := by
    intro h
    exact hakNe ((wireColumn_eq_iff hsa hsk).mp h).1
  exact crossingNeighborhood_wire_exclusion hh hv haiNe ht hc hp

end GameTheory.Math.GridWire
