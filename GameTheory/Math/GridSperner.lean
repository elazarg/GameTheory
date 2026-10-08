import GameTheory.Math.SpernerTriangle
import GameTheory.Math.GridFlux

/-! Sperner colorings of a square grid with each square split along its rising
diagonal. Oriented edge counts cancel inside the grid; the boundary has net
count one, so a triangular cell must contain all three colors. -/

namespace GameTheory.Math.Sperner

open scoped BigOperators

/-- The usual square-grid boundary exclusions: left forbids one, bottom two,
and top and right zero. Interior colors are unrestricted. -/
def GridBoundary (color : ℕ → ℕ → Fin 3) (n : ℕ) : Prop :=
  (∀ j, j ≤ n → color 0 j ≠ 1) ∧
    (∀ i, i ≤ n → color i 0 ≠ 2) ∧
    (∀ j, j ≤ n → color n j ≠ 0) ∧
    (∀ i, i ≤ n → color i n ≠ 0)

/-- Enforce a fixed Sperner boundary while keeping every interior color.
The rule checks coordinates locally and does not enumerate the grid. -/
def standardGridColor (n : ℕ) (interior : ℕ → ℕ → Fin 3) (i j : ℕ) : Fin 3 :=
  if j = 0 then if i = 0 then 0 else 1
  else if i = n ∨ j = n then 2
  else if i = 0 then 0 else interior i j

/-- Local boundary enforcement produces a Sperner coloring at positive grid size. -/
theorem standardGridColor_boundary (n : ℕ) (interior : ℕ → ℕ → Fin 3)
    (hn : 0 < n) : GridBoundary (standardGridColor n interior) n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [standardGridColor]
    split_ifs <;> simp_all
  · intro i hi
    simp only [standardGridColor]
    split_ifs <;> simp_all
  · intro j hj
    simp only [standardGridColor]
    split_ifs <;> simp_all
  · intro i hi
    simp [standardGridColor, Nat.ne_of_gt hn]

/-- Boundary enforcement leaves strict interior vertices unchanged. -/
theorem standardGridColor_interior {n i j : ℕ} (color : ℕ → ℕ → Fin 3)
    (hi : 0 < i) (hin : i < n) (hj : 0 < j) (hjn : j < n) :
    standardGridColor n color i j = color i j := by
  simp [standardGridColor, Nat.ne_of_gt hi, Nat.ne_of_lt hin,
    Nat.ne_of_gt hj, Nat.ne_of_lt hjn]

/-- The oriented count in the lower triangle of a grid square. -/
def lowerFlux (color : ℕ → ℕ → Fin 3) (i j : ℕ) : ℤ :=
  triangleFlux (color i j) (color (i + 1) j) (color (i + 1) (j + 1))

/-- The oriented count in the upper triangle of a grid square. -/
def upperFlux (color : ℕ → ℕ → Fin 3) (i j : ℕ) : ℤ :=
  triangleFlux (color i j) (color (i + 1) (j + 1)) (color i (j + 1))

/-- The shared diagonal cancels between the two counterclockwise triangles. -/
theorem squareFlux_eq (color : ℕ → ℕ → Fin 3) (i j : ℕ) :
    lowerFlux color i j + upperFlux color i j =
      cellBoundaryFlux (fun i j => edgeFlux (color i j) (color (i + 1) j))
        (fun i j => edgeFlux (color i j) (color i (j + 1))) i j := by
  unfold lowerFlux upperFlux triangleFlux cellBoundaryFlux
  rw [edgeFlux_reverse (color i j) (color (i + 1) (j + 1)),
    edgeFlux_reverse (color i (j + 1)) (color (i + 1) (j + 1)),
    edgeFlux_reverse (color i j) (color i (j + 1))]
  dsimp only
  omega

private theorem bottom_flux {color : ℕ → ℕ → Fin 3} {n : ℕ}
    (hb : GridBoundary color n) :
    (∑ i ∈ Finset.range n, edgeFlux (color i 0) (color (i + 1) 0)) = 1 := by
  have hzero : color 0 0 = 0 := by
    have h : ∀ a : Fin 3, a ≠ 1 → a ≠ 2 → a = 0 := by decide
    exact h _ (hb.1 0 (Nat.zero_le n)) (hb.2.1 0 (Nat.zero_le n))
  have hone : color n 0 = 1 := by
    have h : ∀ a : Fin 3, a ≠ 0 → a ≠ 2 → a = 1 := by decide
    exact h _ (hb.2.2.1 0 (Nat.zero_le n)) (hb.2.1 n le_rfl)
  calc
    _ = ∑ i ∈ Finset.range n,
        ((if color (i + 1) 0 = 1 then (1 : ℤ) else 0) -
          (if color i 0 = 1 then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact edgeFlux_eq_indicator_sub (hb.2.1 i (by omega))
        (hb.2.1 (i + 1) (by omega))
    _ = _ := by
      rw [Finset.sum_range_sub (fun i => if color i 0 = 1 then (1 : ℤ) else 0)]
      simp [hzero, hone]

/-- The total oriented triangle count is one for every Sperner boundary coloring. -/
theorem sum_gridFlux_eq_one {color : ℕ → ℕ → Fin 3} {n : ℕ}
    (hb : GridBoundary color n) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (lowerFlux color i j + upperFlux color i j)) = 1 := by
  simp_rw [squareFlux_eq]
  rw [sum_cellBoundaryFlux]
  have htop : ∀ i ∈ Finset.range n, edgeFlux (color i n) (color (i + 1) n) = 0 := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact edgeFlux_eq_zero_of_ne_zero (hb.2.2.2 i (by omega))
      (hb.2.2.2 (i + 1) (by omega))
  have hright : ∀ j ∈ Finset.range n, edgeFlux (color n j) (color n (j + 1)) = 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact edgeFlux_eq_zero_of_ne_zero (hb.2.2.1 j (by omega))
      (hb.2.2.1 (j + 1) (by omega))
  have hleft : ∀ j ∈ Finset.range n, edgeFlux (color 0 j) (color 0 (j + 1)) = 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact edgeFlux_eq_zero_of_ne_one (hb.1 j (by omega)) (hb.1 (j + 1) (by omega))
  have hfirst : (∑ i ∈ Finset.range n,
      (edgeFlux (color i 0) (color (i + 1) 0) - edgeFlux (color i n) (color (i + 1) n))) =
        ∑ i ∈ Finset.range n, edgeFlux (color i 0) (color (i + 1) 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [htop i hi, sub_zero]
  have hsecond : (∑ j ∈ Finset.range n,
      (edgeFlux (color n j) (color n (j + 1)) - edgeFlux (color 0 j) (color 0 (j + 1)))) =
        0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hright j hj, hleft j hj, sub_self]
  rw [hfirst, hsecond, add_zero, bottom_flux hb]

/-- A Sperner coloring contains a trichromatic triangle in one of the two
halves of a grid square. Its witness uses only the square coordinates and half. -/
theorem exists_grid_trichromatic {color : ℕ → ℕ → Fin 3} {n : ℕ}
    (hb : GridBoundary color n) :
    ∃ i < n, ∃ j < n,
      Trichromatic (color i j) (color (i + 1) j) (color (i + 1) (j + 1)) ∨
        Trichromatic (color i j) (color (i + 1) (j + 1)) (color i (j + 1)) := by
  have hsum : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (lowerFlux color i j + upperFlux color i j)) ≠ 0 := by
    rw [sum_gridFlux_eq_one hb]
    decide
  obtain ⟨i, hi, hrow⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  obtain ⟨j, hj, hcell⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrow
  refine ⟨i, Finset.mem_range.mp hi, j, Finset.mem_range.mp hj, ?_⟩
  by_cases hlower : lowerFlux color i j = 0
  · right
    apply (triangleFlux_ne_zero_iff_trichromatic _ _ _).mp
    change upperFlux color i j ≠ 0
    simpa only [hlower, zero_add] using hcell
  · left
    exact (triangleFlux_ne_zero_iff_trichromatic _ _ _).mp hlower

end GameTheory.Math.Sperner
