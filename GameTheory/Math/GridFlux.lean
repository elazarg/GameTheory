import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

/-! Signed flux on a square grid cancels along shared interior edges. Summing
cell boundaries therefore leaves only the oriented outer boundary. -/

namespace GameTheory.Math.Sperner

open scoped BigOperators

/-- Counterclockwise boundary flux of one square, using rightward horizontal
and upward vertical edge orientations. -/
def cellBoundaryFlux (h v : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ :=
  h i j + v (i + 1) j - h i (j + 1) - v i j

/-- Interior edges cancel exactly, leaving the four oriented boundary sums. -/
theorem sum_cellBoundaryFlux (h v : ℕ → ℕ → ℤ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, cellBoundaryFlux h v i j) =
      (∑ i ∈ Finset.range n, (h i 0 - h i n)) +
        (∑ j ∈ Finset.range n, (v n j - v 0 j)) := by
  have hh : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (h i j - h i (j + 1))) =
      ∑ i ∈ Finset.range n, (h i 0 - h i n) := by
    simp_rw [Finset.sum_range_sub']
  have hv : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (v (i + 1) j - v i j)) =
      ∑ j ∈ Finset.range n, (v n j - v 0 j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_range_sub (fun i => v i j) n
  calc
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        ((h i j - h i (j + 1)) + (v (i + 1) j - v i j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      unfold cellBoundaryFlux
      ring
    _ = _ := by simp_rw [Finset.sum_add_distrib]; rw [hh, hv]

end GameTheory.Math.Sperner
