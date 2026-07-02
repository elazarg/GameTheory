/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# Finite Coordinate Sum Helpers

Small lemmas for splitting a `Fin (n + 1)` sum into its first `n`
coordinates and its last coordinate.
-/

namespace Math
namespace Fin

open Finset

/-- If the coordinates of a vector on `Fin (n + 1)` sum to `1`, then the last
coordinate is `1` minus the sum of the preceding coordinates. -/
theorem last_eq_one_sub_sum_castSucc {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hsum : ∑ i : Fin (n + 1), x i = 1) :
    x (.last n) = 1 - ∑ i : Fin n, x i.castSucc := by
  have hsplit := Fin.sum_univ_castSucc x
  rw [hsplit] at hsum
  linarith

/-- If two `Fin (n + 1)` vectors have the same total sum, then the difference
of their last coordinates is the negative of the sum of the preceding coordinate
differences. -/
theorem last_sub_last_eq_sum_sub_castSucc {n : ℕ} (x y : Fin (n + 1) → ℝ)
    (hsum : ∑ i : Fin (n + 1), x i = ∑ i : Fin (n + 1), y i) :
    x (.last n) - y (.last n) =
      ∑ i : Fin n, (y i.castSucc - x i.castSucc) := by
  have hxsplit := Fin.sum_univ_castSucc x
  have hysplit := Fin.sum_univ_castSucc y
  rw [hxsplit, hysplit] at hsum
  rw [Finset.sum_sub_distrib]
  linarith

/-- If two `Fin (n + 1)` vectors have the same total sum, the difference of
their last coordinates is bounded by the sum of absolute differences of the
preceding coordinates. -/
theorem abs_last_sub_last_le_sum_abs_castSucc_of_sum_eq {n : ℕ}
    (x y : Fin (n + 1) → ℝ)
    (hsum : ∑ i : Fin (n + 1), x i = ∑ i : Fin (n + 1), y i) :
    |x (.last n) - y (.last n)| ≤
      ∑ i : Fin n, |x i.castSucc - y i.castSucc| := by
  rw [last_sub_last_eq_sum_sub_castSucc x y hsum]
  calc
    |∑ i : Fin n, (y i.castSucc - x i.castSucc)|
        ≤ ∑ i : Fin n, |y i.castSucc - x i.castSucc| :=
          Finset.abs_sum_le_sum_abs
            (fun i : Fin n => y i.castSucc - x i.castSucc) Finset.univ
    _ = ∑ i : Fin n, |x i.castSucc - y i.castSucc| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_sub_comm]

/-- For two `Fin (n + 1)` vectors with the same total sum `1`, the difference
of their last coordinates is bounded by the sum of absolute differences of the
preceding coordinates. -/
theorem abs_last_sub_last_le_sum_abs_castSucc {n : ℕ} (x y : Fin (n + 1) → ℝ)
    (hxsum : ∑ i : Fin (n + 1), x i = 1)
    (hysum : ∑ i : Fin (n + 1), y i = 1) :
    |x (.last n) - y (.last n)| ≤
      ∑ i : Fin n, |x i.castSucc - y i.castSucc| := by
  exact abs_last_sub_last_le_sum_abs_castSucc_of_sum_eq x y (by rw [hxsum, hysum])

/-- Finite families have real shifts with pairwise irrational differences. -/
theorem irrationalShifts_exist (n : ℕ) :
    ∃ α : Fin n → ℝ, Pairwise fun j k : Fin n => Irrational (α j - α k) := by
  refine ⟨fun j => (j : ℚ) * Real.sqrt 2, ?_⟩
  intro j k hjk
  have hq : (j : ℚ) - k ≠ 0 := by
    exact sub_ne_zero_of_ne (by simpa [Fin.ext_iff] using hjk)
  simpa [sub_mul] using irrational_sqrt_two.ratCast_mul hq

end Fin
end Math
