/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ProbabilityMassFunction.Simplex
import Mathlib.Topology.Order.Lattice

/-!
# Rectangular zero-sum matrix games

This file provides the common finite-dimensional layer for rectangular
zero-sum matrix games.  A game has a row action type and a possibly different
column action type.  It can be evaluated either on real coordinate vectors or
on finite probability mass functions; the two presentations agree through the
standard-simplex representation of a finite `PMF`.

The finite maximum against a fixed column mixture and finite minimum against a
fixed row mixture are continuous and are attained by simplex vertices.  These
facts are useful independently of a minimax theorem.
-/

noncomputable section

open scoped BigOperators
open Set

namespace GameTheory
namespace MatrixGame

/-- A rectangular zero-sum matrix game, represented by the row player's payoff. -/
abbrev Rectangular (Row : Type u) (Col : Type v) := Row → Col → ℝ

/-- A square matrix game is a rectangular game with the same action type for
both players. -/
abbrev Square (S : Type u) := Rectangular S S

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Bilinear payoff `xᵀ A y` on real coordinate vectors. -/
def bilinearPayoff (A : Rectangular I J) (x : I → ℝ) (y : J → ℝ) : ℝ :=
  ∑ i, x i * ∑ j, A i j * y j

/-- Bilinear payoff restricted to the two mixed-strategy simplices. -/
def simplexPayoff (A : Rectangular I J)
    (row : stdSimplex ℝ I) (col : stdSimplex ℝ J) : ℝ :=
  bilinearPayoff A row col

open Classical in
/-- Expected row-player payoff under independent mixed strategies. -/
noncomputable def expectedPayoff (A : Rectangular I J) (row : PMF I) (col : PMF J) : ℝ :=
  ∑ i, ∑ j, (row i).toReal * (col j).toReal * A i j

open Classical in
/-- Evaluating a rectangular game on `PMF`s agrees with evaluating its bilinear
payoff on their standard-simplex coordinate vectors. -/
theorem expectedPayoff_eq_bilinearPayoff_toVector
    (A : Rectangular I J) (row : PMF I) (col : PMF J) :
    expectedPayoff A row col =
      bilinearPayoff A
        (Math.ProbabilityMassFunction.toVector row)
        (Math.ProbabilityMassFunction.toVector col) := by
  unfold expectedPayoff bilinearPayoff Math.ProbabilityMassFunction.toVector
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The `PMF` and standard-simplex presentations of mixed payoff agree under
the canonical equivalences. -/
theorem expectedPayoff_eq_simplexPayoff
    (A : Rectangular I J) (row : PMF I) (col : PMF J) :
    expectedPayoff A row col =
      simplexPayoff A
        (Math.ProbabilityMassFunction.stdSimplexEquiv row)
        (Math.ProbabilityMassFunction.stdSimplexEquiv col) := by
  simpa [simplexPayoff] using expectedPayoff_eq_bilinearPayoff_toVector A row col

/-- Payoff of a pure row against a column vector. -/
def rowPayoff (A : Rectangular I J) (i : I) (y : J → ℝ) : ℝ :=
  ∑ j, A i j * y j

/-- Payoff of a row vector against a pure column. -/
def columnPayoff (A : Rectangular I J) (x : I → ℝ) (j : J) : ℝ :=
  ∑ i, x i * A i j

/-- Expand a bilinear payoff as a row-weighted sum. -/
theorem bilinearPayoff_eq_sum_rowPayoff
    (A : Rectangular I J) (x : I → ℝ) (y : J → ℝ) :
    bilinearPayoff A x y = ∑ i, x i * rowPayoff A i y :=
  rfl

open Classical in
/-- Expand a bilinear payoff as a column-weighted sum. -/
theorem bilinearPayoff_eq_sum_columnPayoff
    (A : Rectangular I J) (x : I → ℝ) (y : J → ℝ) :
    bilinearPayoff A x y = ∑ j, y j * columnPayoff A x j := by
  unfold bilinearPayoff columnPayoff
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The bilinear payoff is continuous in the row vector. -/
theorem continuous_bilinearPayoff_left (A : Rectangular I J) (y : J → ℝ) :
    Continuous fun x => bilinearPayoff A x y := by
  unfold bilinearPayoff
  fun_prop

/-- The bilinear payoff is continuous in the column vector. -/
theorem continuous_bilinearPayoff_right (A : Rectangular I J) (x : I → ℝ) :
    Continuous fun y => bilinearPayoff A x y := by
  unfold bilinearPayoff
  fun_prop

section PureStrategies

open Classical in
/-- Expected payoff when the row player uses a pure strategy. -/
theorem expectedPayoff_pure_row (A : Rectangular I J) (i : I) (col : PMF J) :
    expectedPayoff A (PMF.pure i) col =
      ∑ j : J, (col j).toReal * A i j := by
  unfold expectedPayoff
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [PMF.pure_apply, hki]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

open Classical in
/-- Expected payoff when the column player uses a pure strategy. -/
theorem expectedPayoff_pure_col (A : Rectangular I J) (row : PMF I) (j : J) :
    expectedPayoff A row (PMF.pure j) =
      ∑ i : I, (row i).toReal * A i j := by
  unfold expectedPayoff
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [PMF.pure_apply, hkj]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

end PureStrategies

section RowMaximum

variable [Nonempty I]

/-- Maximum payoff of a pure row against a fixed column vector. -/
def maxRowPayoff (A : Rectangular I J) (y : J → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => rowPayoff A i y

/-- Every pure-row payoff is bounded by `maxRowPayoff`. -/
theorem rowPayoff_le_maxRowPayoff (A : Rectangular I J) (i : I) (y : J → ℝ) :
    rowPayoff A i y ≤ maxRowPayoff A y :=
  Finset.le_sup' (fun i => rowPayoff A i y) (Finset.mem_univ i)

/-- A simplex-weighted row payoff is bounded by the largest pure-row payoff. -/
theorem bilinearPayoff_le_maxRowPayoff
    (A : Rectangular I J) {x : I → ℝ} {y : J → ℝ}
    (hx : x ∈ stdSimplex ℝ I) : bilinearPayoff A x y ≤ maxRowPayoff A y := by
  calc
    bilinearPayoff A x y ≤ ∑ i, x i * maxRowPayoff A y := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (rowPayoff_le_maxRowPayoff A i y) (hx.1 i)
    _ = maxRowPayoff A y := by rw [← Finset.sum_mul, hx.2, one_mul]

open Classical in
/-- A pure row, viewed as a simplex vertex, attains `maxRowPayoff`. -/
theorem exists_bilinearPayoff_eq_maxRowPayoff
    (A : Rectangular I J) (y : J → ℝ) :
    ∃ x ∈ stdSimplex ℝ I, bilinearPayoff A x y = maxRowPayoff A y := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => rowPayoff A i y)
  refine ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, ?_⟩
  rw [bilinearPayoff, Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, one_mul]
    exact hi.symm
  · intro k _ hki
    rw [Pi.single_eq_of_ne hki, zero_mul]
  · simp

open Classical in
/-- The maximum pure-row payoff is continuous in the column vector. -/
theorem continuous_maxRowPayoff (A : Rectangular I J) : Continuous (maxRowPayoff A) := by
  unfold maxRowPayoff rowPayoff
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro i _
  fun_prop

end RowMaximum

section ColumnMinimum

variable [Nonempty J]

/-- Minimum payoff against a pure column for a fixed row vector. -/
def minColumnPayoff (A : Rectangular I J) (x : I → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun j => columnPayoff A x j

/-- `minColumnPayoff` is bounded by every pure-column payoff. -/
theorem minColumnPayoff_le_columnPayoff
    (A : Rectangular I J) (x : I → ℝ) (j : J) :
    minColumnPayoff A x ≤ columnPayoff A x j :=
  Finset.inf'_le (fun j => columnPayoff A x j) (Finset.mem_univ j)

/-- The smallest pure-column payoff bounds a simplex-weighted column payoff. -/
theorem minColumnPayoff_le_bilinearPayoff
    (A : Rectangular I J) {x : I → ℝ} {y : J → ℝ}
    (hy : y ∈ stdSimplex ℝ J) : minColumnPayoff A x ≤ bilinearPayoff A x y := by
  rw [bilinearPayoff_eq_sum_columnPayoff]
  calc
    minColumnPayoff A x = ∑ j, y j * minColumnPayoff A x := by
      rw [← Finset.sum_mul, hy.2, one_mul]
    _ ≤ ∑ j, y j * columnPayoff A x j := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (minColumnPayoff_le_columnPayoff A x j) (hy.1 j)

open Classical in
/-- A pure column, viewed as a simplex vertex, attains `minColumnPayoff`. -/
theorem exists_bilinearPayoff_eq_minColumnPayoff
    (A : Rectangular I J) (x : I → ℝ) :
    ∃ y ∈ stdSimplex ℝ J, bilinearPayoff A x y = minColumnPayoff A x := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun j => columnPayoff A x j)
  refine ⟨Pi.single j 1, single_mem_stdSimplex ℝ j, ?_⟩
  rw [bilinearPayoff_eq_sum_columnPayoff, Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same, one_mul]
    exact hj.symm
  · intro k _ hkj
    rw [Pi.single_eq_of_ne hkj, zero_mul]
  · simp

open Classical in
/-- The minimum pure-column payoff is continuous in the row vector. -/
theorem continuous_minColumnPayoff (A : Rectangular I J) :
    Continuous (minColumnPayoff A) := by
  unfold minColumnPayoff columnPayoff
  apply Continuous.finset_inf'_apply Finset.univ_nonempty
  intro j _
  fun_prop

end ColumnMinimum

end MatrixGame
end GameTheory
