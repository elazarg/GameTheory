/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.ZeroSum.MatrixGame
import Math.ProbabilityMassFunction.Simplex

/-!
# Geometry of optimal matrix-game strategies

This file identifies optimal mixed strategies for a finite zero-sum matrix game
with their coordinate vectors in the standard simplex.  In those coordinates,
row-optimal and column-optimal strategies are intersections of the simplex with
finitely many closed halfspaces.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace MatrixGame

variable {S : Type}

/-- Payoff of a row-coordinate vector against a pure column. -/
def rowVectorPayoff [Fintype S] (A : Square S) (w : S → ℝ) (y : S) : ℝ :=
  ∑ x : S, w x * A x y

/-- Payoff of a pure row against a column-coordinate vector. -/
def columnVectorPayoff [Fintype S] (A : Square S) (w : S → ℝ) (x : S) : ℝ :=
  ∑ y : S, w y * A x y

section Payoff

variable [Fintype S] (A : Square S)

open Classical in
/-- Rewrite expected payoff as an average over pure-column payoffs. -/
theorem expectedPayoff_eq_sum_rowVectorPayoff (row col : PMF S) :
    expectedPayoff A row col =
      ∑ y : S, (col y).toReal *
        rowVectorPayoff A (Math.ProbabilityMassFunction.toVector row) y := by
  unfold expectedPayoff rowVectorPayoff Math.ProbabilityMassFunction.toVector
  calc
    (∑ x : S, ∑ y : S, (row x).toReal * (col y).toReal * A x y)
        = ∑ y : S, ∑ x : S, (row x).toReal * (col y).toReal * A x y := by
          rw [Finset.sum_comm]
    _ = ∑ y : S, (col y).toReal * ∑ x : S, (row x).toReal * A x y := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring

open Classical in
/-- Rewrite expected payoff as an average over pure-row payoffs. -/
theorem expectedPayoff_eq_sum_columnVectorPayoff (row col : PMF S) :
    expectedPayoff A row col =
      ∑ x : S, (row x).toReal *
        columnVectorPayoff A (Math.ProbabilityMassFunction.toVector col) x := by
  unfold expectedPayoff columnVectorPayoff Math.ProbabilityMassFunction.toVector
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- A row mix guarantees `v` iff every pure column gives payoff at least `v`. -/
theorem rowGuarantees_iff_forall_rowVectorPayoff (row : PMF S) (v : ℝ) :
    RowGuarantees A row v ↔
      ∀ y : S, v ≤ rowVectorPayoff A (Math.ProbabilityMassFunction.toVector row) y := by
  constructor
  · intro h y
    have hpure := h (PMF.pure y)
    rw [expectedPayoff_pure_col] at hpure
    simpa [rowVectorPayoff, Math.ProbabilityMassFunction.toVector]
      using hpure
  · intro h col
    rw [expectedPayoff_eq_sum_rowVectorPayoff]
    calc
      v = ∑ y : S, (col y).toReal * v := by
            rw [← Finset.sum_mul, Math.Probability.pmf_toReal_sum_one, one_mul]
      _ ≤ ∑ y : S, (col y).toReal *
            rowVectorPayoff A (Math.ProbabilityMassFunction.toVector row) y := by
            exact Finset.sum_le_sum fun y _ =>
              mul_le_mul_of_nonneg_left (h y) ENNReal.toReal_nonneg

/-- A column mix caps payoffs by `v` iff every pure row gives payoff at most `v`. -/
theorem columnCaps_iff_forall_columnVectorPayoff (col : PMF S) (v : ℝ) :
    ColumnCaps A col v ↔
      ∀ x : S, columnVectorPayoff A (Math.ProbabilityMassFunction.toVector col) x ≤ v := by
  constructor
  · intro h x
    have hpure := h (PMF.pure x)
    rw [expectedPayoff_pure_row] at hpure
    simpa [columnVectorPayoff, Math.ProbabilityMassFunction.toVector]
      using hpure
  · intro h row
    rw [expectedPayoff_eq_sum_columnVectorPayoff]
    calc
      ∑ x : S, (row x).toReal *
          columnVectorPayoff A (Math.ProbabilityMassFunction.toVector col) x
          ≤ ∑ x : S, (row x).toReal * v := by
            exact Finset.sum_le_sum fun x _ =>
              mul_le_mul_of_nonneg_left (h x) ENNReal.toReal_nonneg
      _ = v := by
            rw [← Finset.sum_mul, Math.Probability.pmf_toReal_sum_one, one_mul]

end Payoff

section OptimalSets

variable [Fintype S] [Nonempty S] (A : Square S)

/-- Coordinate vectors of row-optimal mixed strategies. -/
def optimalRowSet : Set (S → ℝ) :=
  Math.ProbabilityMassFunction.toVector '' optimalRowStrategies A

/-- Coordinate vectors of column-optimal mixed strategies. -/
def optimalColumnSet : Set (S → ℝ) :=
  Math.ProbabilityMassFunction.toVector '' optimalColumnStrategies A

/-- The halfspace description of the row-optimal coordinate set. -/
def optimalRowHalfspaceSet : Set (S → ℝ) :=
  stdSimplex ℝ S ∩ { w | ∀ y : S, value A ≤ rowVectorPayoff A w y }

/-- The halfspace description of the column-optimal coordinate set. -/
def optimalColumnHalfspaceSet : Set (S → ℝ) :=
  stdSimplex ℝ S ∩ { w | ∀ x : S, columnVectorPayoff A w x ≤ value A }

theorem mem_optimalRowSet_iff (w : S → ℝ) :
    w ∈ optimalRowSet A ↔
      w ∈ stdSimplex ℝ S ∧ ∀ y : S, value A ≤ rowVectorPayoff A w y := by
  constructor
  · rintro ⟨row, hrow, rfl⟩
    exact ⟨Math.ProbabilityMassFunction.toVector_mem_stdSimplex row,
      (rowGuarantees_iff_forall_rowVectorPayoff (A := A) row (value A)).1 hrow⟩
  · rintro ⟨hw, hpay⟩
    let row := Math.ProbabilityMassFunction.ofVector w hw
    refine ⟨row, ?_, ?_⟩
    · have hvec : Math.ProbabilityMassFunction.toVector row = w := by
        exact Math.ProbabilityMassFunction.toVector_ofVector hw
      exact (rowGuarantees_iff_forall_rowVectorPayoff (A := A) row (value A)).2 (by
        simpa [hvec] using hpay)
    · exact Math.ProbabilityMassFunction.toVector_ofVector hw

theorem optimalRowSet_eq_halfspaceSet :
    optimalRowSet A = optimalRowHalfspaceSet A := by
  ext w
  exact mem_optimalRowSet_iff (A := A) w

theorem mem_optimalColumnSet_iff (w : S → ℝ) :
    w ∈ optimalColumnSet A ↔
      w ∈ stdSimplex ℝ S ∧ ∀ x : S, columnVectorPayoff A w x ≤ value A := by
  constructor
  · rintro ⟨col, hcol, rfl⟩
    exact ⟨Math.ProbabilityMassFunction.toVector_mem_stdSimplex col,
      (columnCaps_iff_forall_columnVectorPayoff (A := A) col (value A)).1 hcol⟩
  · rintro ⟨hw, hpay⟩
    let col := Math.ProbabilityMassFunction.ofVector w hw
    refine ⟨col, ?_, ?_⟩
    · have hvec : Math.ProbabilityMassFunction.toVector col = w := by
        exact Math.ProbabilityMassFunction.toVector_ofVector hw
      exact (columnCaps_iff_forall_columnVectorPayoff (A := A) col (value A)).2 (by
        simpa [hvec] using hpay)
    · exact Math.ProbabilityMassFunction.toVector_ofVector hw

theorem optimalColumnSet_eq_halfspaceSet :
    optimalColumnSet A = optimalColumnHalfspaceSet A := by
  ext w
  exact mem_optimalColumnSet_iff (A := A) w

theorem optimalRowSet_subset_stdSimplex :
    optimalRowSet A ⊆ stdSimplex ℝ S := by
  intro w hw
  exact (mem_optimalRowSet_iff (A := A) w).1 hw |>.1

theorem optimalColumnSet_subset_stdSimplex :
    optimalColumnSet A ⊆ stdSimplex ℝ S := by
  intro w hw
  exact (mem_optimalColumnSet_iff (A := A) w).1 hw |>.1

theorem optimalRowSet_convex :
    Convex ℝ (optimalRowSet A) := by
  rw [optimalRowSet_eq_halfspaceSet]
  intro u hu v hv a b ha hb hab
  rcases hu with ⟨huS, hu⟩
  rcases hv with ⟨hvS, hv⟩
  constructor
  · exact (convex_stdSimplex ℝ S) huS hvS ha hb hab
  · intro y
    have hlinear :
        rowVectorPayoff A (a • u + b • v) y =
          a * rowVectorPayoff A u y + b * rowVectorPayoff A v y := by
      unfold rowVectorPayoff
      calc
        (∑ x : S, (a • u + b • v) x * A x y)
            = ∑ x : S, (a * (u x * A x y) + b * (v x * A x y)) := by
              apply Finset.sum_congr rfl
              intro x _
              simp [Pi.add_apply, Pi.smul_apply]
              ring
        _ = (∑ x : S, a * (u x * A x y)) +
              ∑ x : S, b * (v x * A x y) := by
              rw [Finset.sum_add_distrib]
        _ = a * (∑ x : S, u x * A x y) +
              b * (∑ x : S, v x * A x y) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [hlinear]
    calc
      value A = (a + b) * value A := by rw [hab, one_mul]
      _ = a * value A + b * value A := by ring
      _ ≤ a * rowVectorPayoff A u y + b * rowVectorPayoff A v y := by
            exact add_le_add (mul_le_mul_of_nonneg_left (hu y) ha)
              (mul_le_mul_of_nonneg_left (hv y) hb)

theorem optimalColumnSet_convex :
    Convex ℝ (optimalColumnSet A) := by
  rw [optimalColumnSet_eq_halfspaceSet]
  intro u hu v hv a b ha hb hab
  rcases hu with ⟨huS, hu⟩
  rcases hv with ⟨hvS, hv⟩
  constructor
  · exact (convex_stdSimplex ℝ S) huS hvS ha hb hab
  · intro x
    have hlinear :
        columnVectorPayoff A (a • u + b • v) x =
          a * columnVectorPayoff A u x + b * columnVectorPayoff A v x := by
      unfold columnVectorPayoff
      calc
        (∑ y : S, (a • u + b • v) y * A x y)
            = ∑ y : S, (a * (u y * A x y) + b * (v y * A x y)) := by
              apply Finset.sum_congr rfl
              intro y _
              simp [Pi.add_apply, Pi.smul_apply]
              ring
        _ = (∑ y : S, a * (u y * A x y)) +
              ∑ y : S, b * (v y * A x y) := by
              rw [Finset.sum_add_distrib]
        _ = a * (∑ y : S, u y * A x y) +
              b * (∑ y : S, v y * A x y) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [hlinear]
    calc
      a * columnVectorPayoff A u x + b * columnVectorPayoff A v x
          ≤ a * value A + b * value A := by
            exact add_le_add (mul_le_mul_of_nonneg_left (hu x) ha)
              (mul_le_mul_of_nonneg_left (hv x) hb)
      _ = (a + b) * value A := by ring
      _ = value A := by rw [hab, one_mul]

omit [Nonempty S] in
theorem continuous_rowVectorPayoff (y : S) :
    Continuous fun w : S → ℝ => rowVectorPayoff A w y := by
  unfold rowVectorPayoff
  exact continuous_finsetSum (Finset.univ : Finset S)
    (fun x _ => (continuous_apply x).mul continuous_const)

omit [Nonempty S] in
theorem continuous_columnVectorPayoff (x : S) :
    Continuous fun w : S → ℝ => columnVectorPayoff A w x := by
  unfold columnVectorPayoff
  exact continuous_finsetSum (Finset.univ : Finset S)
    (fun y _ => (continuous_apply y).mul continuous_const)

theorem optimalRowSet_isClosed :
    IsClosed (optimalRowSet A) := by
  rw [optimalRowSet_eq_halfspaceSet]
  refine (isClosed_stdSimplex ℝ S).inter ?_
  have hclosed : IsClosed (⋂ y : S, { w : S → ℝ | value A ≤ rowVectorPayoff A w y }) :=
    isClosed_iInter fun y : S =>
      isClosed_le (f := fun _ : S → ℝ => value A)
        (g := fun w : S → ℝ => rowVectorPayoff A w y)
        continuous_const (continuous_rowVectorPayoff (A := A) y)
  convert hclosed using 1
  ext w
  simp [Set.mem_iInter]

theorem optimalColumnSet_isClosed :
    IsClosed (optimalColumnSet A) := by
  rw [optimalColumnSet_eq_halfspaceSet]
  refine (isClosed_stdSimplex ℝ S).inter ?_
  have hclosed : IsClosed (⋂ x : S, { w : S → ℝ | columnVectorPayoff A w x ≤ value A }) :=
    isClosed_iInter fun x : S =>
      isClosed_le (f := fun w : S → ℝ => columnVectorPayoff A w x)
        (g := fun _ : S → ℝ => value A)
        (continuous_columnVectorPayoff (A := A) x) continuous_const
  convert hclosed using 1
  ext w
  simp [Set.mem_iInter]

theorem optimalRowSet_isCompact :
    IsCompact (optimalRowSet A) := by
  exact (isCompact_stdSimplex ℝ S).of_isClosed_subset
    (optimalRowSet_isClosed (A := A)) (optimalRowSet_subset_stdSimplex (A := A))

theorem optimalColumnSet_isCompact :
    IsCompact (optimalColumnSet A) := by
  exact (isCompact_stdSimplex ℝ S).of_isClosed_subset
    (optimalColumnSet_isClosed (A := A)) (optimalColumnSet_subset_stdSimplex (A := A))

theorem optimalRowSet_image_nonempty :
    (optimalRowSet A).Nonempty := by
  obtain ⟨row, hrow⟩ := optimalRowStrategies_nonempty A
  exact ⟨Math.ProbabilityMassFunction.toVector row, ⟨row, hrow, rfl⟩⟩

theorem optimalColumnSet_image_nonempty :
    (optimalColumnSet A).Nonempty := by
  obtain ⟨col, hcol⟩ := optimalColumnStrategies_nonempty A
  exact ⟨Math.ProbabilityMassFunction.toVector col, ⟨col, hcol, rfl⟩⟩

/-- Coordinate row-optimal strategies form a nonempty compact convex subset of
the ambient finite-dimensional simplex. -/
theorem optimalRowSet_geometry :
    Convex ℝ (optimalRowSet A) ∧ IsClosed (optimalRowSet A) ∧
      IsCompact (optimalRowSet A) ∧ (optimalRowSet A).Nonempty :=
  ⟨optimalRowSet_convex A, optimalRowSet_isClosed A, optimalRowSet_isCompact A,
    optimalRowSet_image_nonempty A⟩

/-- Coordinate column-optimal strategies form a nonempty compact convex subset
of the ambient finite-dimensional simplex. -/
theorem optimalColumnSet_geometry :
    Convex ℝ (optimalColumnSet A) ∧ IsClosed (optimalColumnSet A) ∧
      IsCompact (optimalColumnSet A) ∧ (optimalColumnSet A).Nonempty :=
  ⟨optimalColumnSet_convex A, optimalColumnSet_isClosed A, optimalColumnSet_isCompact A,
    optimalColumnSet_image_nonempty A⟩

end OptimalSets

end MatrixGame

end GameTheory
