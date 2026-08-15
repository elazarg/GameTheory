/-
# Zero-sum external regret and empirical saddle gaps

In a two-player zero-sum matrix game, the correlated payoff of a learning
trace cancels when the two players' external regrets are added. What remains
is exactly the saddle deviation gap of the trace's independent empirical
marginals. This module derives that identity from the canonical Core regret,
mixed extension, and approximate-Nash predicate.
-/

import GameTheory.Core.Approximate
import GameTheory.Core.Learning
import GameTheory.Core.MatrixGame

noncomputable section

namespace GameTheory.MatrixGame

open GameTheory GameTheory.Math.Probability

universe u

@[reducible]
def utilityGame {I J : Type u} (A : I → J → ℝ) : UtilityGame (Fin 2) where
  form := form I J
  utility := utility A

/-- The row marginal of an arbitrary finite law over pure matrix profiles. -/
def rowMarginal {I J : Type u}
    (statusQuo : FinDist (Profile (form I J).sig)) : FinDist I :=
  statusQuo.map fun profile => profile 0

/-- The column marginal of an arbitrary finite law over pure matrix profiles. -/
def columnMarginal {I J : Type u}
    (statusQuo : FinDist (Profile (form I J).sig)) : FinDist J :=
  statusQuo.map fun profile => profile 1

/-- With a pure row, matrix expected payoff is expectation over the column
law. -/
theorem expectedPayoff_pure_row {I J : Type u} (A : I → J → ℝ)
    (row : I) (col : FinDist J) :
    expectedPayoff A (FinDist.pure row) col = col.expect (A row) := by
  have hsame : Profile.update (mixedProfile (FinDist.pure row) col) 1 col =
      mixedProfile (FinDist.pure row) col := by
    exact Profile.update_eq_self _ 1
  have hplay :
      (form I J).mixed.play (mixedProfile (FinDist.pure row) col) =
        col.bind fun current =>
          (form I J).mixed.play
            (Profile.update (mixedProfile (FinDist.pure row) col) 1
              (FinDist.pure current)) := by
    rw [← hsame]
    exact GameForm.mixed_play_update (form I J)
      (mixedProfile (FinDist.pure row) col) 1 col
  unfold expectedPayoff
  rw [hplay, expectedUtility_bind]
  apply FinDist.expect_congr
  intro current _
  rw [mixedProfile_update_one]
  have hpure : mixedProfile (FinDist.pure row) (FinDist.pure current) =
      (form I J).purify (pureProfile row current) :=
    mixedProfile_pure row current
  calc
    expectedUtility (utility A) 0
        ((form I J).mixed.play
          (mixedProfile (FinDist.pure row) (FinDist.pure current))) =
      expectedUtility (utility A) 0
        ((form I J).mixed.play
          ((form I J).purify (pureProfile row current))) := by rw [hpure]
    _ = A row current := by
      rw [GameForm.mixed_play_purify, expectedUtility_pure]
      rfl

/-- With a pure column, matrix expected payoff is expectation over the row
law. -/
theorem expectedPayoff_pure_column {I J : Type u} (A : I → J → ℝ)
    (row : FinDist I) (col : J) :
    expectedPayoff A row (FinDist.pure col) =
      row.expect fun current => A current col := by
  have hsame : Profile.update (mixedProfile row (FinDist.pure col)) 0 row =
      mixedProfile row (FinDist.pure col) := by
    exact Profile.update_eq_self _ 0
  have hplay :
      (form I J).mixed.play (mixedProfile row (FinDist.pure col)) =
        row.bind fun current =>
          (form I J).mixed.play
            (Profile.update (mixedProfile row (FinDist.pure col)) 0
              (FinDist.pure current)) := by
    rw [← hsame]
    exact GameForm.mixed_play_update (form I J)
      (mixedProfile row (FinDist.pure col)) 0 row
  unfold expectedPayoff
  rw [hplay, expectedUtility_bind]
  apply FinDist.expect_congr
  intro current _
  rw [mixedProfile_update_zero]
  have hpure : mixedProfile (FinDist.pure current) (FinDist.pure col) =
      (form I J).purify (pureProfile current col) :=
    mixedProfile_pure current col
  calc
    expectedUtility (utility A) 0
        ((form I J).mixed.play
          (mixedProfile (FinDist.pure current) (FinDist.pure col))) =
      expectedUtility (utility A) 0
        ((form I J).mixed.play
          ((form I J).purify (pureProfile current col))) := by rw [hpure]
    _ = A current col := by
      rw [GameForm.mixed_play_purify, expectedUtility_pure]
      rfl

/-- Matrix payoff is affine in the row law. -/
theorem expectedPayoff_eq_expect_rows {I J : Type u} (A : I → J → ℝ)
    (row : FinDist I) (col : FinDist J) :
    expectedPayoff A row col =
      row.expect fun current => expectedPayoff A (FinDist.pure current) col := by
  have hsame : Profile.update (mixedProfile row col) 0 row =
      mixedProfile row col := Profile.update_eq_self _ 0
  have hplay :
      (form I J).mixed.play (mixedProfile row col) =
        row.bind fun current =>
          (form I J).mixed.play
            (Profile.update (mixedProfile row col) 0 (FinDist.pure current)) := by
    rw [← hsame]
    exact GameForm.mixed_play_update (form I J) (mixedProfile row col) 0 row
  unfold expectedPayoff
  rw [hplay, expectedUtility_bind]
  apply FinDist.expect_congr
  intro current _
  rw [mixedProfile_update_zero]
  rfl

/-- Matrix payoff is affine in the column law. -/
theorem expectedPayoff_eq_expect_columns {I J : Type u} (A : I → J → ℝ)
    (row : FinDist I) (col : FinDist J) :
    expectedPayoff A row col =
      col.expect fun current => expectedPayoff A row (FinDist.pure current) := by
  have hsame : Profile.update (mixedProfile row col) 1 col =
      mixedProfile row col := Profile.update_eq_self _ 1
  have hplay :
      (form I J).mixed.play (mixedProfile row col) =
        col.bind fun current =>
          (form I J).mixed.play
            (Profile.update (mixedProfile row col) 1 (FinDist.pure current)) := by
    rw [← hsame]
    exact GameForm.mixed_play_update (form I J) (mixedProfile row col) 1 col
  unfold expectedPayoff
  rw [hplay, expectedUtility_bind]
  apply FinDist.expect_congr
  intro current _
  rw [mixedProfile_update_one]
  rfl

/-- Expected payoff of a separable zero-sum matrix is the difference of the
two marginal expectations. -/
theorem expectedPayoff_sub {I J : Type u} (rowValue : I → ℝ)
    (colValue : J → ℝ) (row : FinDist I) (col : FinDist J) :
    expectedPayoff (fun currentRow currentCol =>
        rowValue currentRow - colValue currentCol) row col =
      row.expect rowValue - col.expect colValue := by
  rw [expectedPayoff_eq_expect_rows]
  simp_rw [expectedPayoff_pure_row, FinDist.expect_sub, FinDist.expect_const]

/-- Row external regret is the fixed row's payoff against the status quo's
column marginal minus the correlated status-quo payoff. -/
theorem externalRegret_zero_eq {I J : Type u} (A : I → J → ℝ)
    (statusQuo : FinDist (Profile (form I J).sig)) (row : I) :
    (utilityGame A).externalRegret statusQuo 0 row =
      expectedPayoff A (FinDist.pure row) (columnMarginal statusQuo) -
        statusQuo.expect fun profile => A (profile 0) (profile 1) := by
  rw [(utilityGame A).externalRegret_eq_expect_gain]
  simp only [utilityGame, expectedUtility_pure, utility_zero]
  have hupdated :
      (fun profile : Profile (form I J).sig =>
        A ((Profile.update profile 0 row) 0)
          ((Profile.update profile 0 row) 1)) =
        fun profile => A row (profile 1) := by
    funext profile
    rw [Profile.update_same,
      Profile.update_of_ne _ _ (by decide : (1 : Fin 2) ≠ 0)]
  rw [FinDist.expect_sub, hupdated, expectedPayoff_pure_row, columnMarginal,
    FinDist.expect_map]

/-- Column external regret is the correlated row payoff minus the fixed
column's payoff against the row marginal. -/
theorem externalRegret_one_eq {I J : Type u} (A : I → J → ℝ)
    (statusQuo : FinDist (Profile (form I J).sig)) (col : J) :
    (utilityGame A).externalRegret statusQuo 1 col =
      statusQuo.expect (fun profile => A (profile 0) (profile 1)) -
        expectedPayoff A (rowMarginal statusQuo) (FinDist.pure col) := by
  rw [(utilityGame A).externalRegret_eq_expect_gain]
  simp only [utilityGame, expectedUtility_pure, utility_one]
  have hupdated :
      (fun profile : Profile (form I J).sig =>
        -A ((Profile.update profile 1 col) 0)
          ((Profile.update profile 1 col) 1)) =
        fun profile => -A (profile 0) col := by
    funext profile
    rw [Profile.update_same,
      Profile.update_of_ne _ _ (by decide : (0 : Fin 2) ≠ 1)]
  rw [FinDist.expect_sub, hupdated, expectedPayoff_pure_column, rowMarginal,
    FinDist.expect_map]
  have hfixed :
      statusQuo.expect (fun profile => -A (profile 0) col) =
        -statusQuo.expect (fun profile => A (profile 0) col) := by
    calc
      statusQuo.expect (fun profile => -A (profile 0) col) =
          statusQuo.expect (fun profile => (-1 : ℝ) * A (profile 0) col) := by
            congr 1
            funext profile
            ring
      _ = (-1 : ℝ) * statusQuo.expect
          (fun profile => A (profile 0) col) := FinDist.expect_smul ..
      _ = _ := by ring
  have hbase :
      statusQuo.expect (fun profile => -A (profile 0) (profile 1)) =
        -statusQuo.expect (fun profile => A (profile 0) (profile 1)) := by
    calc
      statusQuo.expect (fun profile => -A (profile 0) (profile 1)) =
          statusQuo.expect (fun profile =>
            (-1 : ℝ) * A (profile 0) (profile 1)) := by
              congr 1
              funext profile
              ring
      _ = (-1 : ℝ) * statusQuo.expect
          (fun profile => A (profile 0) (profile 1)) := FinDist.expect_smul ..
      _ = _ := by ring
  rw [hfixed, hbase]
  ring

/-- **Zero-sum regret cancellation.** The sum of the two canonical external
regrets is exactly the saddle deviation gap of the independent marginals. -/
theorem saddleGap_eq_externalRegret_add {I J : Type u}
    (A : I → J → ℝ)
    (statusQuo : FinDist (Profile (form I J).sig)) (row : I) (col : J) :
    expectedPayoff A (FinDist.pure row) (columnMarginal statusQuo) -
        expectedPayoff A (rowMarginal statusQuo) (FinDist.pure col) =
      (utilityGame A).externalRegret statusQuo 0 row +
        (utilityGame A).externalRegret statusQuo 1 col := by
  rw [externalRegret_zero_eq, externalRegret_one_eq]
  ring

/-- Uniform external-regret bounds control every pure saddle deviation gap. -/
theorem pureSaddleGap_le_of_externalRegret_le {I J : Type u}
    (A : I → J → ℝ)
    (statusQuo : FinDist (Profile (form I J).sig)) {rowBound colBound : ℝ}
    (hrow : ∀ row, (utilityGame A).externalRegret statusQuo 0 row ≤ rowBound)
    (hcol : ∀ col, (utilityGame A).externalRegret statusQuo 1 col ≤ colBound) :
    ∀ row col,
      expectedPayoff A (FinDist.pure row) (columnMarginal statusQuo) -
          expectedPayoff A (rowMarginal statusQuo) (FinDist.pure col) ≤
        rowBound + colBound := by
  intro row col
  rw [saddleGap_eq_externalRegret_add]
  exact add_le_add (hrow row) (hcol col)

/-- The same bound controls the saddle gap against arbitrary mixed row and
column deviations, by affinity of matrix payoff. -/
theorem mixedSaddleGap_le_of_externalRegret_le {I J : Type u}
    (A : I → J → ℝ)
    (statusQuo : FinDist (Profile (form I J).sig)) {rowBound colBound : ℝ}
    (hrow : ∀ row, (utilityGame A).externalRegret statusQuo 0 row ≤ rowBound)
    (hcol : ∀ col, (utilityGame A).externalRegret statusQuo 1 col ≤ colBound)
    (rowDeviation : FinDist I) (colDeviation : FinDist J) :
    expectedPayoff A rowDeviation (columnMarginal statusQuo) -
        expectedPayoff A (rowMarginal statusQuo) colDeviation ≤
      rowBound + colBound := by
  have hpure := pureSaddleGap_le_of_externalRegret_le A statusQuo hrow hcol
  have hcolAverage : ∀ row,
      expectedPayoff A (FinDist.pure row) (columnMarginal statusQuo) -
          expectedPayoff A (rowMarginal statusQuo) colDeviation ≤
        rowBound + colBound := by
    intro row
    have h := FinDist.expect_mono (μ := colDeviation)
      (u := fun col =>
        expectedPayoff A (FinDist.pure row) (columnMarginal statusQuo) -
          expectedPayoff A (rowMarginal statusQuo) (FinDist.pure col))
      (v := fun _col => rowBound + colBound)
      (fun col _ => hpure row col)
    rw [FinDist.expect_sub, FinDist.expect_const,
      ← expectedPayoff_eq_expect_columns] at h
    simpa only [FinDist.expect_const] using h
  have h := FinDist.expect_mono (μ := rowDeviation)
    (u := fun row =>
      expectedPayoff A (FinDist.pure row) (columnMarginal statusQuo) -
        expectedPayoff A (rowMarginal statusQuo) colDeviation)
    (v := fun _row => rowBound + colBound)
    (fun row _ => hcolAverage row)
  rw [FinDist.expect_sub, FinDist.expect_const,
    ← expectedPayoff_eq_expect_rows] at h
  simpa only [FinDist.expect_const] using h

/-- **No regret implies approximate zero-sum Nash.** The independent marginal
profile of an arbitrary correlated trace is a canonical approximate mixed Nash
profile, with tolerance equal to the sum of the two regret bounds. -/
theorem marginalProfile_isεNash_of_externalRegret_le {I J : Type u}
    (A : I → J → ℝ)
    (statusQuo : FinDist (Profile (form I J).sig)) {rowBound colBound : ℝ}
    (hrow : ∀ row, (utilityGame A).externalRegret statusQuo 0 row ≤ rowBound)
    (hcol : ∀ col, (utilityGame A).externalRegret statusQuo 1 col ≤ colBound) :
    IsεNash (form I J).mixed (utility A) (rowBound + colBound)
      (mixedProfile (rowMarginal statusQuo) (columnMarginal statusQuo)) := by
  rw [isεNash_iff]
  intro who replacement
  rcases (by decide : ∀ player : Fin 2, player = 0 ∨ player = 1) who with rfl | rfl
  · rw [mixedProfile_update_zero, expectedUtility_zero_mixedProfile,
      expectedUtility_zero_mixedProfile]
    have hgap := mixedSaddleGap_le_of_externalRegret_le A statusQuo hrow hcol
      replacement (columnMarginal statusQuo)
    linarith
  · rw [mixedProfile_update_one, expectedUtility_one_mixedProfile,
      expectedUtility_one_mixedProfile]
    have hgap := mixedSaddleGap_le_of_externalRegret_le A statusQuo hrow hcol
      (rowMarginal statusQuo) replacement
    linarith

end GameTheory.MatrixGame
