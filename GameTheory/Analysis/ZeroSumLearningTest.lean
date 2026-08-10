/-
# Hostile checks for zero-sum no-regret learning

The positive control has a strictly positive saddle gap.  The cancellation
control deliberately uses a correlated trace: its empirical joint law is not
the product of its marginals, and the players' signed regrets cancel to yield
an exact Nash equilibrium of those marginals.
-/

import GameTheory.Analysis.ZeroSumLearning

noncomputable section

namespace GameTheory.MatrixGame.ZeroSumLearningTest

open GameTheory Probability

def matchingPayoff (row col : Bool) : ℝ :=
  if row = col then 1 else -1

def bothFalse : Profile (form Bool Bool).sig :=
  pureProfile false false

def bothTrue : Profile (form Bool Bool).sig :=
  pureProfile true true

/-- A perfectly correlated empirical trace with fair row and column
marginals. -/
def diagonalLaw : FinDist (Profile (form Bool Bool).sig) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure bothFalse) (FinDist.pure bothTrue)

/-- A pure trace at a non-saddle action profile. -/
def mismatchedLaw : FinDist (Profile (form Bool Bool).sig) :=
  FinDist.pure (pureProfile false true)

theorem diagonal_row_regret (row : Bool) :
    (utilityGame matchingPayoff).externalRegret diagonalLaw 0 row = -1 := by
  rw [externalRegret_zero_eq, expectedPayoff_pure_row]
  simp [columnMarginal, diagonalLaw, bothFalse, bothTrue, matchingPayoff,
    FinDist.expect_mix]
  cases row <;> norm_num

theorem diagonal_column_regret (col : Bool) :
    (utilityGame matchingPayoff).externalRegret diagonalLaw 1 col = 1 := by
  rw [externalRegret_one_eq, expectedPayoff_pure_column]
  simp [rowMarginal, diagonalLaw, bothFalse, bothTrue, matchingPayoff,
    FinDist.expect_mix]
  cases col <;> norm_num

/-- The generic theorem consumes signed canonical regrets.  It therefore sees
the useful zero-sum cancellation `-1 + 1 = 0`, rather than discarding the
negative row regret with a positive-part operation. -/
theorem diagonal_marginals_are_nash :
    IsNash (form Bool Bool).mixed (euPreference (utility matchingPayoff))
      (mixedProfile (rowMarginal diagonalLaw) (columnMarginal diagonalLaw)) := by
  rw [isNash_iff_isεNash_zero]
  simpa using marginalProfile_isεNash_of_externalRegret_le matchingPayoff
    diagonalLaw (rowBound := -1) (colBound := 1)
      (fun row => le_of_eq (diagonal_row_regret row))
      (fun col => le_of_eq (diagonal_column_regret col))

theorem mismatched_row_regret_positive :
    (utilityGame matchingPayoff).externalRegret mismatchedLaw 0 true = 2 := by
  rw [externalRegret_zero_eq, expectedPayoff_pure_row]
  norm_num [columnMarginal, mismatchedLaw, matchingPayoff]

theorem mismatched_column_regret_zero :
    (utilityGame matchingPayoff).externalRegret mismatchedLaw 1 true = 0 := by
  rw [externalRegret_one_eq, expectedPayoff_pure_column]
  norm_num [rowMarginal, mismatchedLaw, matchingPayoff]

/-- Positive control: the saddle-gap identity is non-vacuous and returns the
exact gap `2` at the mismatched pure trace. -/
theorem mismatched_saddle_gap_eq_two :
    expectedPayoff matchingPayoff (FinDist.pure true)
          (columnMarginal mismatchedLaw) -
        expectedPayoff matchingPayoff (rowMarginal mismatchedLaw)
          (FinDist.pure true) = 2 := by
  rw [saddleGap_eq_externalRegret_add]
  rw [mismatched_row_regret_positive, mismatched_column_regret_zero]
  norm_num

/-- The pure gap bound is consumed separately from the Nash wrapper, so the
underlying quantitative certificate remains usable by minimax clients. -/
theorem mismatched_saddle_gap_le_two :
    ∀ row col,
      expectedPayoff matchingPayoff (FinDist.pure row)
            (columnMarginal mismatchedLaw) -
          expectedPayoff matchingPayoff (rowMarginal mismatchedLaw)
            (FinDist.pure col) ≤ 2 := by
  have hrow : ∀ row,
      (utilityGame matchingPayoff).externalRegret mismatchedLaw 0 row ≤ 2 := by
    intro row
    rw [externalRegret_zero_eq, expectedPayoff_pure_row]
    cases row <;> norm_num [columnMarginal, mismatchedLaw, matchingPayoff]
  have hcol : ∀ col,
      (utilityGame matchingPayoff).externalRegret mismatchedLaw 1 col ≤ 0 := by
    intro col
    rw [externalRegret_one_eq, expectedPayoff_pure_column]
    cases col <;> norm_num [rowMarginal, mismatchedLaw, matchingPayoff]
  simpa using pureSaddleGap_le_of_externalRegret_le matchingPayoff
    mismatchedLaw hrow hcol

end GameTheory.MatrixGame.ZeroSumLearningTest
