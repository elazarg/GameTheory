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

open GameTheory GameTheory.Math.Probability

private instance (i : Fin 2) : Fintype ((form Bool Bool).sig.Strategy i) := by
  cases i using Fin.cases with
  | zero => exact inferInstance
  | succ j =>
    cases j using Fin.cases with
    | zero => exact (inferInstance : Fintype Bool)
    | succ k => exact k.elim0

def matchingPayoff (row col : Bool) : ℝ :=
  if row = col then 1 else -1

def bothFalse : Profile (form Bool Bool).sig := pureProfile false false
def bothTrue : Profile (form Bool Bool).sig := pureProfile true true

def diagonalLaw : PMF (Profile (form Bool Bool).sig) :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure bothFalse) (PMF.pure bothTrue)

def mismatchedLaw : PMF (Profile (form Bool Bool).sig) :=
  PMF.pure (pureProfile false true)

/-- The finite joint profile law has an integrable matching payoff. -/
theorem finiteBase (law : PMF (Profile (form Bool Bool).sig)) :
    PayoffIntegrable law
      (fun profile => matchingPayoff (profile 0) (profile 1)) :=
  payoffIntegrable_of_finite _ _

/-- Fixing the row preserves payoff integrability under the column marginal. -/
theorem finiteRow (law : PMF (Profile (form Bool Bool).sig)) (row : Bool) :
    PayoffIntegrable (columnMarginal law) (matchingPayoff row) :=
  payoffIntegrable_of_finite _ _

/-- Fixing the column preserves payoff integrability under the row marginal. -/
theorem finiteColumn (law : PMF (Profile (form Bool Bool).sig)) (col : Bool) :
    PayoffIntegrable (rowMarginal law) (fun row => matchingPayoff row col) :=
  payoffIntegrable_of_finite _ _

private theorem finiteMixed (row col : PMF Bool) :
    UtilityIntegrable (utility matchingPayoff) 0
      ((form Bool Bool).mixed.play (mixedProfile row col)) :=
  payoffIntegrable_of_finite _ _

private theorem expect_half_pure {α : Type*} [Finite α]
    (first second : α) (f : α → ℝ) :
    expect (mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure first) (PMF.pure second)) f
      (payoffIntegrable_of_finite _ _) = (f first + f second) / 2 := by
  let hfirst := payoffIntegrable_pure first f
  let hsecond := payoffIntegrable_pure second f
  calc
    _ = expect (mix (1 / 2) (by norm_num) (by norm_num)
          (PMF.pure first) (PMF.pure second)) f
          (payoffIntegrable_mix (1 / 2) (by norm_num) (by norm_num)
            (PMF.pure first) (PMF.pure second) f hfirst hsecond) :=
      expect_proof_irrel _ _ _ _
    _ = (f first + f second) / 2 := by
      rw [expect_mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure first) (PMF.pure second) f hfirst hsecond,
        expect_pure, expect_pure]
      ring

private theorem diagonal_rowMarginal :
    rowMarginal diagonalLaw =
      mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure false) (PMF.pure true) := by
  simp only [rowMarginal, diagonalLaw, mix_map, PMF.pure_map]
  rfl

private theorem diagonal_columnMarginal :
    columnMarginal diagonalLaw =
      mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure false) (PMF.pure true) := by
  simp only [columnMarginal, diagonalLaw, mix_map, PMF.pure_map]
  rfl

private theorem diagonal_expect (f : Profile (form Bool Bool).sig → ℝ) :
    expect diagonalLaw f (payoffIntegrable_of_finite _ _) =
      (f bothFalse + f bothTrue) / 2 :=
  expect_half_pure bothFalse bothTrue f

private theorem diagonal_row_expect (f : Bool → ℝ) :
    expect (rowMarginal diagonalLaw) f (payoffIntegrable_of_finite _ _) =
      (f false + f true) / 2 := by
  calc
    _ = expect (mix (1 / 2) (by norm_num) (by norm_num)
          (PMF.pure false) (PMF.pure true)) f
          (payoffIntegrable_of_finite _ _) :=
      expect_congr_law diagonal_rowMarginal f _ _
    _ = _ := expect_half_pure false true f

private theorem diagonal_column_expect (f : Bool → ℝ) :
    expect (columnMarginal diagonalLaw) f (payoffIntegrable_of_finite _ _) =
      (f false + f true) / 2 := by
  calc
    _ = expect (mix (1 / 2) (by norm_num) (by norm_num)
          (PMF.pure false) (PMF.pure true)) f
          (payoffIntegrable_of_finite _ _) :=
      expect_congr_law diagonal_columnMarginal f _ _
    _ = _ := expect_half_pure false true f

theorem diagonal_row_regret (row : Bool) :
    (utilityGame matchingPayoff).externalRegret diagonalLaw 0 row
      (correlatedIntegrable_zero matchingPayoff diagonalLaw
        (finiteBase diagonalLaw))
      (rowReplacementIntegrable matchingPayoff diagonalLaw row
        (finiteRow diagonalLaw row)) = -1 := by
  rw [externalRegret_zero_eq matchingPayoff diagonalLaw row
    (finiteBase diagonalLaw) (finiteRow diagonalLaw row),
    expectedPayoff_pure_row matchingPayoff row
      (columnMarginal diagonalLaw) (finiteRow diagonalLaw row),
    diagonal_column_expect, diagonal_expect]
  cases row <;> norm_num [matchingPayoff, bothFalse, bothTrue, pureProfile]

theorem diagonal_column_regret (col : Bool) :
    (utilityGame matchingPayoff).externalRegret diagonalLaw 1 col
      (correlatedIntegrable_one matchingPayoff diagonalLaw
        (finiteBase diagonalLaw))
      (columnReplacementIntegrable matchingPayoff diagonalLaw col
        (finiteColumn diagonalLaw col)) = 1 := by
  rw [externalRegret_one_eq matchingPayoff diagonalLaw col
    (finiteBase diagonalLaw) (finiteColumn diagonalLaw col),
    expectedPayoff_pure_column matchingPayoff
      (rowMarginal diagonalLaw) col (finiteColumn diagonalLaw col),
    diagonal_row_expect, diagonal_expect]
  cases col <;> norm_num [matchingPayoff, bothFalse, bothTrue, pureProfile]
theorem diagonal_marginals_are_nash :
    IsNash (form Bool Bool).mixed (euPreference (utility matchingPayoff))
      (mixedProfile (rowMarginal diagonalLaw) (columnMarginal diagonalLaw)) := by
  rw [isNash_iff_isεNash_zero]
  have hrow : ∀ row,
      (utilityGame matchingPayoff).externalRegret diagonalLaw 0 row
        (correlatedIntegrable_zero matchingPayoff diagonalLaw
          (finiteBase diagonalLaw))
        (rowReplacementIntegrable matchingPayoff diagonalLaw row
          (finiteRow diagonalLaw row)) ≤ -1 := by
    intro row
    rw [diagonal_row_regret]
  have hcol : ∀ col,
      (utilityGame matchingPayoff).externalRegret diagonalLaw 1 col
        (correlatedIntegrable_one matchingPayoff diagonalLaw
          (finiteBase diagonalLaw))
        (columnReplacementIntegrable matchingPayoff diagonalLaw col
          (finiteColumn diagonalLaw col)) ≤ 1 := by
    intro col
    rw [diagonal_column_regret]
  simpa using marginalProfile_isεNash_of_externalRegret_le
    matchingPayoff diagonalLaw (rowBound := -1) (colBound := 1)
    (finiteBase diagonalLaw) (finiteRow diagonalLaw)
    (finiteColumn diagonalLaw) hrow hcol
    (fun replacement => finiteMixed replacement (columnMarginal diagonalLaw))
    (fun replacement => finiteMixed (rowMarginal diagonalLaw) replacement)

theorem mismatched_row_regret_positive :
    (utilityGame matchingPayoff).externalRegret mismatchedLaw 0 true
      (correlatedIntegrable_zero matchingPayoff mismatchedLaw
        (finiteBase mismatchedLaw))
      (rowReplacementIntegrable matchingPayoff mismatchedLaw true
        (finiteRow mismatchedLaw true)) = 2 := by
  rw [externalRegret_zero_eq matchingPayoff mismatchedLaw true
    (finiteBase mismatchedLaw) (finiteRow mismatchedLaw true),
    expectedPayoff_pure_row matchingPayoff true
      (columnMarginal mismatchedLaw) (finiteRow mismatchedLaw true)]
  norm_num [columnMarginal, mismatchedLaw, matchingPayoff,
    PMF.pure_map, expect_pure]

theorem mismatched_column_regret_zero :
    (utilityGame matchingPayoff).externalRegret mismatchedLaw 1 true
      (correlatedIntegrable_one matchingPayoff mismatchedLaw
        (finiteBase mismatchedLaw))
      (columnReplacementIntegrable matchingPayoff mismatchedLaw true
        (finiteColumn mismatchedLaw true)) = 0 := by
  rw [externalRegret_one_eq matchingPayoff mismatchedLaw true
    (finiteBase mismatchedLaw) (finiteColumn mismatchedLaw true),
    expectedPayoff_pure_column matchingPayoff
      (rowMarginal mismatchedLaw) true (finiteColumn mismatchedLaw true)]
  norm_num [rowMarginal, mismatchedLaw, matchingPayoff,
    PMF.pure_map, expect_pure]
/-- The non-saddle trace has exact positive gap two. -/
theorem mismatched_saddle_gap_eq_two :
    expectedPayoff matchingPayoff (PMF.pure true)
          (columnMarginal mismatchedLaw)
          (integrable_pure_row matchingPayoff true
            (columnMarginal mismatchedLaw) (finiteRow mismatchedLaw true)) -
        expectedPayoff matchingPayoff (rowMarginal mismatchedLaw)
          (PMF.pure true)
          (integrable_pure_column matchingPayoff
            (rowMarginal mismatchedLaw) true (finiteColumn mismatchedLaw true)) = 2 := by
  rw [saddleGap_eq_externalRegret_add matchingPayoff mismatchedLaw true true
    (finiteBase mismatchedLaw) (finiteRow mismatchedLaw true)
    (finiteColumn mismatchedLaw true)]
  rw [mismatched_row_regret_positive, mismatched_column_regret_zero]
  norm_num

/-- The pure quantitative certificate remains usable without Nash packaging. -/
theorem mismatched_saddle_gap_le_two :
    ∀ row col,
      expectedPayoff matchingPayoff (PMF.pure row)
            (columnMarginal mismatchedLaw)
            (integrable_pure_row matchingPayoff row
              (columnMarginal mismatchedLaw) (finiteRow mismatchedLaw row)) -
          expectedPayoff matchingPayoff (rowMarginal mismatchedLaw)
            (PMF.pure col)
            (integrable_pure_column matchingPayoff
              (rowMarginal mismatchedLaw) col (finiteColumn mismatchedLaw col)) ≤
        2 := by
  have hrow : ∀ row,
      (utilityGame matchingPayoff).externalRegret mismatchedLaw 0 row
        (correlatedIntegrable_zero matchingPayoff mismatchedLaw
          (finiteBase mismatchedLaw))
        (rowReplacementIntegrable matchingPayoff mismatchedLaw row
          (finiteRow mismatchedLaw row)) ≤ 2 := by
    intro row
    rw [externalRegret_zero_eq matchingPayoff mismatchedLaw row
      (finiteBase mismatchedLaw) (finiteRow mismatchedLaw row),
      expectedPayoff_pure_row matchingPayoff row
        (columnMarginal mismatchedLaw) (finiteRow mismatchedLaw row)]
    cases row <;> norm_num [columnMarginal, mismatchedLaw, matchingPayoff,
      PMF.pure_map, expect_pure]
  have hcol : ∀ col,
      (utilityGame matchingPayoff).externalRegret mismatchedLaw 1 col
        (correlatedIntegrable_one matchingPayoff mismatchedLaw
          (finiteBase mismatchedLaw))
        (columnReplacementIntegrable matchingPayoff mismatchedLaw col
          (finiteColumn mismatchedLaw col)) ≤ 0 := by
    intro col
    rw [externalRegret_one_eq matchingPayoff mismatchedLaw col
      (finiteBase mismatchedLaw) (finiteColumn mismatchedLaw col),
      expectedPayoff_pure_column matchingPayoff
        (rowMarginal mismatchedLaw) col (finiteColumn mismatchedLaw col)]
    cases col <;> norm_num [rowMarginal, mismatchedLaw, matchingPayoff,
      PMF.pure_map, expect_pure]
  simpa using pureSaddleGap_le_of_externalRegret_le matchingPayoff mismatchedLaw
    (rowBound := 2) (colBound := 0) (finiteBase mismatchedLaw)
    (finiteRow mismatchedLaw) (finiteColumn mismatchedLaw) hrow hcol
end GameTheory.MatrixGame.ZeroSumLearningTest
