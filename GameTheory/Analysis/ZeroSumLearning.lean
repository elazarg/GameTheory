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

private theorem correlatedValue_zero {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig))
    (h : PayoffIntegrable statusQuo
      (fun profile => A (profile 0) (profile 1))) :
    expectedUtility (utility A) 0 ((form I J).outcomeLaw statusQuo)
        (correlatedIntegrable_zero A statusQuo h) =
      expect statusQuo (fun profile => A (profile 0) (profile 1)) h := by
  let f : I × J → ℝ := fun outcome => A outcome.1 outcome.2
  let projection : Profile (form I J).sig → I × J :=
    fun profile => (profile 0, profile 1)
  have hmap : PayoffIntegrable (statusQuo.map projection) f :=
    (payoffIntegrable_map_iff projection statusQuo f).2 h
  refine (show expect ((form I J).outcomeLaw statusQuo) f _ = _ from ?_)
  calc
    expect ((form I J).outcomeLaw statusQuo) f _ =
        expect (statusQuo.map projection) f hmap :=
      expect_congr_law (correlatedPlay_eq_map statusQuo) f _ _
    _ = expect statusQuo (f ∘ projection) h :=
      expect_map projection statusQuo f h hmap
private theorem correlatedValue_one {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig))
    (h : PayoffIntegrable statusQuo
      (fun profile => A (profile 0) (profile 1))) :
    expectedUtility (utility A) 1 ((form I J).outcomeLaw statusQuo)
        (correlatedIntegrable_one A statusQuo h) =
      -expect statusQuo (fun profile => A (profile 0) (profile 1)) h := by
  let f : I × J → ℝ := fun outcome => -A outcome.1 outcome.2
  let projection : Profile (form I J).sig → I × J :=
    fun profile => (profile 0, profile 1)
  have hneg : PayoffIntegrable statusQuo (f ∘ projection) := payoffIntegrable_neg h
  have hmap : PayoffIntegrable (statusQuo.map projection) f :=
    (payoffIntegrable_map_iff projection statusQuo f).2 hneg
  refine (show expect ((form I J).outcomeLaw statusQuo) f _ = _ from ?_)
  calc
    expect ((form I J).outcomeLaw statusQuo) f _ =
        expect (statusQuo.map projection) f hmap :=
      expect_congr_law (correlatedPlay_eq_map statusQuo) f _ _
    _ = expect statusQuo (f ∘ projection) hneg :=
      expect_map projection statusQuo f hneg hmap
    _ = -expect statusQuo (fun profile => A (profile 0) (profile 1)) h :=
      expect_neg h

private theorem rowReplacementValue {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig)) (row : I)
    (h : PayoffIntegrable (columnMarginal statusQuo) (A row)) :
    expectedUtility (utility A) 0
        (statusQuo.bind fun profile =>
          (form I J).play (Profile.update profile 0 row))
        (rowReplacementIntegrable A statusQuo row h) =
      expectedPayoff A (PMF.pure row) (columnMarginal statusQuo)
        (integrable_pure_row A row (columnMarginal statusQuo) h) := by
  exact expectedUtility_congr_law (utility A) 0
    ((rowReplacement_eq_map statusQuo row).trans
      (mixed_play_pure_row row (columnMarginal statusQuo)).symm) _ _

private theorem columnReplacementValue {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig)) (col : J)
    (h : PayoffIntegrable (rowMarginal statusQuo)
      (fun row => A row col)) :
    expectedUtility (utility A) 1
        (statusQuo.bind fun profile =>
          (form I J).play (Profile.update profile 1 col))
        (columnReplacementIntegrable A statusQuo col h) =
      -expectedPayoff A (rowMarginal statusQuo) (PMF.pure col)
        (integrable_pure_column A (rowMarginal statusQuo) col h) := by
  let law := (form I J).mixed.play
    (mixedProfile (rowMarginal statusQuo) (PMF.pure col))
  have hzero : UtilityIntegrable (utility A) 0 law :=
    integrable_pure_column A (rowMarginal statusQuo) col h
  have hone : UtilityIntegrable (utility A) 1 law :=
    payoffIntegrable_neg hzero
  calc
    _ = expectedUtility (utility A) 1 law hone :=
      expectedUtility_congr_law (utility A) 1
        ((columnReplacement_eq_map statusQuo col).trans
          (mixed_play_pure_column (rowMarginal statusQuo) col).symm) _ _
    _ = -expectedPayoff A (rowMarginal statusQuo) (PMF.pure col) hzero :=
      expectedUtility_one_mixedProfile A (rowMarginal statusQuo)
        (PMF.pure col) hzero hone
/-- Row regret is the pure-row payoff against the column marginal minus the
correlated incumbent payoff. -/
theorem externalRegret_zero_eq {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig)) (row : I)
    (hbase : PayoffIntegrable statusQuo
      (fun profile => A (profile 0) (profile 1)))
    (hrow : PayoffIntegrable (columnMarginal statusQuo) (A row)) :
    (utilityGame A).externalRegret statusQuo 0 row
        (correlatedIntegrable_zero A statusQuo hbase)
        (rowReplacementIntegrable A statusQuo row hrow) =
      expectedPayoff A (PMF.pure row) (columnMarginal statusQuo)
        (integrable_pure_row A row (columnMarginal statusQuo) hrow) -
        expect statusQuo (fun profile => A (profile 0) (profile 1)) hbase := by
  unfold UtilityGame.externalRegret
  rw [rowReplacementValue A statusQuo row hrow,
    correlatedValue_zero A statusQuo hbase]

/-- Column regret is correlated row payoff minus the pure-column payoff
against the row marginal. -/
theorem externalRegret_one_eq {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig)) (col : J)
    (hbase : PayoffIntegrable statusQuo
      (fun profile => A (profile 0) (profile 1)))
    (hcol : PayoffIntegrable (rowMarginal statusQuo)
      (fun row => A row col)) :
    (utilityGame A).externalRegret statusQuo 1 col
        (correlatedIntegrable_one A statusQuo hbase)
        (columnReplacementIntegrable A statusQuo col hcol) =
      expect statusQuo (fun profile => A (profile 0) (profile 1)) hbase -
        expectedPayoff A (rowMarginal statusQuo) (PMF.pure col)
          (integrable_pure_column A (rowMarginal statusQuo) col hcol) := by
  unfold UtilityGame.externalRegret
  rw [columnReplacementValue A statusQuo col hcol,
    correlatedValue_one A statusQuo hbase]
  ring
/-- Correlated incumbent payoff cancels in the sum of signed row and column
external regrets. -/
theorem saddleGap_eq_externalRegret_add {I J : Type u}
    (A : I → J → ℝ) (statusQuo : PMF (Profile (form I J).sig))
    (row : I) (col : J)
    (hbase : PayoffIntegrable statusQuo
      (fun profile => A (profile 0) (profile 1)))
    (hrow : PayoffIntegrable (columnMarginal statusQuo) (A row))
    (hcol : PayoffIntegrable (rowMarginal statusQuo)
      (fun current => A current col)) :
    expectedPayoff A (PMF.pure row) (columnMarginal statusQuo)
        (integrable_pure_row A row (columnMarginal statusQuo) hrow) -
      expectedPayoff A (rowMarginal statusQuo) (PMF.pure col)
        (integrable_pure_column A (rowMarginal statusQuo) col hcol) =
      (utilityGame A).externalRegret statusQuo 0 row
        (correlatedIntegrable_zero A statusQuo hbase)
        (rowReplacementIntegrable A statusQuo row hrow) +
      (utilityGame A).externalRegret statusQuo 1 col
        (correlatedIntegrable_one A statusQuo hbase)
        (columnReplacementIntegrable A statusQuo col hcol) := by
  rw [externalRegret_zero_eq A statusQuo row hbase hrow,
    externalRegret_one_eq A statusQuo col hbase hcol]
  ring

/-- Uniform signed regret bounds control each pure saddle gap. -/
theorem pureSaddleGap_le_of_externalRegret_le {I J : Type u}
    (A : I → J → ℝ) (statusQuo : PMF (Profile (form I J).sig))
    {rowBound colBound : ℝ}
    (hbase : PayoffIntegrable statusQuo
      (fun profile => A (profile 0) (profile 1)))
    (hrows : ∀ row, PayoffIntegrable (columnMarginal statusQuo) (A row))
    (hcols : ∀ col, PayoffIntegrable (rowMarginal statusQuo)
      (fun row => A row col))
    (hrow : ∀ row,
      (utilityGame A).externalRegret statusQuo 0 row
        (correlatedIntegrable_zero A statusQuo hbase)
        (rowReplacementIntegrable A statusQuo row (hrows row)) ≤ rowBound)
    (hcol : ∀ col,
      (utilityGame A).externalRegret statusQuo 1 col
        (correlatedIntegrable_one A statusQuo hbase)
        (columnReplacementIntegrable A statusQuo col (hcols col)) ≤ colBound) :
    ∀ row col,
      expectedPayoff A (PMF.pure row) (columnMarginal statusQuo)
          (integrable_pure_row A row (columnMarginal statusQuo) (hrows row)) -
        expectedPayoff A (rowMarginal statusQuo) (PMF.pure col)
          (integrable_pure_column A (rowMarginal statusQuo) col (hcols col)) ≤
        rowBound + colBound := by
  intro row col
  rw [saddleGap_eq_externalRegret_add A statusQuo row col
    hbase (hrows row) (hcols col)]
  exact add_le_add (hrow row) (hcol col)
/-- Pure saddle bounds extend to mixed deviations only when both actual
independent deviation laws have integrable matrix payoff. -/
theorem mixedSaddleGap_le_of_externalRegret_le {I J : Type u}
    (A : I → J → ℝ) (statusQuo : PMF (Profile (form I J).sig))
    {rowBound colBound : ℝ}
    (hbase : PayoffIntegrable statusQuo
      (fun profile => A (profile 0) (profile 1)))
    (hrows : ∀ row, PayoffIntegrable (columnMarginal statusQuo) (A row))
    (hcols : ∀ col, PayoffIntegrable (rowMarginal statusQuo)
      (fun row => A row col))
    (hrow : ∀ row,
      (utilityGame A).externalRegret statusQuo 0 row
        (correlatedIntegrable_zero A statusQuo hbase)
        (rowReplacementIntegrable A statusQuo row (hrows row)) ≤ rowBound)
    (hcol : ∀ col,
      (utilityGame A).externalRegret statusQuo 1 col
        (correlatedIntegrable_one A statusQuo hbase)
        (columnReplacementIntegrable A statusQuo col (hcols col)) ≤ colBound)
    (rowDeviation : PMF I) (colDeviation : PMF J)
    (hrowMixed : UtilityIntegrable (utility A) 0
      ((form I J).mixed.play
        (mixedProfile rowDeviation (columnMarginal statusQuo))))
    (hcolMixed : UtilityIntegrable (utility A) 0
      ((form I J).mixed.play
        (mixedProfile (rowMarginal statusQuo) colDeviation))) :
    expectedPayoff A rowDeviation (columnMarginal statusQuo) hrowMixed -
        expectedPayoff A (rowMarginal statusQuo) colDeviation hcolMixed ≤
      rowBound + colBound := by
  have hpure := pureSaddleGap_le_of_externalRegret_le A statusQuo
    hbase hrows hcols hrow hcol
  have hpureRaw (row : I) (col : J) :
      expect (columnMarginal statusQuo) (A row) (hrows row) -
        expect (rowMarginal statusQuo) (fun current => A current col)
          (hcols col) ≤ rowBound + colBound := by
    have h := hpure row col
    rw [expectedPayoff_pure_row A row (columnMarginal statusQuo) (hrows row),
      expectedPayoff_pure_column A (rowMarginal statusQuo) col (hcols col)] at h
    exact h
  obtain ⟨hcolOuter, hcolAverage⟩ :=
    expectedPayoff_eq_expect_columns A (rowMarginal statusQuo) colDeviation
      hcolMixed hcols
  have hcolGap (row : I) :
      expect (columnMarginal statusQuo) (A row) (hrows row) -
        expectedPayoff A (rowMarginal statusQuo) colDeviation hcolMixed ≤
          rowBound + colBound := by
    let c := expect (columnMarginal statusQuo) (A row) (hrows row)
    have hsub : PayoffIntegrable colDeviation
        (fun col => c - expect (rowMarginal statusQuo)
          (fun current => A current col) (hcols col)) :=
      payoffIntegrable_sub (payoffIntegrable_constant colDeviation c) hcolOuter
    have hbound := expect_le_const colDeviation _ hsub
      (rowBound + colBound) (fun col _ => hpureRaw row col)
    have hvalue :
        expect colDeviation (fun col => c - expect (rowMarginal statusQuo)
            (fun current => A current col) (hcols col)) hsub =
          c - expectedPayoff A (rowMarginal statusQuo) colDeviation hcolMixed := by
      calc
        _ = expect colDeviation (fun _ => c)
              (payoffIntegrable_constant colDeviation c) -
            expect colDeviation (fun col =>
              expect (rowMarginal statusQuo) (fun current => A current col)
                (hcols col)) hcolOuter :=
          expect_sub (payoffIntegrable_constant colDeviation c) hcolOuter
        _ = _ := by rw [expect_constant, ← hcolAverage]
    rw [hvalue] at hbound
    exact hbound
  obtain ⟨hrowOuter, hrowAverage⟩ :=
    expectedPayoff_eq_expect_rows A rowDeviation (columnMarginal statusQuo)
      hrowMixed hrows
  let c := expectedPayoff A (rowMarginal statusQuo) colDeviation hcolMixed
  have hsub : PayoffIntegrable rowDeviation
      (fun row => expect (columnMarginal statusQuo) (A row) (hrows row) - c) :=
    payoffIntegrable_sub hrowOuter (payoffIntegrable_constant rowDeviation c)
  have hbound := expect_le_const rowDeviation _ hsub
    (rowBound + colBound) (fun row _ => hcolGap row)
  have hvalue :
      expect rowDeviation (fun row =>
          expect (columnMarginal statusQuo) (A row) (hrows row) - c) hsub =
        expectedPayoff A rowDeviation (columnMarginal statusQuo) hrowMixed - c := by
    calc
      _ = expect rowDeviation (fun row =>
            expect (columnMarginal statusQuo) (A row) (hrows row)) hrowOuter -
          expect rowDeviation (fun _ => c)
            (payoffIntegrable_constant rowDeviation c) :=
        expect_sub hrowOuter (payoffIntegrable_constant rowDeviation c)
      _ = _ := by rw [expect_constant, ← hrowAverage]
  rw [hvalue] at hbound
  exact hbound
/-- Independent marginals of a correlated trace are approximate Nash when
all actual unilateral mixed deviation laws have defined payoff. -/
theorem marginalProfile_isεNash_of_externalRegret_le {I J : Type u}
    (A : I → J → ℝ) (statusQuo : PMF (Profile (form I J).sig))
    {rowBound colBound : ℝ}
    (hbase : PayoffIntegrable statusQuo
      (fun profile => A (profile 0) (profile 1)))
    (hrows : ∀ row, PayoffIntegrable (columnMarginal statusQuo) (A row))
    (hcols : ∀ col, PayoffIntegrable (rowMarginal statusQuo)
      (fun row => A row col))
    (hrow : ∀ row,
      (utilityGame A).externalRegret statusQuo 0 row
        (correlatedIntegrable_zero A statusQuo hbase)
        (rowReplacementIntegrable A statusQuo row (hrows row)) ≤ rowBound)
    (hcol : ∀ col,
      (utilityGame A).externalRegret statusQuo 1 col
        (correlatedIntegrable_one A statusQuo hbase)
        (columnReplacementIntegrable A statusQuo col (hcols col)) ≤ colBound)
    (hrowMixed : ∀ replacement : PMF I, UtilityIntegrable (utility A) 0
      ((form I J).mixed.play
        (mixedProfile replacement (columnMarginal statusQuo))))
    (hcolMixed : ∀ replacement : PMF J, UtilityIntegrable (utility A) 0
      ((form I J).mixed.play
        (mixedProfile (rowMarginal statusQuo) replacement))) :
    IsεNash (form I J).mixed (utility A) (rowBound + colBound)
      (mixedProfile (rowMarginal statusQuo) (columnMarginal statusQuo)) := by
  rw [isεNash_iff]
  intro who replacement
  rcases (by decide : ∀ player : Fin 2, player = 0 ∨ player = 1) who with rfl | rfl
  · let base := hrowMixed (rowMarginal statusQuo)
    let dev := hrowMixed replacement
    refine ⟨base, ?_, ?_⟩
    · simpa only [mixedProfile_update_zero] using dev
    · have hgap := mixedSaddleGap_le_of_externalRegret_le A statusQuo
        hbase hrows hcols hrow hcol replacement (columnMarginal statusQuo)
        dev (hcolMixed (columnMarginal statusQuo))
      have hineq :
          expectedUtility (utility A) 0
              ((form I J).mixed.play
                (mixedProfile replacement (columnMarginal statusQuo))) dev ≤
            expectedUtility (utility A) 0
                ((form I J).mixed.play
                  (mixedProfile (rowMarginal statusQuo)
                    (columnMarginal statusQuo))) base +
              (rowBound + colBound) := by
        show expectedPayoff A replacement (columnMarginal statusQuo) dev ≤
          expectedPayoff A (rowMarginal statusQuo)
            (columnMarginal statusQuo) base + (rowBound + colBound)
        linarith
      simpa only [mixedProfile_update_zero] using hineq
  · let baseZero := hrowMixed (rowMarginal statusQuo)
    let baseOne : UtilityIntegrable (utility A) 1
        ((form I J).mixed.play
          (mixedProfile (rowMarginal statusQuo) (columnMarginal statusQuo))) :=
      payoffIntegrable_neg baseZero
    let devZero := hcolMixed replacement
    let devOne : UtilityIntegrable (utility A) 1
        ((form I J).mixed.play
          (mixedProfile (rowMarginal statusQuo) replacement)) :=
      payoffIntegrable_neg devZero
    refine ⟨baseOne, ?_, ?_⟩
    · simpa only [mixedProfile_update_one] using devOne
    · have hgap := mixedSaddleGap_le_of_externalRegret_le A statusQuo
        hbase hrows hcols hrow hcol (rowMarginal statusQuo) replacement
        baseZero devZero
      have hineq :
          expectedUtility (utility A) 1
              ((form I J).mixed.play
                (mixedProfile (rowMarginal statusQuo) replacement)) devOne ≤
            expectedUtility (utility A) 1
                ((form I J).mixed.play
                  (mixedProfile (rowMarginal statusQuo)
                    (columnMarginal statusQuo))) baseOne +
              (rowBound + colBound) := by
        rw [expectedUtility_one_mixedProfile A (rowMarginal statusQuo)
          replacement devZero devOne,
          expectedUtility_one_mixedProfile A (rowMarginal statusQuo)
            (columnMarginal statusQuo) baseZero baseOne]
        linarith
      simpa only [mixedProfile_update_one] using hineq
end GameTheory.MatrixGame
