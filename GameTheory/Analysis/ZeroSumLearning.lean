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
    (statusQuo : PMF (Profile (form I J).sig)) :
    expectedUtility (utility A) 0 ((form I J).outcomeLaw statusQuo) =
      expect statusQuo (fun profile => A (profile 0) (profile 1)) := by
  let f : I × J → ℝ := fun outcome => A outcome.1 outcome.2
  let projection : Profile (form I J).sig → I × J :=
    fun profile => (profile 0, profile 1)
  refine (show expect ((form I J).outcomeLaw statusQuo) f = _ from ?_)
  calc
    expect ((form I J).outcomeLaw statusQuo) f =
        expect (statusQuo.map projection) f :=
      expect_congr_law (correlatedPlay_eq_map statusQuo) f
    _ = expect statusQuo (f ∘ projection) :=
      expect_map projection statusQuo f
private theorem correlatedValue_one {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig)) :
    expectedUtility (utility A) 1 ((form I J).outcomeLaw statusQuo) =
      -expect statusQuo (fun profile => A (profile 0) (profile 1)) := by
  let f : I × J → ℝ := fun outcome => -A outcome.1 outcome.2
  let projection : Profile (form I J).sig → I × J :=
    fun profile => (profile 0, profile 1)
  refine (show expect ((form I J).outcomeLaw statusQuo) f = _ from ?_)
  calc
    expect ((form I J).outcomeLaw statusQuo) f =
        expect (statusQuo.map projection) f :=
      expect_congr_law (correlatedPlay_eq_map statusQuo) f
    _ = expect statusQuo (f ∘ projection) :=
      expect_map projection statusQuo f
    _ = -expect statusQuo (fun profile => A (profile 0) (profile 1)) :=
      expect_neg

private theorem rowReplacementValue {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig)) (row : I) :
    expectedUtility (utility A) 0
        (statusQuo.bind fun profile =>
          (form I J).play (Profile.update profile 0 row)) =
      expectedPayoff A (PMF.pure row) (columnMarginal statusQuo) := by
  exact expectedUtility_congr_law (utility A) 0
    ((rowReplacement_eq_map statusQuo row).trans
      (mixed_play_pure_row row (columnMarginal statusQuo)).symm)

private theorem columnReplacementValue {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig)) (col : J) :
    expectedUtility (utility A) 1
        (statusQuo.bind fun profile =>
          (form I J).play (Profile.update profile 1 col)) =
      -expectedPayoff A (rowMarginal statusQuo) (PMF.pure col) := by
  let law := (form I J).mixed.play
    (mixedProfile (rowMarginal statusQuo) (PMF.pure col))
  calc
    _ = expectedUtility (utility A) 1 law :=
      expectedUtility_congr_law (utility A) 1
        ((columnReplacement_eq_map statusQuo col).trans
          (mixed_play_pure_column (rowMarginal statusQuo) col).symm)
    _ = -expectedPayoff A (rowMarginal statusQuo) (PMF.pure col) :=
      expectedUtility_one_mixedProfile A (rowMarginal statusQuo)
        (PMF.pure col)
/-- Row regret is the pure-row payoff against the column marginal minus the
correlated incumbent payoff. -/
theorem externalRegret_zero_eq {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig)) (row : I) :
    (utilityGame A).externalRegret statusQuo 0 row =
      expectedPayoff A (PMF.pure row) (columnMarginal statusQuo) -
        expect statusQuo (fun profile => A (profile 0) (profile 1)) := by
  unfold UtilityGame.externalRegret
  rw [rowReplacementValue A statusQuo row,
    correlatedValue_zero A statusQuo]

/-- Column regret is correlated row payoff minus the pure-column payoff
against the row marginal. -/
theorem externalRegret_one_eq {I J : Type u} (A : I → J → ℝ)
    (statusQuo : PMF (Profile (form I J).sig)) (col : J) :
    (utilityGame A).externalRegret statusQuo 1 col =
      expect statusQuo (fun profile => A (profile 0) (profile 1)) -
        expectedPayoff A (rowMarginal statusQuo) (PMF.pure col) := by
  unfold UtilityGame.externalRegret
  rw [columnReplacementValue A statusQuo col,
    correlatedValue_one A statusQuo]
  ring
/-- Correlated incumbent payoff cancels in the sum of signed row and column
external regrets. -/
theorem saddleGap_eq_externalRegret_add {I J : Type u}
    (A : I → J → ℝ) (statusQuo : PMF (Profile (form I J).sig))
    (row : I) (col : J) :
    expectedPayoff A (PMF.pure row) (columnMarginal statusQuo) -
      expectedPayoff A (rowMarginal statusQuo) (PMF.pure col) =
      (utilityGame A).externalRegret statusQuo 0 row +
      (utilityGame A).externalRegret statusQuo 1 col := by
  rw [externalRegret_zero_eq A statusQuo row,
    externalRegret_one_eq A statusQuo col]
  ring

/-- Uniform signed regret bounds control each pure saddle gap. -/
theorem pureSaddleGap_le_of_externalRegret_le {I J : Type u}
    (A : I → J → ℝ) (statusQuo : PMF (Profile (form I J).sig))
    {rowBound colBound : ℝ}
    (hrow : ∀ row,
      (utilityGame A).externalRegret statusQuo 0 row
         ≤ rowBound)
    (hcol : ∀ col,
      (utilityGame A).externalRegret statusQuo 1 col
         ≤ colBound) :
    ∀ row col,
      expectedPayoff A (PMF.pure row) (columnMarginal statusQuo) -
        expectedPayoff A (rowMarginal statusQuo) (PMF.pure col) ≤
        rowBound + colBound := by
  intro row col
  rw [saddleGap_eq_externalRegret_add A statusQuo row col]
  exact add_le_add (hrow row) (hcol col)
/-- Pure saddle bounds extend to mixed deviations only when both actual
independent deviation laws have integrable matrix payoff. -/
theorem mixedSaddleGap_le_of_externalRegret_le {I J : Type u}
    (A : I → J → ℝ) (statusQuo : PMF (Profile (form I J).sig))
    {rowBound colBound : ℝ}
    (hrow : ∀ row,
      (utilityGame A).externalRegret statusQuo 0 row
         ≤ rowBound)
    (hcol : ∀ col,
      (utilityGame A).externalRegret statusQuo 1 col
         ≤ colBound)
    (rowDeviation : PMF I) (colDeviation : PMF J)
    (hrowMixed : UtilityIntegrable (utility A) 0
      ((form I J).mixed.play
        (mixedProfile rowDeviation (columnMarginal statusQuo))))
    (hcolMixed : UtilityIntegrable (utility A) 0
      ((form I J).mixed.play
        (mixedProfile (rowMarginal statusQuo) colDeviation))) :
    expectedPayoff A rowDeviation (columnMarginal statusQuo) -
        expectedPayoff A (rowMarginal statusQuo) colDeviation ≤
      rowBound + colBound := by
  have hpure := pureSaddleGap_le_of_externalRegret_le A statusQuo
     hrow hcol
  have hpureRaw (row : I) (col : J) :
      expect (columnMarginal statusQuo) (A row) -
        expect (rowMarginal statusQuo) (fun current => A current col)
           ≤ rowBound + colBound := by
    have h := hpure row col
    rw [expectedPayoff_pure_row A row (columnMarginal statusQuo),
      expectedPayoff_pure_column A (rowMarginal statusQuo) col] at h
    exact h
  obtain ⟨hcolOuter, hcolAverage⟩ :=
    expectedPayoff_eq_expect_columns A (rowMarginal statusQuo) colDeviation
      hcolMixed
  have hcolGap (row : I) :
      expect (columnMarginal statusQuo) (A row) -
        expectedPayoff A (rowMarginal statusQuo) colDeviation ≤
          rowBound + colBound := by
    let c := expect (columnMarginal statusQuo) (A row)
    have hsub : PayoffIntegrable colDeviation
        (fun col => c - expect (rowMarginal statusQuo)
          (fun current => A current col)) :=
      payoffIntegrable_sub (payoffIntegrable_constant colDeviation c) hcolOuter
    have hbound := expect_le_const colDeviation _ hsub
      (rowBound + colBound) (fun col _ => hpureRaw row col)
    have hvalue :
        expect colDeviation (fun col => c - expect (rowMarginal statusQuo)
            (fun current => A current col)) =
          c - expectedPayoff A (rowMarginal statusQuo) colDeviation := by
      calc
        _ = expect colDeviation (fun _ => c) -
            expect colDeviation (fun col =>
              expect (rowMarginal statusQuo) (fun current => A current col)) :=
          expect_sub (payoffIntegrable_constant colDeviation c) hcolOuter
        _ = _ := by rw [expect_constant, ← hcolAverage]
    rw [hvalue] at hbound
    exact hbound
  obtain ⟨hrowOuter, hrowAverage⟩ :=
    expectedPayoff_eq_expect_rows A rowDeviation (columnMarginal statusQuo)
      hrowMixed
  let c := expectedPayoff A (rowMarginal statusQuo) colDeviation
  have hsub : PayoffIntegrable rowDeviation
      (fun row => expect (columnMarginal statusQuo) (A row) - c) :=
    payoffIntegrable_sub hrowOuter (payoffIntegrable_constant rowDeviation c)
  have hbound := expect_le_const rowDeviation _ hsub
    (rowBound + colBound) (fun row _ => hcolGap row)
  have hvalue :
      expect rowDeviation (fun row =>
          expect (columnMarginal statusQuo) (A row) - c) =
        expectedPayoff A rowDeviation (columnMarginal statusQuo) - c := by
    calc
      _ = expect rowDeviation (fun row =>
            expect (columnMarginal statusQuo) (A row)) -
          expect rowDeviation (fun _ => c) :=
        expect_sub hrowOuter (payoffIntegrable_constant rowDeviation c)
      _ = _ := by rw [expect_constant, ← hrowAverage]
  rw [hvalue] at hbound
  exact hbound
/-- Independent marginals of a correlated trace are approximate Nash when
all actual unilateral mixed deviation laws have defined payoff. -/
theorem marginalProfile_isεNash_of_externalRegret_le {I J : Type u}
    (A : I → J → ℝ) (statusQuo : PMF (Profile (form I J).sig))
    {rowBound colBound : ℝ}
    (hrow : ∀ row,
      (utilityGame A).externalRegret statusQuo 0 row
         ≤ rowBound)
    (hcol : ∀ col,
      (utilityGame A).externalRegret statusQuo 1 col
         ≤ colBound)
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
    refine (euPreferenceWithin_iff _ _ _ _ _ base
      (by simpa only [mixedProfile_update_zero] using dev)).2 ?_
    · have hgap := mixedSaddleGap_le_of_externalRegret_le A statusQuo
         hrow hcol replacement (columnMarginal statusQuo)
        dev (hcolMixed (columnMarginal statusQuo))
      have hineq :
          expectedUtility (utility A) 0
              ((form I J).mixed.play
                (mixedProfile replacement (columnMarginal statusQuo))) ≤
            expectedUtility (utility A) 0
                ((form I J).mixed.play
                  (mixedProfile (rowMarginal statusQuo)
                    (columnMarginal statusQuo))) +
              (rowBound + colBound) := by
        show expectedPayoff A replacement (columnMarginal statusQuo) ≤
          expectedPayoff A (rowMarginal statusQuo)
            (columnMarginal statusQuo) + (rowBound + colBound)
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
    refine (euPreferenceWithin_iff _ _ _ _ _ baseOne
      (by simpa only [mixedProfile_update_one] using devOne)).2 ?_
    · have hgap := mixedSaddleGap_le_of_externalRegret_le A statusQuo
         hrow hcol (rowMarginal statusQuo) replacement
        baseZero devZero
      have hineq :
          expectedUtility (utility A) 1
              ((form I J).mixed.play
                (mixedProfile (rowMarginal statusQuo) replacement)) ≤
            expectedUtility (utility A) 1
                ((form I J).mixed.play
                  (mixedProfile (rowMarginal statusQuo)
                    (columnMarginal statusQuo))) +
              (rowBound + colBound) := by
        rw [expectedUtility_one_mixedProfile A (rowMarginal statusQuo)
          replacement,
          expectedUtility_one_mixedProfile A (rowMarginal statusQuo)
            (columnMarginal statusQuo)]
        linarith
      simpa only [mixedProfile_update_one] using hineq
end GameTheory.MatrixGame
