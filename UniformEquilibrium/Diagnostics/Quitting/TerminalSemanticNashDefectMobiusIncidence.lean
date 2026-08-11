/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter

/-!
# Local Nash defect in Boolean Möbius and incidence coordinates

The one-coordinate Nash defect of a played product root has an exact
two-action formula.  If `g` is pure Quit minus pure Continue, then

`defect_i = continue_i * (g_i)_+ + quit_i * (-g_i)_+`.

Thus defect is precisely the probability assigned to the worse played action
times the positive endpoint advantage.  Substituting the Boolean Möbius
adapter splits `g_i` into singleton, pair, and higher grades.  The positive
part does not distribute through that signed sum, but it is subadditive.  The
resulting six-term bound is the sharp grade-facing interface: positive and
negative singleton, pair, and higher derivatives are charged with the actual
Continue and Quit probabilities respectively.

The final section refines each signed grade into nonnegative Möbius incidence
charges.  A Möbius monomial is the probability of the corresponding quitter
cylinder.  Multiplying it by the player's played-action probability produces
an actual action-and-coalition cylinder.  This gives a nonnegative consumer
for packet/cycle arguments, while making the unavoidable cancellation seam
explicit: coefficients inside one derivative grade may have either sign, so
only an upper charge, not an exact positive-coefficient allocation, exists in
general.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Exact played-action formula -/

/-- Exact decomposition of coordinate Nash defect into the two possible
played-action mistakes. -/
theorem quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootCoordinateNashDefect reward tail root who =
      (root who false).toReal *
          max (quittingRootEndpointDifference reward tail root who) 0 +
        (root who true).toReal *
          max (-quittingRootEndpointDifference reward tail root who) 0 := by
  let quitValue := quittingRootQuitPayoff reward tail root who
  let continueValue := quittingRootContinuePayoff reward tail root who
  let quitProbability := (root who true).toReal
  let continueProbability := (root who false).toReal
  let difference := quittingRootEndpointDifference reward tail root who
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix
    reward tail root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hsum' : continueProbability + quitProbability = 1 := hsum
  have hdifference : difference = quitValue - continueValue := rfl
  rw [quittingRootCoordinateNashDefect, hmix]
  change max quitValue continueValue -
      (quitProbability * quitValue + continueProbability * continueValue) =
    continueProbability * max difference 0 +
      quitProbability * max (-difference) 0
  by_cases hpositive : 0 ≤ difference
  · have hvalues : continueValue ≤ quitValue := by
      rw [hdifference] at hpositive
      linarith
    rw [max_eq_left hvalues, max_eq_left hpositive,
      max_eq_right (by linarith : -difference ≤ 0)]
    rw [hdifference]
    have hquitProbability : quitProbability = 1 - continueProbability := by
      linarith [hsum']
    rw [hquitProbability]
    ring
  · have hnegative : difference ≤ 0 := le_of_not_ge hpositive
    have hvalues : quitValue ≤ continueValue := by
      rw [hdifference] at hnegative
      linarith
    rw [max_eq_right hvalues, max_eq_right hnegative,
      max_eq_left (by linarith : 0 ≤ -difference)]
    rw [hdifference]
    have hcontinueProbability : continueProbability = 1 - quitProbability := by
      linarith [hsum']
    rw [hcontinueProbability]
    ring

/-! ## Singleton, pair, and higher derivative grades -/

/-- Exact Möbius-grade form of the played-action defect identity. -/
theorem quittingRootCoordinateNashDefect_eq_mobiusGradePosParts
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootCoordinateNashDefect reward tail root who =
      (root who false).toReal *
          max
            ((quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
                (hazardOfRoot root) who 1 +
              (quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
                  (hazardOfRoot root) who 2 +
                (quittingStageCenteredCoalGame reward tail who).higherOrderCoordinateDerivative
                  (hazardOfRoot root) who)
            0 +
        (root who true).toReal *
          max
            (-((quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
                  (hazardOfRoot root) who 1 +
                (quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
                    (hazardOfRoot root) who 2 +
                  (quittingStageCenteredCoalGame reward tail who).higherOrderCoordinateDerivative
                    (hazardOfRoot root) who))
            0 := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart,
    quittingRootEndpointDifference_eq_mobiusCardinalitySplit]

omit [Fintype ι] [DecidableEq ι] in
private theorem max_three_add_zero_le_sum_max
    (a b c : ℝ) :
    max (a + b + c) 0 ≤ max a 0 + max b 0 + max c 0 := by
  apply max_le
  · exact add_le_add
      (add_le_add (le_max_left a 0) (le_max_left b 0))
      (le_max_left c 0)
  · exact add_nonneg
      (add_nonneg (le_max_right a 0) (le_max_right b 0))
      (le_max_right c 0)

/-- The exact positive part can be charged grade by grade.  This loses only
signed cancellation between singleton, pair, and higher derivatives. -/
theorem quittingRootCoordinateNashDefect_le_mobiusGradeCharges
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootCoordinateNashDefect reward tail root who ≤
      (root who false).toReal *
          (max
              ((quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
                (hazardOfRoot root) who 1) 0 +
            max
              ((quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
                (hazardOfRoot root) who 2) 0 +
            max
              ((quittingStageCenteredCoalGame reward tail who).higherOrderCoordinateDerivative
                (hazardOfRoot root) who) 0) +
        (root who true).toReal *
          (max
              (-((quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
                (hazardOfRoot root) who 1)) 0 +
            max
              (-((quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
                (hazardOfRoot root) who 2)) 0 +
            max
              (-((quittingStageCenteredCoalGame reward tail who).higherOrderCoordinateDerivative
                (hazardOfRoot root) who)) 0) := by
  let singleton :=
    (quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
      (hazardOfRoot root) who 1
  let pair :=
    (quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
      (hazardOfRoot root) who 2
  let higher :=
    (quittingStageCenteredCoalGame reward tail who).higherOrderCoordinateDerivative
      (hazardOfRoot root) who
  have hpositive := max_three_add_zero_le_sum_max singleton pair higher
  have hnegative := max_three_add_zero_le_sum_max (-singleton) (-pair) (-higher)
  have hcontinue : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  have hquit : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  rw [quittingRootCoordinateNashDefect_eq_mobiusGradePosParts]
  change (root who false).toReal * max (singleton + pair + higher) 0 +
      (root who true).toReal * max (-(singleton + pair + higher)) 0 ≤ _
  have hnegativeSum : -(singleton + pair + higher) =
      -singleton + -pair + -higher := by ring
  rw [hnegativeSum]
  exact add_le_add
    (mul_le_mul_of_nonneg_left hpositive hcontinue)
    (mul_le_mul_of_nonneg_left hnegative hquit)

/-! ## Nonnegative Möbius incidence charges -/

/-- Positive-coefficient incidence charge of one Möbius cardinality grade.
The monomial is the probability that every other member of `S` Quits. -/
def quittingMobiusPositiveIncidenceChargeOfCard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (card : ℕ) : ℝ :=
  ∑ S : Finset ι,
    if who ∈ S ∧ S.card = card then
      max (quittingStageMobiusCoeff reward tail who S) 0 *
        ∏ player ∈ S.erase who, hazardOfRoot root player
    else 0

/-- Negative-coefficient incidence charge of one Möbius cardinality grade.
-/
def quittingMobiusNegativeIncidenceChargeOfCard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (card : ℕ) : ℝ :=
  ∑ S : Finset ι,
    if who ∈ S ∧ S.card = card then
      max (-quittingStageMobiusCoeff reward tail who S) 0 *
        ∏ player ∈ S.erase who, hazardOfRoot root player
    else 0

/-- Positive-coefficient incidence charge of all Möbius grades at least
three. -/
def quittingMobiusPositiveHigherIncidenceCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) : ℝ :=
  ∑ S : Finset ι,
    if who ∈ S ∧ 3 ≤ S.card then
      max (quittingStageMobiusCoeff reward tail who S) 0 *
        ∏ player ∈ S.erase who, hazardOfRoot root player
    else 0

/-- Negative-coefficient incidence charge of all Möbius grades at least
three. -/
def quittingMobiusNegativeHigherIncidenceCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) : ℝ :=
  ∑ S : Finset ι,
    if who ∈ S ∧ 3 ≤ S.card then
      max (-quittingStageMobiusCoeff reward tail who S) 0 *
        ∏ player ∈ S.erase who, hazardOfRoot root player
    else 0

omit [Fintype ι] in
private theorem mobiusMonomial_nonneg
    (root : ι → PMF Bool) (who : ι) (S : Finset ι) :
    0 ≤ ∏ player ∈ S.erase who, hazardOfRoot root player := by
  exact Finset.prod_nonneg fun player _ => hazardOfRoot_nonneg root player

private theorem coordinateDerivativeOfCard_le_positiveIncidenceCharge
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (card : ℕ) :
    (quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
        (hazardOfRoot root) who card ≤
      quittingMobiusPositiveIncidenceChargeOfCard reward tail root who card := by
  unfold CoalGame.coordinateDerivativeOfCard
    quittingMobiusPositiveIncidenceChargeOfCard quittingStageMobiusCoeff
  apply Finset.sum_le_sum
  intro S _
  split_ifs with hgrade
  · exact mul_le_mul_of_nonneg_right
      (le_max_left _ 0) (mobiusMonomial_nonneg root who S)
  · exact le_rfl

private theorem neg_coordinateDerivativeOfCard_le_negativeIncidenceCharge
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (card : ℕ) :
    -(quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
        (hazardOfRoot root) who card ≤
      quittingMobiusNegativeIncidenceChargeOfCard reward tail root who card := by
  unfold CoalGame.coordinateDerivativeOfCard
    quittingMobiusNegativeIncidenceChargeOfCard quittingStageMobiusCoeff
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro S _
  split_ifs with hgrade
  · calc
      -((quittingStageCenteredCoalGame reward tail who).unanimityCoeff S *
          ∏ i ∈ S.erase who, hazardOfRoot root i) =
          (-(quittingStageCenteredCoalGame reward tail who).unanimityCoeff S) *
            ∏ i ∈ S.erase who, hazardOfRoot root i := by ring
      _ ≤ max (-(quittingStageCenteredCoalGame reward tail who).unanimityCoeff S) 0 *
            ∏ i ∈ S.erase who, hazardOfRoot root i :=
        mul_le_mul_of_nonneg_right
          (le_max_left _ 0) (mobiusMonomial_nonneg root who S)
  · simp

private theorem higherDerivative_le_positiveIncidenceCharge
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    (quittingStageCenteredCoalGame reward tail who).higherOrderCoordinateDerivative
        (hazardOfRoot root) who ≤
      quittingMobiusPositiveHigherIncidenceCharge reward tail root who := by
  unfold CoalGame.higherOrderCoordinateDerivative
    quittingMobiusPositiveHigherIncidenceCharge quittingStageMobiusCoeff
  apply Finset.sum_le_sum
  intro S _
  split_ifs with hgrade
  · exact mul_le_mul_of_nonneg_right
      (le_max_left _ 0) (mobiusMonomial_nonneg root who S)
  · exact le_rfl

private theorem neg_higherDerivative_le_negativeIncidenceCharge
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    -(quittingStageCenteredCoalGame reward tail who).higherOrderCoordinateDerivative
        (hazardOfRoot root) who ≤
      quittingMobiusNegativeHigherIncidenceCharge reward tail root who := by
  unfold CoalGame.higherOrderCoordinateDerivative
    quittingMobiusNegativeHigherIncidenceCharge quittingStageMobiusCoeff
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro S _
  split_ifs with hgrade
  · calc
      -((quittingStageCenteredCoalGame reward tail who).unanimityCoeff S *
          ∏ i ∈ S.erase who, hazardOfRoot root i) =
          (-(quittingStageCenteredCoalGame reward tail who).unanimityCoeff S) *
            ∏ i ∈ S.erase who, hazardOfRoot root i := by ring
      _ ≤ max (-(quittingStageCenteredCoalGame reward tail who).unanimityCoeff S) 0 *
            ∏ i ∈ S.erase who, hazardOfRoot root i :=
        mul_le_mul_of_nonneg_right
          (le_max_left _ 0) (mobiusMonomial_nonneg root who S)
  · simp

private theorem positiveIncidenceChargeOfCard_nonneg
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (card : ℕ) :
    0 ≤ quittingMobiusPositiveIncidenceChargeOfCard reward tail root who card := by
  unfold quittingMobiusPositiveIncidenceChargeOfCard
  exact Finset.sum_nonneg fun S _ => by
    split_ifs
    · exact mul_nonneg (le_max_right _ 0) (mobiusMonomial_nonneg root who S)
    · exact le_rfl

private theorem negativeIncidenceChargeOfCard_nonneg
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (card : ℕ) :
    0 ≤ quittingMobiusNegativeIncidenceChargeOfCard reward tail root who card := by
  unfold quittingMobiusNegativeIncidenceChargeOfCard
  exact Finset.sum_nonneg fun S _ => by
    split_ifs
    · exact mul_nonneg (le_max_right _ 0) (mobiusMonomial_nonneg root who S)
    · exact le_rfl

private theorem positiveHigherIncidenceCharge_nonneg
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    0 ≤ quittingMobiusPositiveHigherIncidenceCharge reward tail root who := by
  unfold quittingMobiusPositiveHigherIncidenceCharge
  exact Finset.sum_nonneg fun S _ => by
    split_ifs
    · exact mul_nonneg (le_max_right _ 0) (mobiusMonomial_nonneg root who S)
    · exact le_rfl

private theorem negativeHigherIncidenceCharge_nonneg
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    0 ≤ quittingMobiusNegativeHigherIncidenceCharge reward tail root who := by
  unfold quittingMobiusNegativeHigherIncidenceCharge
  exact Finset.sum_nonneg fun S _ => by
    split_ifs
    · exact mul_nonneg (le_max_right _ 0) (mobiusMonomial_nonneg root who S)
    · exact le_rfl

private theorem max_le_nonnegative_upper {a upper : ℝ}
    (ha : a ≤ upper) (hupper : 0 ≤ upper) : max a 0 ≤ upper :=
  max_le ha hupper

/-- **Game-facing Möbius incidence charge.** Coordinate Nash defect is paid
by six nonnegative actual product-event cylinders: positive Möbius grades
when the player played Continue, and negative grades when the player played
Quit.  No coefficient sign is assumed. -/
theorem quittingRootCoordinateNashDefect_le_playedMobiusIncidenceCharges
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootCoordinateNashDefect reward tail root who ≤
      (root who false).toReal *
          (quittingMobiusPositiveIncidenceChargeOfCard reward tail root who 1 +
            quittingMobiusPositiveIncidenceChargeOfCard reward tail root who 2 +
            quittingMobiusPositiveHigherIncidenceCharge reward tail root who) +
        (root who true).toReal *
          (quittingMobiusNegativeIncidenceChargeOfCard reward tail root who 1 +
            quittingMobiusNegativeIncidenceChargeOfCard reward tail root who 2 +
            quittingMobiusNegativeHigherIncidenceCharge reward tail root who) := by
  let singleton :=
    (quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
      (hazardOfRoot root) who 1
  let pair :=
    (quittingStageCenteredCoalGame reward tail who).coordinateDerivativeOfCard
      (hazardOfRoot root) who 2
  let higher :=
    (quittingStageCenteredCoalGame reward tail who).higherOrderCoordinateDerivative
      (hazardOfRoot root) who
  let positiveSingleton :=
    quittingMobiusPositiveIncidenceChargeOfCard reward tail root who 1
  let positivePair :=
    quittingMobiusPositiveIncidenceChargeOfCard reward tail root who 2
  let positiveHigher :=
    quittingMobiusPositiveHigherIncidenceCharge reward tail root who
  let negativeSingleton :=
    quittingMobiusNegativeIncidenceChargeOfCard reward tail root who 1
  let negativePair :=
    quittingMobiusNegativeIncidenceChargeOfCard reward tail root who 2
  let negativeHigher :=
    quittingMobiusNegativeHigherIncidenceCharge reward tail root who
  have hsPos : singleton ≤ positiveSingleton :=
    coordinateDerivativeOfCard_le_positiveIncidenceCharge
      (reward := reward) tail root who 1
  have hpPos : pair ≤ positivePair :=
    coordinateDerivativeOfCard_le_positiveIncidenceCharge
      (reward := reward) tail root who 2
  have hhPos : higher ≤ positiveHigher :=
    higherDerivative_le_positiveIncidenceCharge
      (reward := reward) tail root who
  have hsNeg : -singleton ≤ negativeSingleton :=
    neg_coordinateDerivativeOfCard_le_negativeIncidenceCharge
      (reward := reward) tail root who 1
  have hpNeg : -pair ≤ negativePair :=
    neg_coordinateDerivativeOfCard_le_negativeIncidenceCharge
      (reward := reward) tail root who 2
  have hhNeg : -higher ≤ negativeHigher :=
    neg_higherDerivative_le_negativeIncidenceCharge
      (reward := reward) tail root who
  have hsPos0 : 0 ≤ positiveSingleton :=
    positiveIncidenceChargeOfCard_nonneg
      (reward := reward) tail root who 1
  have hpPos0 : 0 ≤ positivePair :=
    positiveIncidenceChargeOfCard_nonneg
      (reward := reward) tail root who 2
  have hhPos0 : 0 ≤ positiveHigher :=
    positiveHigherIncidenceCharge_nonneg
      (reward := reward) tail root who
  have hsNeg0 : 0 ≤ negativeSingleton :=
    negativeIncidenceChargeOfCard_nonneg
      (reward := reward) tail root who 1
  have hpNeg0 : 0 ≤ negativePair :=
    negativeIncidenceChargeOfCard_nonneg
      (reward := reward) tail root who 2
  have hhNeg0 : 0 ≤ negativeHigher :=
    negativeHigherIncidenceCharge_nonneg
      (reward := reward) tail root who
  have hcontinue : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  have hquit : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hgrade := quittingRootCoordinateNashDefect_le_mobiusGradeCharges
    (reward := reward) tail root who
  calc
    quittingRootCoordinateNashDefect reward tail root who ≤
        (root who false).toReal *
            (max singleton 0 + max pair 0 + max higher 0) +
          (root who true).toReal *
            (max (-singleton) 0 + max (-pair) 0 + max (-higher) 0) := hgrade
    _ ≤ (root who false).toReal *
            (positiveSingleton + positivePair + positiveHigher) +
          (root who true).toReal *
            (negativeSingleton + negativePair + negativeHigher) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hcontinue
        exact add_le_add
          (add_le_add
            (max_le_nonnegative_upper hsPos hsPos0)
            (max_le_nonnegative_upper hpPos hpPos0))
          (max_le_nonnegative_upper hhPos hhPos0)
      · apply mul_le_mul_of_nonneg_left _ hquit
        exact add_le_add
          (add_le_add
            (max_le_nonnegative_upper hsNeg hsNeg0)
            (max_le_nonnegative_upper hpNeg hpNeg0))
          (max_le_nonnegative_upper hhNeg hhNeg0)

/-! ## One explicit finite Möbius label -/

/-- The positive-coefficient incidence term attached to one specific Möbius
coalition.  It is weighted by the probability that `who` actually played
Continue and that every other member of `coalition` Quits. -/
def quittingPlayedPositiveMobiusIncidenceTerm
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (coalition : Finset ι) : ℝ :=
  if who ∈ coalition then
    (root who false).toReal *
      max (quittingStageMobiusCoeff reward tail who coalition) 0 *
        ∏ player ∈ coalition.erase who, hazardOfRoot root player
  else 0

/-- The negative-coefficient incidence term attached to one specific Möbius
coalition.  It is weighted by the probability that `who` actually played
Quit and that every other member of `coalition` Quits. -/
def quittingPlayedNegativeMobiusIncidenceTerm
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (coalition : Finset ι) : ℝ :=
  if who ∈ coalition then
    (root who true).toReal *
      max (-quittingStageMobiusCoeff reward tail who coalition) 0 *
        ∏ player ∈ coalition.erase who, hazardOfRoot root player
  else 0

/-- The played-action signed Möbius incidence at one coalition.  For a fixed
coefficient at most one of its positive and negative summands is nonzero. -/
def quittingPlayedMobiusIncidenceTerm
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (coalition : Finset ι) : ℝ :=
  quittingPlayedPositiveMobiusIncidenceTerm
      reward tail root who coalition +
    quittingPlayedNegativeMobiusIncidenceTerm
      reward tail root who coalition

omit [Fintype ι] in
private theorem quittingPlayedPositiveMobiusIncidenceTerm_nonneg
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (coalition : Finset ι) :
    0 ≤ quittingPlayedPositiveMobiusIncidenceTerm
      reward tail root who coalition := by
  unfold quittingPlayedPositiveMobiusIncidenceTerm
  split_ifs
  · exact mul_nonneg
      (mul_nonneg ENNReal.toReal_nonneg (le_max_right _ 0))
      (mobiusMonomial_nonneg root who coalition)
  · exact le_rfl

omit [Fintype ι] in
private theorem quittingPlayedNegativeMobiusIncidenceTerm_nonneg
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (coalition : Finset ι) :
    0 ≤ quittingPlayedNegativeMobiusIncidenceTerm
      reward tail root who coalition := by
  unfold quittingPlayedNegativeMobiusIncidenceTerm
  split_ifs
  · exact mul_nonneg
      (mul_nonneg ENNReal.toReal_nonneg (le_max_right _ 0))
      (mobiusMonomial_nonneg root who coalition)
  · exact le_rfl

omit [Fintype ι] in
private theorem quittingPlayedMobiusIncidenceTerm_nonneg
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (coalition : Finset ι) :
    0 ≤ quittingPlayedMobiusIncidenceTerm reward tail root who coalition :=
  add_nonneg
    (quittingPlayedPositiveMobiusIncidenceTerm_nonneg
      (reward := reward) tail root who coalition)
    (quittingPlayedNegativeMobiusIncidenceTerm_nonneg
      (reward := reward) tail root who coalition)

/-- The full coordinate defect is bounded by the sum of the explicit
played-action Möbius incidences. -/
theorem quittingRootCoordinateNashDefect_le_sum_playedMobiusIncidenceTerm
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootCoordinateNashDefect reward tail root who ≤
      ∑ coalition : Finset ι,
        quittingPlayedMobiusIncidenceTerm reward tail root who coalition := by
  let G := quittingStageCenteredCoalGame reward tail who
  let x := hazardOfRoot root
  let derivative := G.coordinateDerivative x who
  let positiveCharge := ∑ coalition : Finset ι,
    if who ∈ coalition then
      max (G.unanimityCoeff coalition) 0 *
        ∏ player ∈ coalition.erase who, x player
    else 0
  let negativeCharge := ∑ coalition : Finset ι,
    if who ∈ coalition then
      max (-G.unanimityCoeff coalition) 0 *
        ∏ player ∈ coalition.erase who, x player
    else 0
  have hpositiveUpper : derivative ≤ positiveCharge := by
    dsimp [derivative, positiveCharge]
    unfold CoalGame.coordinateDerivative
    apply Finset.sum_le_sum
    intro coalition _
    split_ifs with hwho
    · exact mul_le_mul_of_nonneg_right
        (le_max_left _ 0) (mobiusMonomial_nonneg root who coalition)
    · exact le_rfl
  have hnegativeUpper : -derivative ≤ negativeCharge := by
    dsimp [derivative, negativeCharge]
    unfold CoalGame.coordinateDerivative
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro coalition _
    split_ifs with hwho
    · calc
        -(G.unanimityCoeff coalition *
            ∏ player ∈ coalition.erase who, x player) =
            (-G.unanimityCoeff coalition) *
              ∏ player ∈ coalition.erase who, x player := by ring
        _ ≤ max (-G.unanimityCoeff coalition) 0 *
              ∏ player ∈ coalition.erase who, x player :=
          mul_le_mul_of_nonneg_right
            (le_max_left _ 0) (mobiusMonomial_nonneg root who coalition)
    · simp
  have hpositiveNonneg : 0 ≤ positiveCharge := by
    dsimp [positiveCharge]
    exact Finset.sum_nonneg fun coalition _ => by
      split_ifs
      · exact mul_nonneg (le_max_right _ 0)
          (mobiusMonomial_nonneg root who coalition)
      · exact le_rfl
  have hnegativeNonneg : 0 ≤ negativeCharge := by
    dsimp [negativeCharge]
    exact Finset.sum_nonneg fun coalition _ => by
      split_ifs
      · exact mul_nonneg (le_max_right _ 0)
          (mobiusMonomial_nonneg root who coalition)
      · exact le_rfl
  have hcontinue : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  have hquit : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart,
    quittingRootEndpointDifference_eq_mobiusCoordinateDerivative]
  change (root who false).toReal * max derivative 0 +
      (root who true).toReal * max (-derivative) 0 ≤ _
  calc
    (root who false).toReal * max derivative 0 +
          (root who true).toReal * max (-derivative) 0 ≤
        (root who false).toReal * positiveCharge +
          (root who true).toReal * negativeCharge :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (max_le_nonnegative_upper hpositiveUpper hpositiveNonneg) hcontinue)
        (mul_le_mul_of_nonneg_left
          (max_le_nonnegative_upper hnegativeUpper hnegativeNonneg) hquit)
    _ = ∑ coalition : Finset ι,
          quittingPlayedMobiusIncidenceTerm reward tail root who coalition := by
      dsimp [positiveCharge, negativeCharge, G, x]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro coalition _
      unfold quittingPlayedMobiusIncidenceTerm
        quittingPlayedPositiveMobiusIncidenceTerm
        quittingPlayedNegativeMobiusIncidenceTerm quittingStageMobiusCoeff
      split_ifs <;> ring

/-- **Quantitative finite Möbius label.**  Positive coordinate defect selects
one explicit coalition, one coefficient sign, and hence one played-action
cylinder.  The coalition is classified as singleton, pair, or higher, and
the loss in selecting one label is exactly the number `card (Finset ι)` of
Boolean coalitions.  This division-free form is suited to later time
pigeonhole arguments. -/
theorem exists_playedMobiusIncidenceLabel_of_coordinateNashDefect_pos
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hdefect : 0 < quittingRootCoordinateNashDefect reward tail root who) :
    ∃ coalition : Finset ι,
      who ∈ coalition ∧
      (coalition.card = 1 ∨ coalition.card = 2 ∨ 3 ≤ coalition.card) ∧
      0 < quittingPlayedMobiusIncidenceTerm
        reward tail root who coalition ∧
      quittingRootCoordinateNashDefect reward tail root who ≤
        (Fintype.card (Finset ι) : ℝ) *
          quittingPlayedMobiusIncidenceTerm reward tail root who coalition ∧
      ((0 < quittingPlayedPositiveMobiusIncidenceTerm
            reward tail root who coalition ∧
          quittingRootCoordinateNashDefect reward tail root who ≤
            (Fintype.card (Finset ι) : ℝ) *
              quittingPlayedPositiveMobiusIncidenceTerm
                reward tail root who coalition) ∨
        (0 < quittingPlayedNegativeMobiusIncidenceTerm
            reward tail root who coalition ∧
          quittingRootCoordinateNashDefect reward tail root who ≤
            (Fintype.card (Finset ι) : ℝ) *
              quittingPlayedNegativeMobiusIncidenceTerm
                reward tail root who coalition)) := by
  let term : Finset ι → ℝ := fun coalition =>
    quittingPlayedMobiusIncidenceTerm reward tail root who coalition
  obtain ⟨coalition, _hmem, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Finset ι)) term
      Finset.univ_nonempty
  have hsumLe : (∑ candidate : Finset ι, term candidate) ≤
      (Fintype.card (Finset ι) : ℝ) * term coalition := by
    calc
      (∑ candidate : Finset ι, term candidate) ≤
          ∑ _candidate : Finset ι, term coalition :=
        Finset.sum_le_sum fun candidate _ =>
          hmax candidate (Finset.mem_univ candidate)
      _ = (Fintype.card (Finset ι) : ℝ) * term coalition := by
        simp [nsmul_eq_mul]
  have hquantitative : quittingRootCoordinateNashDefect reward tail root who ≤
      (Fintype.card (Finset ι) : ℝ) * term coalition :=
    (quittingRootCoordinateNashDefect_le_sum_playedMobiusIncidenceTerm
      (reward := reward) tail root who).trans hsumLe
  have htermNonneg : 0 ≤ term coalition :=
    quittingPlayedMobiusIncidenceTerm_nonneg
      (reward := reward) tail root who coalition
  have htermPos : 0 < term coalition := by
    rcases htermNonneg.eq_or_lt with hzero | hpositive
    · rw [← hzero, mul_zero] at hquantitative
      linarith
    · exact hpositive
  have hwho : who ∈ coalition := by
    by_contra hnot
    have hzero : term coalition = 0 := by
      simp [term, quittingPlayedMobiusIncidenceTerm,
        quittingPlayedPositiveMobiusIncidenceTerm,
        quittingPlayedNegativeMobiusIncidenceTerm, hnot]
    rw [hzero] at htermPos
    linarith
  have hgrade : coalition.card = 1 ∨ coalition.card = 2 ∨
      3 ≤ coalition.card := by
    have hcard : 0 < coalition.card := Finset.card_pos.mpr ⟨who, hwho⟩
    omega
  refine ⟨coalition, hwho, hgrade, htermPos, hquantitative, ?_⟩
  by_cases hcoeff : 0 ≤ quittingStageMobiusCoeff reward tail who coalition
  · have hnegativeZero : quittingPlayedNegativeMobiusIncidenceTerm
        reward tail root who coalition = 0 := by
      unfold quittingPlayedNegativeMobiusIncidenceTerm
      rw [if_pos hwho, max_eq_right (neg_nonpos.mpr hcoeff)]
      ring
    have htermEq : term coalition =
        quittingPlayedPositiveMobiusIncidenceTerm
          reward tail root who coalition := by
      simp [term, quittingPlayedMobiusIncidenceTerm, hnegativeZero]
    left
    rw [htermEq] at htermPos hquantitative
    exact ⟨htermPos, hquantitative⟩
  · have hpositiveZero : quittingPlayedPositiveMobiusIncidenceTerm
        reward tail root who coalition = 0 := by
      unfold quittingPlayedPositiveMobiusIncidenceTerm
      rw [if_pos hwho, max_eq_right (le_of_not_ge hcoeff)]
      ring
    have htermEq : term coalition =
        quittingPlayedNegativeMobiusIncidenceTerm
          reward tail root who coalition := by
      simp [term, quittingPlayedMobiusIncidenceTerm, hpositiveZero]
    right
    rw [htermEq] at htermPos hquantitative
    exact ⟨htermPos, hquantitative⟩

/-! ## Finite-cutoff time and label pigeonhole -/

/-- Boolean orientation of a played Möbius incidence: `false` selects the
Continue-weighted positive coefficient and `true` the Quit-weighted negative
coefficient. -/
def quittingOrientedPlayedMobiusIncidenceTerm
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (coalition : Finset ι) (orientation : Bool) : ℝ :=
  if orientation then
    quittingPlayedNegativeMobiusIncidenceTerm
      reward tail root who coalition
  else
    quittingPlayedPositiveMobiusIncidenceTerm
      reward tail root who coalition

omit [Fintype ι] in
private theorem quittingOrientedPlayedMobiusIncidenceTerm_nonneg
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (coalition : Finset ι) (orientation : Bool) :
    0 ≤ quittingOrientedPlayedMobiusIncidenceTerm
      reward tail root who coalition orientation := by
  cases orientation <;>
    simp [quittingOrientedPlayedMobiusIncidenceTerm,
      quittingPlayedPositiveMobiusIncidenceTerm_nonneg
        (reward := reward) tail root who coalition,
      quittingPlayedNegativeMobiusIncidenceTerm_nonneg
        (reward := reward) tail root who coalition]

/-- Time-summed incidence of one fixed player/coalition/orientation label,
restricted to dates at which the supplied selector chooses that player. -/
def quittingPlayedMobiusIncidenceOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tails : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (liveWeight : ℕ → ℝ) (owner : ℕ → ι) (cutoff : ℕ)
    (who : ι) (coalition : Finset ι) (orientation : Bool) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    if who = owner time then
      liveWeight time *
        quittingOrientedPlayedMobiusIncidenceTerm
          reward (tails time) (roots time) who coalition orientation
    else 0

/-- The live-weighted defect occupation is bounded by the sum over all fixed
player/coalition/orientation occupations. -/
theorem sum_liveWeight_mul_coordinateNashDefect_le_sum_incidenceOccupations
    (tails : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (liveWeight : ℕ → ℝ) (owner : ℕ → ι) (cutoff : ℕ)
    (hlive : ∀ time, 0 ≤ liveWeight time) :
    (∑ time ∈ Finset.range cutoff,
        liveWeight time *
          quittingRootCoordinateNashDefect
            reward (tails time) (roots time) (owner time)) ≤
      ∑ label : ι × Finset ι × Bool,
        quittingPlayedMobiusIncidenceOccupation reward tails roots
          liveWeight owner cutoff label.1 label.2.1 label.2.2 := by
  let row : ℕ → ι → Finset ι → Bool → ℝ :=
    fun time who coalition orientation =>
      if who = owner time then
        liveWeight time *
          quittingOrientedPlayedMobiusIncidenceTerm
            reward (tails time) (roots time) who coalition orientation
      else 0
  have htime : ∀ time,
      liveWeight time *
          quittingRootCoordinateNashDefect
            reward (tails time) (roots time) (owner time) ≤
        ∑ label : ι × Finset ι × Bool,
          row time label.1 label.2.1 label.2.2 := by
    intro time
    have hlocal :=
      quittingRootCoordinateNashDefect_le_sum_playedMobiusIncidenceTerm
        (reward := reward) (tails time) (roots time) (owner time)
    have hscaled := mul_le_mul_of_nonneg_left hlocal (hlive time)
    rw [Finset.mul_sum] at hscaled
    calc
      liveWeight time * quittingRootCoordinateNashDefect
          reward (tails time) (roots time) (owner time) ≤
          ∑ coalition : Finset ι,
            liveWeight time * quittingPlayedMobiusIncidenceTerm
              reward (tails time) (roots time) (owner time) coalition := hscaled
      _ = ∑ label : ι × Finset ι × Bool,
            row time label.1 label.2.1 label.2.2 := by
        simp only [Fintype.sum_prod_type]
        apply Eq.symm
        calc
          (∑ who, ∑ coalition, ∑ orientation,
              row time who coalition orientation) =
              ∑ coalition, ∑ orientation,
                row time (owner time) coalition orientation := by
            simp [row]
          _ = ∑ coalition : Finset ι,
              liveWeight time * quittingPlayedMobiusIncidenceTerm
                reward (tails time) (roots time) (owner time) coalition := by
            apply Finset.sum_congr rfl
            intro coalition _
            rw [Fintype.sum_bool]
            simp [row, quittingOrientedPlayedMobiusIncidenceTerm,
              quittingPlayedMobiusIncidenceTerm]
            ring
  calc
    (∑ time ∈ Finset.range cutoff,
        liveWeight time * quittingRootCoordinateNashDefect
          reward (tails time) (roots time) (owner time)) ≤
      ∑ time ∈ Finset.range cutoff,
        ∑ label : ι × Finset ι × Bool,
          row time label.1 label.2.1 label.2.2 :=
        Finset.sum_le_sum fun time _ => htime time
    _ = ∑ label : ι × Finset ι × Bool,
        quittingPlayedMobiusIncidenceOccupation reward tails roots
          liveWeight owner cutoff label.1 label.2.1 label.2.2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro label _
      rfl

/-- **Finite-cutoff fixed-label pigeonhole.**  A positive lower bound on the
live-weighted coordinate-defect occupation selects one fixed player,
coalition, and orientation whose time-summed played Möbius incidence carries
that lower bound up to the exact number of possible labels.  The coalition
retains its singleton/pair/higher grade.  This is an occupation label only;
it does not assert state matching, persistence beyond the cutoff, or a legal
deviation/cycle. -/
theorem exists_fixed_playedMobiusIncidenceOccupation_of_defectOccupation
    (tails : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (liveWeight : ℕ → ℝ) (owner : ℕ → ι) (cutoff : ℕ)
    (lower : ℝ) (hlower : 0 < lower)
    (hlive : ∀ time, 0 ≤ liveWeight time)
    (hoccupation : lower ≤
      ∑ time ∈ Finset.range cutoff,
        liveWeight time * quittingRootCoordinateNashDefect
          reward (tails time) (roots time) (owner time)) :
    ∃ who : ι, ∃ coalition : Finset ι, ∃ orientation : Bool,
      who ∈ coalition ∧
      (coalition.card = 1 ∨ coalition.card = 2 ∨ 3 ≤ coalition.card) ∧
      0 < quittingPlayedMobiusIncidenceOccupation reward tails roots
        liveWeight owner cutoff who coalition orientation ∧
      lower ≤
        (Fintype.card (ι × Finset ι × Bool) : ℝ) *
          quittingPlayedMobiusIncidenceOccupation reward tails roots
            liveWeight owner cutoff who coalition orientation := by
  let occupation : ι × Finset ι × Bool → ℝ := fun label =>
    quittingPlayedMobiusIncidenceOccupation reward tails roots
      liveWeight owner cutoff label.1 label.2.1 label.2.2
  have htotal : lower ≤ ∑ label : ι × Finset ι × Bool, occupation label :=
    hoccupation.trans
      (sum_liveWeight_mul_coordinateNashDefect_le_sum_incidenceOccupations
        (reward := reward) tails roots liveWeight owner cutoff hlive)
  obtain ⟨label, _hlabel, hmax⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (ι × Finset ι × Bool)) occupation
      ⟨(owner 0, (∅, false)), Finset.mem_univ _⟩
  have hsumLe : (∑ candidate : ι × Finset ι × Bool, occupation candidate) ≤
      (Fintype.card (ι × Finset ι × Bool) : ℝ) * occupation label := by
    calc
      (∑ candidate : ι × Finset ι × Bool, occupation candidate) ≤
          ∑ _candidate : ι × Finset ι × Bool, occupation label :=
        Finset.sum_le_sum fun candidate _ =>
          hmax candidate (Finset.mem_univ candidate)
      _ = (Fintype.card (ι × Finset ι × Bool) : ℝ) * occupation label := by
        simp [nsmul_eq_mul]
  have hquantitative : lower ≤
      (Fintype.card (ι × Finset ι × Bool) : ℝ) * occupation label :=
    htotal.trans hsumLe
  have hoccupationNonneg : 0 ≤ occupation label := by
    unfold occupation quittingPlayedMobiusIncidenceOccupation
    exact Finset.sum_nonneg fun time _ => by
      split_ifs
      · exact mul_nonneg (hlive time)
          (quittingOrientedPlayedMobiusIncidenceTerm_nonneg
            (reward := reward) (tails time) (roots time)
              label.1 label.2.1 label.2.2)
      · exact le_rfl
  have hoccupationPos : 0 < occupation label := by
    rcases hoccupationNonneg.eq_or_lt with hzero | hpositive
    · rw [← hzero, mul_zero] at hquantitative
      linarith
    · exact hpositive
  have hmember : label.1 ∈ label.2.1 := by
    by_contra hnot
    have hzero : occupation label = 0 := by
      unfold occupation quittingPlayedMobiusIncidenceOccupation
      apply Finset.sum_eq_zero
      intro time _
      split_ifs with howner
      · have htermZero : quittingOrientedPlayedMobiusIncidenceTerm
            reward (tails time) (roots time) label.1 label.2.1 label.2.2 = 0 := by
          cases label.2.2 <;>
            simp [quittingOrientedPlayedMobiusIncidenceTerm,
              quittingPlayedPositiveMobiusIncidenceTerm,
              quittingPlayedNegativeMobiusIncidenceTerm, hnot]
        rw [htermZero, mul_zero]
      · rfl
    rw [hzero] at hoccupationPos
    linarith
  have hgrade : label.2.1.card = 1 ∨ label.2.1.card = 2 ∨
      3 ≤ label.2.1.card := by
    have hcard : 0 < label.2.1.card :=
      Finset.card_pos.mpr ⟨label.1, hmember⟩
    omega
  exact ⟨label.1, label.2.1, label.2.2, hmember, hgrade,
    hoccupationPos, hquantitative⟩

end GameTheory
