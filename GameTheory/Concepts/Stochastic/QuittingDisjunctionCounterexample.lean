/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCycleIsolatedCoordinate
import GameTheory.Concepts.Stochastic.QuittingZeroSoloDisjunct

/-!
# A weight outside both disjuncts of the finite-quitting reduction

`QuittingZeroSoloDisjunct.lean` reduces the existence of a uniform
equilibrium payoff to the disjunction

    `IsQuittingZeroSolo reward ∨ HasAdmissibleAbsorbingQuittingCycle reward`.

Whether that disjunction is *exhaustive* was once recorded in this repository
as an open declaration.  It is not: this file exhibits a two-coordinate weight
satisfying neither branch, machine-checked.

## The weight

With `false` for coordinate `1` and `true` for coordinate `2`,

    `r({1}) = (1, -1)`,  `r({2}) = (1, -1)`,  `r({1,2}) = (0, 1)`.

Note `r_1({1}) = 1 > 0`, so the weight is not zero-solo: the first disjunct
fails at once (`not_isQuittingZeroSolo_reward`).

The second disjunct fails for a subtler reason.  *Absorbing complementary
cycles do exist here*: the single row in which coordinate `2` quits surely and
coordinate `1` is silent, run against the value `(1, -1)`, is an
`IsQuittingCyclicContinuationBlock` (`witnessBlock_isCyclicContinuationBlock`).
What fails is admissibility.  At that row coordinate `1` never quits, so the
deleted survival product at coordinate `2` is `1`, and `r_2({2}) = -1 < 0`;
by `quittingCyclicContinuationBlock_mismatch_eq_of_isolated` the anchored
companion mismatch is exactly `1` (`witness_mismatch_eq_one`), not `0`.

Moreover this is not an accident of the chosen row.  *Every* absorbing
complementary cycle for this weight, of every period, has coordinate `1`
silent at every phase (`isQuittingIsolatedWindow_of_cyclicContinuationBlock`),
so no cycle is admissible and the second disjunct fails outright
(`not_hasAdmissibleAbsorbingQuittingCycle_reward`).

## Why coordinate `1` must be silent

Write `p_k`, `q_k` for the two quit probabilities at phase `k` and put
`v_k = z_k(2) + 1`, the coordinate-`2` value shifted by `-r_2({1}) = 1`.  The
one-stage law becomes

    `v_k = 2 p_k q_k + (1 - p_k)(1 - q_k) v_{k+1}`,

whose stop term `2 p_k` is nonnegative and strictly positive exactly when
coordinate `1` is active.  Coordinate `2`'s two exact-Nash complementarity
clauses read off as `2 p_k ≤ v_k` and `(1 - p_k) v_{k+1} ≤ v_k`; the first
forces `v_k ≤ (1 - p_k) v_{k+1}` whenever `q_k < 1`.  And `q_k = 1` is
impossible while coordinate `1` is active, because `r_1({1,2}) = 0 < 1 =
r_1({2})`: against a surely-quitting opponent, quitting costs coordinate `1`
exactly `1`.  So each phase with `p_k > 0` *strictly increases* `v`, and `v`
never decreases; a cycle returns `v` to its starting value, which no strict
increase permits.

## What this does not say

Nothing here claims this weight has no uniform equilibrium payoff — it has two
coordinates, and one exists by other means.  The claim is only that the weight
lies outside the *carrier* of the stated disjunction, so the disjunction is not
exhaustive and cannot be upgraded to an unconditional existence theorem as it
stands.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

namespace QuittingDisjunctionCounterexample

/-! ## The weight -/

/-- The counterexample weight `r({1}) = (1, -1)`, `r({2}) = (1, -1)`,
`r({1,2}) = (0, 1)`, with `false` for coordinate `1` and `true` for
coordinate `2`. -/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if false ∈ quitters.1 then
      if true ∈ quitters.1 then
        (if who then 1 else 0)
      else
        (if who then -1 else 1)
    else
      (if who then -1 else 1)

@[simp] theorem reward_singleton_false :
    reward (quittingSingletonTerminal false) = fun who ↦ if who then (-1 : ℝ) else 1 := by
  funext who
  simp [reward, quittingSingletonTerminal]

@[simp] theorem reward_singleton_true :
    reward (quittingSingletonTerminal true) = fun who ↦ if who then (-1 : ℝ) else 1 := by
  funext who
  simp [reward, quittingSingletonTerminal]

/-- The remaining table entry: `r({1,2}) = (0, 1)`.  Together with
`reward_singleton_false` and `reward_singleton_true` this pins all six
numbers of the weight. -/
@[simp] theorem reward_doubleton :
    reward ⟨{false, true}, by decide⟩ = fun who ↦ if who then (1 : ℝ) else 0 := by
  funext who
  simp [reward]

theorem reward_singleton_false_self :
    reward (quittingSingletonTerminal false) false = 1 := by simp

theorem reward_singleton_true_self :
    reward (quittingSingletonTerminal true) true = -1 := by simp

/-! ## Item 1: the weight is not zero-solo -/

/-- **The first disjunct fails.**  Coordinate `1` has a strictly positive
solo-quit reward `r_1({1}) = 1`. -/
theorem not_isQuittingZeroSolo_reward : ¬ IsQuittingZeroSolo reward := by
  intro hzero
  have h := hzero false
  rw [reward_singleton_false_self] at h
  norm_num at h

/-! ## Exact endpoint formulas -/

theorem false_quitPayoff (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff reward tail root false =
      1 - (root true true).toReal := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  have hc : (root true false).toReal = 1 - (root true true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, hc]

theorem false_continuePayoff (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootContinuePayoff reward tail root false =
      (root true true).toReal +
        (1 - (root true true).toReal) * tail false := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  have hc : (root true false).toReal = 1 - (root true true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, hc]

theorem true_quitPayoff (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff reward tail root true =
      2 * (root false true).toReal - 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hc : (root false false).toReal = 1 - (root false true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, hc]
  ring

theorem true_continuePayoff (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootContinuePayoff reward tail root true =
      -(root false true).toReal +
        (1 - (root false true).toReal) * tail true := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hc : (root false false).toReal = 1 - (root false true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, hc]

/-- Coordinate `1`'s endpoint gap: quitting is worth `1 - q`, continuing is
worth `q + (1 - q) z_1`. -/
theorem false_endpointDifference (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward tail root false =
      1 - 2 * (root true true).toReal -
        (1 - (root true true).toReal) * tail false := by
  rw [quittingRootEndpointDifference, false_quitPayoff, false_continuePayoff]
  ring

/-- Coordinate `2`'s endpoint gap, written in the shifted value
`v = z_2 + 1`: it is `2p - (1 - p) v`. -/
theorem true_endpointDifference (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward tail root true =
      2 * (root false true).toReal -
        (1 - (root false true).toReal) * (tail true + 1) := by
  rw [quittingRootEndpointDifference, true_quitPayoff, true_continuePayoff]
  ring

/-- **The shifted one-stage law at coordinate `2`.**  With `v = z_2 + 1` the
backward step is `v_k = 2 p q + (1 - p)(1 - q) v_{k+1}`; the stop term `2 p q`
is nonnegative, which is the whole engine of this file. -/
theorem shiftedValue_eq (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootSuccessorPayoff reward tail root true + 1 =
      2 * (root false true).toReal * (root true true).toReal +
        (1 - (root false true).toReal) * (1 - (root true true).toReal) *
          (tail true + 1) := by
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  rw [quittingRootSuccessorPayoff_eq_endpointMix, true_quitPayoff,
    true_continuePayoff]
  have hc : (root true false).toReal = 1 - (root true true).toReal := by linarith
  rw [hc]
  ring

/-! ## Item 2: an absorbing complementary cycle exists

The single row in which coordinate `2` quits surely and coordinate `1` is
silent reproduces the value `(1, -1)` and absorbs with probability one.  So the
*cycle* clause of the second disjunct is perfectly satisfiable on this weight;
it is admissibility that will fail.
-/

/-- The witness row: coordinate `1` continues surely, coordinate `2` quits
surely. -/
def witnessRoot : Bool → PMF Bool :=
  fun who ↦ if who then PMF.pure true else PMF.pure false

/-- The witness value `(1, -1)`, which is also `r({2})` (and `r({1})`). -/
def witnessValue : Payoff Bool := fun who ↦ if who then (-1 : ℝ) else 1

@[simp] theorem witnessRoot_false_true : (witnessRoot false true).toReal = 0 := by
  simp [witnessRoot]

@[simp] theorem witnessRoot_false_false : (witnessRoot false false).toReal = 1 := by
  simp [witnessRoot]

@[simp] theorem witnessRoot_true_true : (witnessRoot true true).toReal = 1 := by
  simp [witnessRoot]

@[simp] theorem witnessRoot_true_false : (witnessRoot true false).toReal = 0 := by
  simp [witnessRoot]

@[simp] theorem witnessValue_false : witnessValue false = 1 := rfl

@[simp] theorem witnessValue_true : witnessValue true = -1 := rfl

/-- The witness row reproduces the witness value: absorbing into `{2}` with
probability one pays exactly `r({2}) = (1, -1)`. -/
theorem witnessValue_eq_successor :
    witnessValue = quittingRootSuccessorPayoff reward witnessValue witnessRoot := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  cases who
  · rw [false_quitPayoff, false_continuePayoff]
    simp
  · rw [true_quitPayoff, true_continuePayoff]
    simp

/-- The witness row is exactly (`ε = 0`) endpoint Nash against the witness
value: coordinate `1` has gap `-1 ≤ 0` at quit probability `0`, and
coordinate `2` is exactly indifferent. -/
theorem witnessRoot_isEndpointNash :
    IsεQuittingRootEndpointNash reward witnessValue 0 witnessRoot := by
  intro who
  cases who
  · rw [false_endpointDifference]
    simp
  · rw [true_endpointDifference]
    simp

/-- The witness row absorbs with probability one. -/
theorem witnessRoot_absorptionMass_pos :
    0 < quittingRootAbsorptionMass witnessRoot := by
  rw [quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability, Fintype.prod_bool,
    witnessRoot_false_false, witnessRoot_true_false]
  norm_num

theorem abs_witnessValue_le :
    ∀ who, |witnessValue who| ≤ quittingRewardBound reward := by
  intro who
  have h := abs_reward_le_quittingRewardBound reward
    (quittingSingletonTerminal true) who
  rwa [reward_singleton_true] at h

/-- The length-one block sitting at the witness row. -/
def witnessBlock : QuittingFiniteNashBellmanPath Bool 1 :=
  quittingRowBlock witnessValue witnessRoot

/-- **Item 2.**  The witness row is an absorbing exact cyclic continuation
block: the *cycle* clause of the second disjunct is satisfiable on this
weight. -/
theorem witnessBlock_isCyclicContinuationBlock :
    IsQuittingCyclicContinuationBlock reward witnessValue 1 witnessBlock :=
  quittingRowBlock_isQuittingCyclicContinuationBlock reward witnessValue
    witnessRoot abs_witnessValue_le witnessValue_eq_successor
    witnessRoot_isEndpointNash witnessRoot_absorptionMass_pos

/-! ## Item 3: the witness cycle is not admissible -/

/-- Coordinate `2` is isolated at the witness row: its only opponent,
coordinate `1`, continues surely. -/
theorem witnessBlock_isIsolated :
    IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots 1 witnessBlock) true 1 := by
  intro time htime
  have htime0 : time = 0 := by omega
  subst htime0
  rw [quittingFiniteNashBellmanPathRoots_of_lt 1 _ 0 (by omega), witnessBlock,
    quittingRootOfSimplex_quittingRowBlock]
  intro other hother
  cases other with
  | false => rfl
  | true => exact absurd rfl hother

/-- Consequently the deleted survival product at coordinate `2` is exactly
one: the contraction branch of admissibility is unavailable here. -/
theorem witnessBlock_opponentSurvivalWeight_eq_one :
    quittingOpponentSurvivalWeight
      (quittingFiniteNashBellmanPathRoots 1 witnessBlock) true 0 1 = 1 :=
  (isQuittingIsolatedWindow_iff_opponentSurvivalWeight_eq_one _ true 1).mp
    witnessBlock_isIsolated

@[simp] theorem soloQuitCap_true :
    quittingPositiveSingletonDebtCap reward true = 0 := by
  rw [quittingSoloQuitAnchor_eq, reward_singleton_true_self]
  norm_num

theorem witness_tendsto_iterate_soloQuitAnchor :
    Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward
          (quittingFiniteNashBellmanPathRoots 1 witnessBlock) true 0 1)^[N]
          (quittingPositiveSingletonDebtCap reward true))
      Filter.atTop (nhds (quittingPositiveSingletonDebtCap reward true)) :=
  tendsto_iterate_soloQuitAnchor_of_isolated reward _ true 1 witnessBlock_isIsolated

/-- **Item 3, the mismatch.**  The anchored companion mismatch of the witness
cycle at coordinate `2` is exactly `1`, computed by the machine-checked
characterization `quittingCyclicContinuationBlock_mismatch_eq_of_isolated`
rather than by recomputing the companion orbit. -/
theorem witness_mismatch_eq_one :
    quittingPositiveSingletonDebtCap reward true - witnessValue true = 1 := by
  rw [quittingCyclicContinuationBlock_mismatch_eq_of_isolated reward witnessValue
    1 witnessBlock witnessBlock_isCyclicContinuationBlock witnessBlock_isIsolated
    (quittingPositiveSingletonDebtCap reward true)
    witness_tendsto_iterate_soloQuitAnchor, reward_singleton_true_self]
  norm_num

/-- **Item 3.**  The witness cycle is not admissible: its deleted survival
product at coordinate `2` is `1` and `r_2({2}) = -1 < 0`, so neither disjunct
of `IsQuittingCycleZeroDeviationMismatchAt` holds there. -/
theorem not_isQuittingCycleAdmissible_witnessBlock :
    ¬ IsQuittingCycleAdmissible reward
      (quittingCyclicContinuationBlockCycle 0 witnessBlock) := by
  intro hadmissible
  have hcycle : quittingCyclicContinuationBlockCycle 0 witnessBlock 0 =
      witnessRoot := by
    rw [quittingCyclicContinuationBlockCycle, witnessBlock,
      quittingRootOfSimplex_quittingRowBlock]
  have hmass : quittingStationaryFixedOpponentsContinueMass witnessRoot true = 1 := by
    change quittingRootDeletedContinueMass witnessRoot true = 1
    refine quittingRootDeletedContinueMass_eq_one_of_isolated ?_
    intro other hother
    cases other with
    | false => rfl
    | true => exact absurd rfl hother
  rcases hadmissible true with hcontract | hnonneg
  · rw [Fin.prod_univ_one, hcycle, hmass] at hcontract
    exact lt_irrefl 1 hcontract
  · rw [reward_singleton_true_self] at hnonneg
    norm_num at hnonneg

/-! ## Item 4, one stage: what exact complementarity forces at a single row

All four inequalities below are read off the two exact-Nash complementarity
clauses of `IsεQuittingRootEndpointNash` at `ε = 0`, together with the shifted
one-stage law `shiftedValue_eq`.  Nothing about cycles is used yet.
-/

theorem quitProbability_nonneg (root : Bool → PMF Bool) (who : Bool) :
    0 ≤ (root who true).toReal := ENNReal.toReal_nonneg

theorem quitProbability_le_one (root : Bool → PMF Bool) (who : Bool) :
    (root who true).toReal ≤ 1 := by
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hnn := ENNReal.toReal_nonneg (a := root who false)
  linarith

/-- **The stop bound.**  Coordinate `2`'s first complementarity clause says the
shifted value dominates the stop term `2p`. -/
theorem two_mul_quitProbability_le_shiftedValue
    (tail : Payoff Bool) (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) :
    2 * (root false true).toReal ≤
      quittingRootSuccessorPayoff reward tail root true + 1 := by
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  have hclause := (hnash true).1
  rw [true_endpointDifference] at hclause
  have hc : (root true false).toReal = 1 - (root true true).toReal := by linarith
  rw [hc] at hclause
  have hid := shiftedValue_eq tail root
  have hkey : quittingRootSuccessorPayoff reward tail root true + 1 -
      2 * (root false true).toReal =
      -((1 - (root true true).toReal) *
        (2 * (root false true).toReal -
          (1 - (root false true).toReal) * (tail true + 1))) := by
    rw [hid]; ring
  linarith

/-- **The transport bound.**  Coordinate `2`'s second complementarity clause
says the shifted value dominates the transported continuation. -/
theorem mul_shiftedTail_le_shiftedValue
    (tail : Payoff Bool) (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) :
    (1 - (root false true).toReal) * (tail true + 1) ≤
      quittingRootSuccessorPayoff reward tail root true + 1 := by
  have hclause := (hnash true).2
  rw [true_endpointDifference] at hclause
  simp only [neg_zero] at hclause
  have hid := shiftedValue_eq tail root
  have hkey : quittingRootSuccessorPayoff reward tail root true + 1 -
      (1 - (root false true).toReal) * (tail true + 1) =
      (root true true).toReal *
        (2 * (root false true).toReal -
          (1 - (root false true).toReal) * (tail true + 1)) := by
    rw [hid]; ring
  linarith

/-- **Coordinate `1` cannot be active against a surely-quitting opponent.**
This is where `r_1({1,2}) = 0 < 1 = r_1({2})` enters: if coordinate `2` quits
with probability one, coordinate `1`'s quit gap is exactly `-1`, so its
complementarity clause forces silence. -/
theorem quitProbability_false_eq_zero_of_quitProbability_true_eq_one
    (tail : Payoff Bool) (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hq : (root true true).toReal = 1) :
    (root false true).toReal = 0 := by
  have hclause := (hnash false).2
  rw [false_endpointDifference, hq] at hclause
  simp only [neg_zero] at hclause
  have hsimp : (1 : ℝ) - 2 * 1 - (1 - 1) * tail false = -1 := by ring
  rw [hsimp] at hclause
  have hp := quitProbability_nonneg root false
  linarith

/-- **The strict transport law.**  Away from a surely-quitting coordinate `2`,
the stop bound turns into an upper bound: the shifted value is *dominated* by
the transported continuation. -/
theorem shiftedValue_le_mul_of_quitProbability_true_lt_one
    (tail : Payoff Bool) (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hq : (root true true).toReal < 1) :
    quittingRootSuccessorPayoff reward tail root true + 1 ≤
      (1 - (root false true).toReal) * (tail true + 1) := by
  have hi := two_mul_quitProbability_le_shiftedValue tail root hnash
  have hq0 := quitProbability_nonneg root true
  have hid := shiftedValue_eq tail root
  have hkey : (1 - (root true true).toReal) *
        (quittingRootSuccessorPayoff reward tail root true + 1) -
      (1 - (root true true).toReal) *
        ((1 - (root false true).toReal) * (tail true + 1)) =
      -((root true true).toReal *
        (quittingRootSuccessorPayoff reward tail root true + 1 -
          2 * (root false true).toReal)) := by
    rw [hid]; ring
  have haux : 0 ≤ (root true true).toReal *
      (quittingRootSuccessorPayoff reward tail root true + 1 -
        2 * (root false true).toReal) :=
    mul_nonneg hq0 (by linarith)
  have hmul : (1 - (root true true).toReal) *
      (quittingRootSuccessorPayoff reward tail root true + 1) ≤
      (1 - (root true true).toReal) *
        ((1 - (root false true).toReal) * (tail true + 1)) := by linarith
  exact le_of_mul_le_mul_left hmul (by linarith)

/-- **The shifted coordinate-`2` value never decreases backwards.** -/
theorem shiftedValue_le_shiftedTail
    (tail : Payoff Bool) (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (htail : 0 ≤ tail true + 1) :
    quittingRootSuccessorPayoff reward tail root true + 1 ≤ tail true + 1 := by
  have hp0 := quitProbability_nonneg root false
  rcases lt_or_eq_of_le (quitProbability_le_one root true) with hq | hq
  · have hC := shiftedValue_le_mul_of_quitProbability_true_lt_one tail root hnash hq
    nlinarith [mul_nonneg hp0 htail]
  · have hp := quitProbability_false_eq_zero_of_quitProbability_true_eq_one
      tail root hnash hq
    have hid := shiftedValue_eq tail root
    rw [hp, hq] at hid
    norm_num at hid
    linarith

/-- **A phase with coordinate `1` active strictly increases it.** -/
theorem shiftedValue_lt_shiftedTail
    (tail : Payoff Bool) (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (htail : 0 ≤ tail true + 1)
    (hpos : 0 < (root false true).toReal) :
    quittingRootSuccessorPayoff reward tail root true + 1 < tail true + 1 := by
  have hp0 := quitProbability_nonneg root false
  have hq : (root true true).toReal < 1 := by
    refine lt_of_le_of_ne (quitProbability_le_one root true) fun hq ↦ ?_
    have hp := quitProbability_false_eq_zero_of_quitProbability_true_eq_one
      tail root hnash hq
    linarith
  have hC := shiftedValue_le_mul_of_quitProbability_true_lt_one tail root hnash hq
  have hi := two_mul_quitProbability_le_shiftedValue tail root hnash
  have hTpos : 0 < tail true + 1 := by nlinarith [mul_nonneg hp0 htail]
  nlinarith [mul_pos hpos hTpos]

/-! ## Item 4: every absorbing complementary cycle silences coordinate `1` -/

/-- The shifted coordinate-`2` value of a block: `v = z_2 + 1`, the
coordinate-`2` value measured from `r_2({1}) = -1`. -/
def blockShiftedValue (period : ℕ)
    (block : QuittingFiniteNashBellmanPath Bool (period + 1)) (time : ℕ) : ℝ :=
  quittingFiniteNashBellmanPathValue (period + 1) block time true + 1

/-- Coordinate `1`'s quit probability at a phase of a block. -/
def blockQuitProbability (period : ℕ)
    (block : QuittingFiniteNashBellmanPath Bool (period + 1)) (time : ℕ) : ℝ :=
  (quittingFiniteNashBellmanPathRoots (period + 1) block time false true).toReal

section Cycle

variable (terminal : Payoff Bool) (period : ℕ)
  (block : QuittingFiniteNashBellmanPath Bool (period + 1))
  (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)

include hblock

/-- The shifted value is nonnegative before the cutoff: it dominates the
nonnegative stop term `2p`. -/
theorem blockShiftedValue_nonneg_of_lt (time : ℕ) (htime : time < period + 1) :
    0 ≤ blockShiftedValue period block time := by
  have hbell := quittingAnchoredPathValue_eq_successor reward terminal (period + 1)
    block hblock.1 time htime
  have hnash := quittingAnchoredPathRoots_isZeroEndpointNash reward terminal
    (period + 1) block hblock.1 time htime
  have hi := two_mul_quitProbability_le_shiftedValue _ _ hnash
  have hp := quitProbability_nonneg
    (quittingFiniteNashBellmanPathRoots (period + 1) block time) false
  simp only [blockShiftedValue]
  rw [congrFun hbell true]
  linarith

/-- The block's cyclic clause: the shifted value at the cutoff is the shifted
value at the origin. -/
theorem blockShiftedValue_at_cutoff :
    blockShiftedValue period block (period + 1) = blockShiftedValue period block 0 := by
  simp only [blockShiftedValue]
  rw [quittingAnchoredPathValue_at_cutoff reward terminal (period + 1) block hblock.1,
    quittingCyclicBlockValue_at_zero reward terminal (period + 1) block hblock]

theorem blockShiftedValue_nonneg (time : ℕ) (htime : time ≤ period + 1) :
    0 ≤ blockShiftedValue period block time := by
  rcases lt_or_eq_of_le htime with hlt | heq
  · exact blockShiftedValue_nonneg_of_lt terminal period block hblock time hlt
  · rw [heq, blockShiftedValue_at_cutoff terminal period block hblock]
    exact blockShiftedValue_nonneg_of_lt terminal period block hblock 0 (by omega)

theorem blockShiftedValue_step_le (time : ℕ) (htime : time < period + 1) :
    blockShiftedValue period block time ≤ blockShiftedValue period block (time + 1) := by
  have hbell := quittingAnchoredPathValue_eq_successor reward terminal (period + 1)
    block hblock.1 time htime
  have hnash := quittingAnchoredPathRoots_isZeroEndpointNash reward terminal
    (period + 1) block hblock.1 time htime
  have htail := blockShiftedValue_nonneg terminal period block hblock (time + 1)
    (by omega)
  simp only [blockShiftedValue] at htail ⊢
  rw [congrFun hbell true]
  exact shiftedValue_le_shiftedTail _ _ hnash htail

theorem blockShiftedValue_step_lt (time : ℕ) (htime : time < period + 1)
    (hpos : 0 < blockQuitProbability period block time) :
    blockShiftedValue period block time < blockShiftedValue period block (time + 1) := by
  have hbell := quittingAnchoredPathValue_eq_successor reward terminal (period + 1)
    block hblock.1 time htime
  have hnash := quittingAnchoredPathRoots_isZeroEndpointNash reward terminal
    (period + 1) block hblock.1 time htime
  have htail := blockShiftedValue_nonneg terminal period block hblock (time + 1)
    (by omega)
  simp only [blockShiftedValue] at htail ⊢
  rw [congrFun hbell true]
  exact shiftedValue_lt_shiftedTail _ _ hnash htail hpos

theorem blockShiftedValue_mono :
    ∀ n, n ≤ period + 1 → ∀ m, m ≤ n →
      blockShiftedValue period block m ≤ blockShiftedValue period block n := by
  intro n
  induction n with
  | zero =>
      intro _ m hm
      rw [Nat.le_zero.mp hm]
  | succ n ih =>
      intro hn m hm
      rcases Nat.eq_or_lt_of_le hm with heq | hlt
      · rw [heq]
      · exact le_trans (ih (by omega) m (by omega))
          (blockShiftedValue_step_le terminal period block hblock n (by omega))

/-- **Item 4, the core.**  Coordinate `1` never quits at any phase of an
absorbing complementary cycle for this weight: a phase with `p > 0` strictly
increases the shifted coordinate-`2` value, which never decreases and must
return to its starting value around the cycle. -/
theorem blockQuitProbability_eq_zero (time : ℕ) (htime : time < period + 1) :
    blockQuitProbability period block time = 0 := by
  by_contra hne
  have hpos : 0 < blockQuitProbability period block time :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
  have hstrict := blockShiftedValue_step_lt terminal period block hblock time htime hpos
  have hbefore := blockShiftedValue_mono terminal period block hblock time
    (by omega) 0 (by omega)
  have hafter := blockShiftedValue_mono terminal period block hblock (period + 1)
    (by omega) (time + 1) (by omega)
  have hcyc := blockShiftedValue_at_cutoff terminal period block hblock
  linarith

/-- **Item 4.**  Coordinate `2` is isolated at every phase of every absorbing
complementary cycle for this weight. -/
theorem isQuittingIsolatedWindow_of_cyclicContinuationBlock :
    IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots (period + 1) block) true (period + 1) := by
  intro time htime other hother
  cases other with
  | true => exact absurd rfl hother
  | false =>
      have hp := blockQuitProbability_eq_zero terminal period block hblock time htime
      rw [blockQuitProbability] at hp
      have hsum := quittingRoot_continueProbability_add_quitProbability
        (quittingFiniteNashBellmanPathRoots (period + 1) block time) false
      exact eq_pure_false_of_continueProbability_eq_one (by linarith)

end Cycle

/-- **The second disjunct fails outright.**  No absorbing complementary cycle
for this weight is admissible: every such cycle silences coordinate `1`, so its
deleted survival product at coordinate `2` is `1`, and `r_2({2}) = -1 < 0`. -/
theorem not_hasAdmissibleAbsorbingQuittingCycle_reward :
    ¬ HasAdmissibleAbsorbingQuittingCycle reward := by
  rintro ⟨terminal, period, block, hblock, hadmissible⟩
  have hiso := isQuittingIsolatedWindow_of_cyclicContinuationBlock terminal period
    block hblock
  rcases hadmissible true with hcontract | hnonneg
  · have hprod : (∏ stage : Fin (period + 1),
        quittingStationaryFixedOpponentsContinueMass
          (quittingCyclicContinuationBlockCycle period block stage) true) = 1 := by
      refine Finset.prod_eq_one fun stage _ ↦ ?_
      have hcycle : quittingCyclicContinuationBlockCycle period block stage =
          quittingFiniteNashBellmanPathRoots (period + 1) block stage.val := by
        rw [quittingFiniteNashBellmanPathRoots_of_lt (period + 1) block stage.val
          stage.isLt]
        rfl
      rw [hcycle]
      exact quittingRootDeletedContinueMass_eq_one_of_isolated (hiso stage.val stage.isLt)
    rw [hprod] at hcontract
    exact lt_irrefl 1 hcontract
  · rw [reward_singleton_true_self] at hnonneg
    norm_num at hnonneg

/-- **The counterexample weight lies outside both disjuncts.** -/
theorem not_isQuittingZeroSolo_and_not_hasAdmissibleAbsorbingQuittingCycle :
    ¬ IsQuittingZeroSolo reward ∧ ¬ HasAdmissibleAbsorbingQuittingCycle reward :=
  ⟨not_isQuittingZeroSolo_reward, not_hasAdmissibleAbsorbingQuittingCycle_reward⟩

end QuittingDisjunctionCounterexample

/-- **The disjunction of the finite-quitting reduction is not exhaustive.**

`HEADLINE` — the permanent regression against restating the disjunction
`IsQuittingZeroSolo ∨ HasAdmissibleAbsorbingQuittingCycle` as a theorem about
every weight: the two-coordinate weight `r({1}) = r({2}) = (1, -1)`,
`r({1,2}) = (0, 1)` satisfies neither branch.  It refutes exactly the
*completeness of this carrier*, so
`exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle` cannot be
upgraded to an unconditional existence theorem by discharging its hypothesis.
It does **not** claim that this weight has no uniform equilibrium payoff — it
has two coordinates and one exists by other means; nor does it say anything
about weights outside the exhibited one. -/
theorem not_forall_isQuittingZeroSolo_or_hasAdmissibleAbsorbingQuittingCycle :
    ¬ ∀ reward : {S : Finset Bool // S.Nonempty} → Payoff Bool,
        IsQuittingZeroSolo reward ∨ HasAdmissibleAbsorbingQuittingCycle reward := by
  intro hall
  rcases hall QuittingDisjunctionCounterexample.reward with hzero | hcycle
  · exact QuittingDisjunctionCounterexample.not_isQuittingZeroSolo_reward hzero
  · exact QuittingDisjunctionCounterexample.not_hasAdmissibleAbsorbingQuittingCycle_reward
      hcycle

end GameTheory
