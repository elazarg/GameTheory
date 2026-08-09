/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtCapCarrier
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtCapBridge
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler
import UniformEquilibrium.Quitting.Debt.Dynamic.ExactDynamicDebtVanishingCounterexample

/-!
# Positive augmented debt need not admit a charged exact predecessor

This rational two-player table is a local regression fence for the exact
dynamic-debt cap seam.  At the zero continuation, equal hazards `1/6` form an
exact Nash root with value `(1/2,1/2)`.  The singleton terminal cap is `(1,1)`,
so the exact current debt is `(5/6,5/6)` and the augmented cap is
`(4/3,4/3)`.

Against that augmented cap, Continue strictly dominates Quit for both
players against every opponent marginal.  Hence all-Continue is the unique
exact Nash root and every exact predecessor there has zero absorption charge.
Positive dynamic debt therefore cannot be converted locally into a positive
charged exact edge.

The table is not strategically pathological: the pure profile in which one
player quits and the other continues is an exact terminal Nash profile.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
  Math.ProbabilityMassFunction
open QuittingSureSetOwnerRepair

namespace QuittingDynamicDebtCapChargedAnchorCounterexample

/-- Singleton quitters receive `1` and the other player receives `3`; joint
quitting gives both players `-2`. -/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if false ∈ quitters.1 then
      if true ∈ quitters.1 then -2
      else if who then 3 else 1
    else if who then 1 else 3

/-- Boolean expectation expansion used throughout the two-player table. -/
theorem expect_pmfPi_bool (selectedRoot : Bool → PMF Bool)
    (f : (Bool → Bool) → ℝ) :
    expect (pmfPi selectedRoot) f =
      expect (selectedRoot false) (fun first =>
        expect (selectedRoot true) (fun second =>
          f (fun who => if who then second else first))) :=
  QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool
    selectedRoot f

/-- A quit coin with probability `1/6`. -/
def sixthCoin : PMF Bool :=
  quittingHazardCoin (1 / 6) (by norm_num) (by norm_num)

/-- Both players use the `1/6` quit coin. -/
def root : Bool → PMF Bool := fun _ => sixthCoin

/-- The exact zero-tail value `(1/2,1/2)`. -/
def value : Payoff Bool := fun _ => 1 / 2

/-- The singleton terminal cap `(1,1)`. -/
def terminalDebt : Payoff Bool := fun _ => 1

/-- The exact one-step debt `(5/6,5/6)`. -/
def currentDebt : Payoff Bool := fun _ => 5 / 6

/-- The augmented cap `(4/3,4/3)`. -/
def augmentedCap : Payoff Bool := fun _ => 4 / 3

def simplexRoot : QuittingRootSimplex Bool :=
  fun who => stdSimplexEquiv (root who)

def current : QuittingNashBellmanPoint Bool := (value, simplexRoot)

def terminal : QuittingNashBellmanPoint Bool :=
  ((0 : Payoff Bool), quittingAllContinueSimplexRoot)

@[simp] theorem sixthCoin_true : (sixthCoin true).toReal = 1 / 6 := by
  simp [sixthCoin]

@[simp] theorem sixthCoin_false : (sixthCoin false).toReal = 5 / 6 := by
  norm_num [sixthCoin]

@[simp] theorem root_apply (who : Bool) : root who = sixthCoin := rfl

@[simp] theorem quittingRootOfSimplex_simplexRoot :
    quittingRootOfSimplex simplexRoot = root := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)

@[simp] theorem singletonReward (who : Bool) :
    reward (quittingSingletonTerminal who) who = 1 := by
  cases who <;> simp [reward, quittingSingletonTerminal]

@[simp] theorem positiveSingletonDebtCap (who : Bool) :
    quittingPositiveSingletonDebtCap reward who = 1 := by
  simp [quittingPositiveSingletonDebtCap]

/-! ## The exact positive-debt edge -/

theorem quitPayoff_zero (who : Bool) :
    quittingRootQuitPayoff reward (0 : Payoff Bool) root who = 1 / 2 := by
  cases who <;>
    unfold quittingRootQuitPayoff quittingRootExpectedPayoff <;>
    rw [expect_pmfPi_bool] <;>
    simp only [expect_eq_sum, Fintype.sum_bool] <;>
    norm_num [root, sixthCoin, quittingHazardCoin, PMF.ofFintype_apply,
      quittingRootPayoff, reward,
      QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction]

theorem continuePayoff_zero (who : Bool) :
    quittingRootContinuePayoff reward (0 : Payoff Bool) root who = 1 / 2 := by
  cases who <;>
    unfold quittingRootContinuePayoff quittingRootExpectedPayoff <;>
    rw [expect_pmfPi_bool] <;>
    simp only [expect_eq_sum, Fintype.sum_bool] <;>
    norm_num [root, sixthCoin, quittingHazardCoin, PMF.ofFintype_apply,
      quittingRootPayoff, reward,
      QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction]

theorem root_isEndpointNash_zero :
    IsεQuittingRootEndpointNash reward (0 : Payoff Bool) 0 root := by
  intro who
  rw [quittingRootEndpointDifference, quitPayoff_zero, continuePayoff_zero]
  norm_num

theorem root_successor_zero :
    quittingRootSuccessorPayoff reward (0 : Payoff Bool) root = value := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    quitPayoff_zero, continuePayoff_zero]
  simp [root, value]
  ring

theorem current_terminal_edge :
    IsQuittingNashBellmanEdge reward current terminal := by
  constructor
  · simpa [current, terminal, quittingRootOfSimplex_simplexRoot] using
      root_successor_zero.symm
  · simpa [current, terminal, quittingRootOfSimplex_simplexRoot] using
      root_isEndpointNash_zero

@[simp] theorem opponentContinueMass (who : Bool) :
    quittingDebtOpponentContinueMass (current, currentDebt) who = 5 / 6 := by
  rw [quittingDebtOpponentContinueMass_eq_stationary]
  rw [show quittingRootOfSimplex (current, currentDebt).1.2 = root by
    exact quittingRootOfSimplex_simplexRoot]
  cases who <;>
    norm_num [quittingStationaryFixedOpponentsContinueMass,
      quittingStationaryContinueMass, pmfPi_apply,
      quittingAllContinueAction, root]

theorem dynamicDebtUpdate (who : Bool) :
    quittingDynamicDebtUpdate reward (current, currentDebt)
        (terminal, quittingPositiveSingletonDebtCap reward) who = 5 / 6 := by
  unfold quittingDynamicDebtUpdate
  rw [show quittingRootOfSimplex (current, currentDebt).1.2 = root by
      exact quittingRootOfSimplex_simplexRoot]
  rw [show (terminal, quittingPositiveSingletonDebtCap reward).1.1 =
      (0 : Payoff Bool) by rfl]
  rw [quitPayoff_zero, continuePayoff_zero, opponentContinueMass,
    show (terminal, quittingPositiveSingletonDebtCap reward).2 who = 1 by
      exact positiveSingletonDebtCap who]
  change max (1 / 2) (1 / 2 + 5 / 6 * 1) - 1 / 2 = 5 / 6
  norm_num

theorem current_terminal_dynamicDebtEdge :
    IsQuittingDynamicDebtEdge reward
      (current, currentDebt)
      (terminal, quittingPositiveSingletonDebtCap reward) := by
  refine ⟨current_terminal_edge, ?_⟩
  intro who
  simpa [currentDebt] using (dynamicDebtUpdate who).symm

@[simp] theorem dynamicDebtCap_current :
    quittingDynamicDebtCap (current, currentDebt) = augmentedCap := by
  funext who
  simp [quittingDynamicDebtCap, current, value, currentDebt, augmentedCap]
  norm_num

/-! ## Punishment floor -/

theorem stationaryQuitValue (arbitraryRoot : Bool → PMF Bool) (who : Bool) :
    quittingStationaryFixedOpponentsQuitValue reward arbitraryRoot who =
      1 - 3 * (arbitraryRoot (!who) true).toReal := by
  cases who <;>
    unfold quittingStationaryFixedOpponentsQuitValue
      quittingFixedOpponentsQuitValue
      quittingRootAbsorbingContribution quittingRootExpectedPayoff <;>
    rw [expect_pmfPi_bool] <;>
    simp only [expect_eq_sum, Fintype.sum_bool] <;>
    have hsum := pmf_toReal_sum_one (arbitraryRoot true) <;>
    have hsum' := pmf_toReal_sum_one (arbitraryRoot false) <;>
    simp only [Fintype.sum_bool] at hsum hsum' <;>
    simp [quittingRootPayoff, reward] <;>
    linarith

theorem stationaryContinueReward (arbitraryRoot : Bool → PMF Bool)
    (who : Bool) :
    quittingStationaryFixedOpponentsContinueReward reward arbitraryRoot who =
      3 * (arbitraryRoot (!who) true).toReal := by
  cases who <;>
    unfold quittingStationaryFixedOpponentsContinueReward
      quittingFixedOpponentsContinueReward
      quittingRootAbsorbingContribution quittingRootExpectedPayoff <;>
    rw [expect_pmfPi_bool] <;>
    simp only [expect_eq_sum, Fintype.sum_bool] <;>
    simp [quittingRootPayoff, reward] <;>
    ring

theorem stationaryContinueMass (arbitraryRoot : Bool → PMF Bool)
    (who : Bool) :
    quittingStationaryFixedOpponentsContinueMass arbitraryRoot who =
      (arbitraryRoot (!who) false).toReal := by
  cases who <;>
    norm_num [quittingStationaryFixedOpponentsContinueMass,
      quittingFixedOpponentsContinueMass,
      quittingStationaryContinueMass, pmfPi_apply,
      quittingAllContinueAction]

theorem one_le_stationaryUnilateralCap
    (arbitraryRoot : Bool → PMF Bool) (who : Bool) :
    1 ≤ quittingStationaryUnilateralCap reward arbitraryRoot who := by
  let q := (arbitraryRoot (!who) true).toReal
  let c := (arbitraryRoot (!who) false).toReal
  have hsum : c + q = 1 := by
    dsimp only [c, q]
    simpa [Fintype.sum_bool, add_comm] using
      pmf_toReal_sum_one (arbitraryRoot (!who))
  rw [quittingStationaryUnilateralCap_eq_max_div,
    stationaryQuitValue, stationaryContinueReward, stationaryContinueMass]
  change 1 ≤ max (1 - 3 * q) (3 * q / (1 - c))
  by_cases hq : q = 0
  · rw [hq]
    norm_num
  · have hqpos : 0 < q := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hq)
    have hden : 1 - c = q := by linarith
    rw [hden]
    have hquotient : 3 * q / q = 3 := by
      field_simp
    rw [hquotient]
    norm_num

theorem punishmentValue_eq_one (who : Bool) :
    quittingPunishmentValue reward who = 1 := by
  apply le_antisymm
  · cases who
    · simpa [quittingSetReward, reward] using
        (quittingPunishmentValue_le_max_solo reward false)
    · simpa [quittingSetReward, reward] using
        (quittingPunishmentValue_le_max_solo reward true)
  · rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
    apply le_ciInf
    intro arbitraryRoot
    exact one_le_stationaryUnilateralCap arbitraryRoot who

/-! ## The local charged-anchor obstruction -/

theorem endpointDifference_augmentedCap
    (arbitraryRoot : Bool → PMF Bool) (who : Bool) :
    quittingRootEndpointDifference reward augmentedCap arbitraryRoot who =
      -(1 / 3) - (14 / 3) * (arbitraryRoot (!who) true).toReal := by
  rw [quittingRootEndpointDifference]
  cases who <;>
    unfold quittingRootQuitPayoff quittingRootContinuePayoff
      quittingRootExpectedPayoff <;>
    rw [expect_pmfPi_bool, expect_pmfPi_bool] <;>
    simp only [expect_eq_sum, Fintype.sum_bool] <;>
    have hsum := pmf_toReal_sum_one (arbitraryRoot true) <;>
    have hsum' := pmf_toReal_sum_one (arbitraryRoot false) <;>
    simp only [Fintype.sum_bool] at hsum hsum' <;>
    simp [quittingRootPayoff, reward, augmentedCap,
      ] <;>
    ring_nf at * <;>
    linarith

theorem allContinue_uniqueNash_at_augmentedCap
    (arbitraryRoot : Bool → PMF Bool)
    (hnash : IsεQuittingRootNash reward augmentedCap 0 arbitraryRoot) :
    arbitraryRoot = quittingAllContinueRoot := by
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward augmentedCap arbitraryRoot).2 hnash
  funext who
  apply pmf_eq_pure_false_of_apply_true_toReal_eq_zero
  have hwho := (hendpoint who).2
  rw [endpointDifference_augmentedCap] at hwho
  have hq : 0 ≤ (arbitraryRoot (!who) true).toReal := ENNReal.toReal_nonneg
  have hp : 0 ≤ (arbitraryRoot who true).toReal := ENNReal.toReal_nonneg
  nlinarith

theorem absorptionCharge_eq_zero_of_nash_at_augmentedCap
    (arbitraryRoot : Bool → PMF Bool)
    (hnash : IsεQuittingRootNash reward augmentedCap 0 arbitraryRoot) :
    quittingRootAbsorptionMass arbitraryRoot = 0 := by
  rw [allContinue_uniqueNash_at_augmentedCap arbitraryRoot hnash]
  exact quittingRootAbsorptionMass_allContinueRoot

/-! ## A genuine exact terminal equilibrium -/

/-- Player `false` quits surely while player `true` continues surely. -/
def terminalRoot : Bool → PMF Bool :=
  fun who => if who then PMF.pure false else PMF.pure true

/-- The terminal payoff `(1,3)`. -/
def terminalValue : Payoff Bool := fun who => if who then 3 else 1

theorem terminalRoot_hasSureQuitter : QuittingRootHasSureQuitter terminalRoot := by
  exact ⟨false, by simp [terminalRoot]⟩

theorem terminalRoot_successor :
    quittingRootSuccessorPayoff reward terminalValue terminalRoot =
      terminalValue := by
  funext who
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp [expect_pure, terminalRoot, terminalValue, quittingRootPayoff, reward,
    QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction]

theorem terminalRoot_isEndpointNash :
    IsεQuittingRootEndpointNash reward terminalValue 0 terminalRoot := by
  intro who
  cases who
  · unfold quittingRootEndpointDifference quittingRootQuitPayoff
      quittingRootContinuePayoff quittingRootExpectedPayoff
    rw [expect_pmfPi_bool, expect_pmfPi_bool]
    simp [expect_pure, terminalRoot, terminalValue, quittingRootPayoff, reward,
      QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction]
  · unfold quittingRootEndpointDifference quittingRootQuitPayoff
      quittingRootContinuePayoff quittingRootExpectedPayoff
    rw [expect_pmfPi_bool, expect_pmfPi_bool]
    simp [expect_pure, terminalRoot, terminalValue, quittingRootPayoff, reward,
      QuittingExactDynamicDebtVanishingCounterexample.quittingQuitters_boolAction]
    norm_num

theorem terminalRoot_boundary :
    IsQuittingStationaryBoundaryAdmissible reward terminalRoot terminalValue := by
  intro who hmass
  cases who
  · simp [terminalValue, quittingSingletonTerminal, reward]
  · exfalso
    have hzero : quittingStationaryFixedOpponentsContinueMass
        terminalRoot true = 0 := by
      norm_num [quittingStationaryFixedOpponentsContinueMass,
        quittingFixedOpponentsContinueMass,
        quittingStationaryContinueMass, pmfPi_apply,
        quittingAllContinueAction, terminalRoot]
    linarith

theorem terminalProfile_isExactNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward terminalRoot) := by
  apply (isZeroAsymptoticNash_stationary_iff_boundary_of_fixedPoint_endpointNash
    reward terminalRoot terminalValue ?_ terminalRoot_successor.symm
      terminalRoot_isEndpointNash).2
  · exact terminalRoot_boundary
  · have hmass : quittingStationaryContinueMass terminalRoot = 0 := by
      norm_num [quittingStationaryContinueMass, pmfPi_apply,
        quittingAllContinueAction, terminalRoot]
    rw [hmass]
    norm_num

end QuittingDynamicDebtCapChargedAnchorCounterexample

end GameTheory
