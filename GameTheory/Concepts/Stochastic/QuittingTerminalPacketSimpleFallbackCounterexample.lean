/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingDynamicDebtOwnerTransferCounterexample
import GameTheory.Concepts.Stochastic.QuittingStationaryGain

/-!
# A positive terminal-debt packet need not supply a simple fallback

This is a minimal two-player terminal packet.  The half--half root is an
exact zero-boundary Nash--Bellman edge and carries positive exact dynamic
debt for player one.  Its joining-loss atom has fixed positive mass.
Nevertheless the underlying game has no exact stationary terminal
equilibrium, hence in particular no stationary singleton-First fallback.

The result is deliberately local.  It does not exclude nonstationary
equilibria or accuracy-indexed periodic profiles, and it makes no claim about
optimized debt over long cutoffs.  Its role is to prevent terminal packet
provenance, or a playerwise scalar prefix summary, from being mistaken for a
producer of a stationary/First boundary.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
  Math.ProbabilityMassFunction

namespace QuittingTerminalPacketSimpleFallbackCounterexample

/-! We use `false` for player one and `true` for player two. -/

/-- Payoffs `QC = (1,-1)`, `CQ = (-1,-1)`, and `QQ = (-2,0)`. -/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if false ∈ quitters.1 then
      if true ∈ quitters.1 then
        if who then 0 else -2
      else
        if who then -1 else 1
    else
      if who then -1 else -1

/-- Both players independently Quit with probability one half. -/
def root : Bool → PMF Bool := fun _ => PMF.uniformOfFintype Bool

/-- The exact zero-boundary root value `(-1/2,-1/2)`. -/
def value : Payoff Bool := fun _ => -1 / 2

/-- Simplex presentation of `root`. -/
def simplexRoot : QuittingRootSimplex Bool :=
  fun who => stdSimplexEquiv (root who)

/-- The zero-boundary edge's current point. -/
def current : QuittingNashBellmanPoint Bool := (value, simplexRoot)

/-- Its zero terminal point. -/
def terminal : QuittingNashBellmanPoint Bool :=
  ((0 : Payoff Bool), quittingAllContinueSimplexRoot)

/-- The exact current debt `(1/2,0)`. -/
def currentDebt : Payoff Bool := fun who => if who then 0 else 1 / 2

theorem expect_pmfPi_bool (selectedRoot : Bool → PMF Bool)
    (f : (Bool → Bool) → ℝ) :
    expect (pmfPi selectedRoot) f =
      expect (selectedRoot false) (fun first ↦
        expect (selectedRoot true) (fun second ↦
          f (fun who ↦ if who then second else first))) :=
  QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool
    selectedRoot f

@[simp] theorem root_apply (who : Bool) :
    root who = PMF.uniformOfFintype Bool := rfl

@[simp] theorem quittingRootOfSimplex_simplexRoot :
    quittingRootOfSimplex simplexRoot = root := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)

@[simp] theorem value_apply (who : Bool) : value who = -1 / 2 := rfl

@[simp] theorem currentDebt_false : currentDebt false = 1 / 2 := by
  simp [currentDebt]

@[simp] theorem currentDebt_true : currentDebt true = 0 := by
  simp [currentDebt]

/-! ## Exact root formulas -/

/-- Player one's pure-Quit endpoint is `1 - 3b`. -/
theorem false_quitPayoff (tail : Payoff Bool)
    (selectedRoot : Bool → PMF Bool) :
    quittingRootQuitPayoff reward tail selectedRoot false =
      1 - 3 * (selectedRoot true true).toReal := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward]
  have hsum :=
    quittingRoot_continueProbability_add_quitProbability selectedRoot true
  ring_nf at hsum ⊢
  linarith

/-- Player one's pure-Continue endpoint is
`-b + (1-b) tail₁`. -/
theorem false_continuePayoff (tail : Payoff Bool)
    (selectedRoot : Bool → PMF Bool) :
    quittingRootContinuePayoff reward tail selectedRoot false =
      -(selectedRoot true true).toReal +
        (selectedRoot true false).toReal * tail false := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward]

/-- Player two's pure-Quit endpoint is `a - 1`. -/
theorem true_quitPayoff (tail : Payoff Bool)
    (selectedRoot : Bool → PMF Bool) :
    quittingRootQuitPayoff reward tail selectedRoot true =
      (selectedRoot false true).toReal - 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward]
  have hsum :=
    quittingRoot_continueProbability_add_quitProbability selectedRoot false
  ring_nf at hsum ⊢
  linarith

/-- Player two's pure-Continue endpoint is
`-a + (1-a) tail₂`. -/
theorem true_continuePayoff (tail : Payoff Bool)
    (selectedRoot : Bool → PMF Bool) :
    quittingRootContinuePayoff reward tail selectedRoot true =
      -(selectedRoot false true).toReal +
        (selectedRoot false false).toReal * tail true := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward]

theorem false_quitPayoff_root_zero :
    quittingRootQuitPayoff reward (0 : Payoff Bool) root false = -1 / 2 := by
  rw [false_quitPayoff]
  norm_num [root, PMF.uniformOfFintype_apply]

theorem false_continuePayoff_root_zero :
    quittingRootContinuePayoff reward (0 : Payoff Bool) root false =
      -1 / 2 := by
  rw [false_continuePayoff]
  norm_num [root, PMF.uniformOfFintype_apply]

theorem true_quitPayoff_root_zero :
    quittingRootQuitPayoff reward (0 : Payoff Bool) root true = -1 / 2 := by
  rw [true_quitPayoff]
  norm_num [root, PMF.uniformOfFintype_apply]

theorem true_continuePayoff_root_zero :
    quittingRootContinuePayoff reward (0 : Payoff Bool) root true =
      -1 / 2 := by
  rw [true_continuePayoff]
  norm_num [root, PMF.uniformOfFintype_apply]

/-- Both players mix indifferently at the zero boundary. -/
theorem root_isEndpointNash_zero :
    IsεQuittingRootEndpointNash reward (0 : Payoff Bool) 0 root := by
  intro who
  cases who
  · rw [quittingRootEndpointDifference, false_quitPayoff_root_zero,
      false_continuePayoff_root_zero]
    norm_num
  · rw [quittingRootEndpointDifference, true_quitPayoff_root_zero,
      true_continuePayoff_root_zero]
    norm_num

/-- The half--half root sends the zero tail to `(-1/2,-1/2)`. -/
theorem root_successor_zero :
    quittingRootSuccessorPayoff reward (0 : Payoff Bool) root = value := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  cases who
  · rw [false_quitPayoff_root_zero, false_continuePayoff_root_zero]
    norm_num [root, PMF.uniformOfFintype_apply, value]
  · rw [true_quitPayoff_root_zero, true_continuePayoff_root_zero]
    norm_num [root, PMF.uniformOfFintype_apply, value]

/-- The displayed points form an exact zero-boundary Nash--Bellman edge. -/
theorem current_terminal_edge :
    IsQuittingNashBellmanEdge reward current terminal := by
  constructor
  · simpa [current, terminal, quittingRootOfSimplex_simplexRoot] using
      root_successor_zero.symm
  · simpa [current, terminal, quittingRootOfSimplex_simplexRoot] using
      root_isEndpointNash_zero

/-! ## Positive exact debt and its nonvanishing joining-loss atom -/

@[simp] theorem positiveSingletonDebtCap_false :
    quittingPositiveSingletonDebtCap reward false = 1 := by
  simp [quittingPositiveSingletonDebtCap, reward,
    quittingSingletonTerminal]

@[simp] theorem positiveSingletonDebtCap_true :
    quittingPositiveSingletonDebtCap reward true = 0 := by
  simp [quittingPositiveSingletonDebtCap, reward,
    quittingSingletonTerminal]

@[simp] theorem opponentContinueMass_false :
    quittingDebtOpponentContinueMass (current, currentDebt) false = 1 / 2 := by
  rw [quittingDebtOpponentContinueMass_eq_stationary]
  rw [show quittingRootOfSimplex (current, currentDebt).1.2 = root by
    exact quittingRootOfSimplex_simplexRoot]
  norm_num [quittingStationaryContinueMass, pmfPi_apply,
    quittingAllContinueAction, root, PMF.uniformOfFintype_apply]

@[simp] theorem opponentContinueMass_true :
    quittingDebtOpponentContinueMass (current, currentDebt) true = 1 / 2 := by
  rw [quittingDebtOpponentContinueMass_eq_stationary]
  rw [show quittingRootOfSimplex (current, currentDebt).1.2 = root by
    exact quittingRootOfSimplex_simplexRoot]
  norm_num [quittingStationaryContinueMass, pmfPi_apply,
    quittingAllContinueAction, root, PMF.uniformOfFintype_apply]

/-- Player one's exact dynamic debt at the packet is `1/2`. -/
theorem dynamicDebtUpdate_false :
    quittingDynamicDebtUpdate reward
        (current, currentDebt)
        (terminal, quittingPositiveSingletonDebtCap reward) false = 1 / 2 := by
  unfold quittingDynamicDebtUpdate
  rw [show quittingRootOfSimplex (current, currentDebt).1.2 = root by
      exact quittingRootOfSimplex_simplexRoot]
  rw [show (terminal, quittingPositiveSingletonDebtCap reward).1.1 =
      (0 : Payoff Bool) by rfl]
  rw [false_quitPayoff_root_zero, false_continuePayoff_root_zero,
    opponentContinueMass_false]
  change max (-1 / 2) (-1 / 2 + 1 / 2 *
      quittingPositiveSingletonDebtCap reward false) - value false = 1 / 2
  rw [positiveSingletonDebtCap_false]
  norm_num [value]

/-- Player two's exact dynamic debt is zero. -/
theorem dynamicDebtUpdate_true :
    quittingDynamicDebtUpdate reward
        (current, currentDebt)
        (terminal, quittingPositiveSingletonDebtCap reward) true = 0 := by
  unfold quittingDynamicDebtUpdate
  rw [show quittingRootOfSimplex (current, currentDebt).1.2 = root by
      exact quittingRootOfSimplex_simplexRoot]
  rw [show (terminal, quittingPositiveSingletonDebtCap reward).1.1 =
      (0 : Payoff Bool) by rfl]
  rw [true_quitPayoff_root_zero, true_continuePayoff_root_zero,
    opponentContinueMass_true]
  change max (-1 / 2) (-1 / 2 + 1 / 2 *
      quittingPositiveSingletonDebtCap reward true) - value true = 0
  rw [positiveSingletonDebtCap_true]
  norm_num [value]

/-- The packet carries the literal exact dynamic-debt annotation `(1/2,0)`. -/
theorem current_terminal_dynamicDebtEdge :
    IsQuittingDynamicDebtEdge reward
      (current, currentDebt)
      (terminal, quittingPositiveSingletonDebtCap reward) := by
  refine ⟨current_terminal_edge, ?_⟩
  intro who
  cases who
  · simpa using dynamicDebtUpdate_false.symm
  · simpa using dynamicDebtUpdate_true.symm

/-- The opponent-quit atom has fixed positive raw mass. -/
theorem terminalOpponentAtom_nonvanishing :
    0 < (root true true).toReal := by
  norm_num [root, PMF.uniformOfFintype_apply]

/-- On that atom player one strictly loses one by joining the quitter set. -/
theorem terminalOpponentAtom_joiningLoss_eq_one :
    reward (quittingSingletonTerminal true) false -
        reward ⟨{false, true}, by simp⟩ false = 1 := by
  norm_num [reward, quittingSingletonTerminal]

/-! ## Stationary roots cannot discharge the packet -/

/-- In the Boolean game, player one's opponent-Continue mass is player two's
Continue probability. -/
theorem stationaryFixedOpponentsContinueMass_false
    (selectedRoot : Bool → PMF Bool) :
    quittingStationaryFixedOpponentsContinueMass selectedRoot false =
      (selectedRoot true false).toReal := by
  simpa [quittingStationaryFixedOpponentsContinueMass] using
    (QuittingExactDynamicDebtVanishingCounterexample.fixedOpponentsContinueMass_false
      (fun _ => selectedRoot) 0)

/-- Symmetrically for player two. -/
theorem stationaryFixedOpponentsContinueMass_true
    (selectedRoot : Bool → PMF Bool) :
    quittingStationaryFixedOpponentsContinueMass selectedRoot true =
      (selectedRoot false false).toReal := by
  simpa [quittingStationaryFixedOpponentsContinueMass] using
    (QuittingExactDynamicDebtVanishingCounterexample.fixedOpponentsContinueMass_true
      (fun _ => selectedRoot) 0)

theorem stationaryFixedOpponentsQuitValue_false
    (selectedRoot : Bool → PMF Bool) :
    quittingStationaryFixedOpponentsQuitValue reward selectedRoot false =
      1 - 3 * (selectedRoot true true).toReal := by
  simpa [quittingStationaryFixedOpponentsQuitValue,
    quittingFixedOpponentsQuitValue, quittingRootQuitPayoff,
    quittingRootAbsorbingContribution] using
    (false_quitPayoff (0 : Payoff Bool) selectedRoot)

theorem stationaryFixedOpponentsContinueReward_false
    (selectedRoot : Bool → PMF Bool) :
    quittingStationaryFixedOpponentsContinueReward reward selectedRoot false =
      -(selectedRoot true true).toReal := by
  simpa [quittingStationaryFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueReward, quittingRootContinuePayoff,
    quittingRootAbsorbingContribution] using
    (false_continuePayoff (0 : Payoff Bool) selectedRoot)

theorem stationaryFixedOpponentsQuitValue_true
    (selectedRoot : Bool → PMF Bool) :
    quittingStationaryFixedOpponentsQuitValue reward selectedRoot true =
      (selectedRoot false true).toReal - 1 := by
  simpa [quittingStationaryFixedOpponentsQuitValue,
    quittingFixedOpponentsQuitValue, quittingRootQuitPayoff,
    quittingRootAbsorbingContribution] using
    (true_quitPayoff (0 : Payoff Bool) selectedRoot)

theorem stationaryFixedOpponentsContinueReward_true
    (selectedRoot : Bool → PMF Bool) :
    quittingStationaryFixedOpponentsContinueReward reward selectedRoot true =
      -(selectedRoot false true).toReal := by
  simpa [quittingStationaryFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueReward, quittingRootContinuePayoff,
    quittingRootAbsorbingContribution] using
    (true_continuePayoff (0 : Payoff Bool) selectedRoot)

/-- Player one's stationary gain numerator is `b(2-3b)`. -/
theorem stationaryGain_false (selectedRoot : Bool → PMF Bool) :
    quittingStationaryGain reward selectedRoot false =
      (selectedRoot true true).toReal *
        (2 - 3 * (selectedRoot true true).toReal) := by
  rw [quittingStationaryGain,
    stationaryFixedOpponentsContinueMass_false,
    stationaryFixedOpponentsQuitValue_false,
    stationaryFixedOpponentsContinueReward_false]
  have hsum :=
    quittingRoot_continueProbability_add_quitProbability selectedRoot true
  have hcontinue : (selectedRoot true false).toReal =
      1 - (selectedRoot true true).toReal := by linarith
  rw [hcontinue]
  ring

/-- Player two's stationary gain numerator is the square of player one's
Quit probability. -/
theorem stationaryGain_true (selectedRoot : Bool → PMF Bool) :
    quittingStationaryGain reward selectedRoot true =
      (selectedRoot false true).toReal ^ 2 := by
  rw [quittingStationaryGain,
    stationaryFixedOpponentsContinueMass_true,
    stationaryFixedOpponentsQuitValue_true,
    stationaryFixedOpponentsContinueReward_true]
  have hsum :=
    quittingRoot_continueProbability_add_quitProbability selectedRoot false
  have hcontinue : (selectedRoot false false).toReal =
      1 - (selectedRoot false true).toReal := by linarith
  rw [hcontinue]
  ring

/-- If player one has positive stationary hazard, root complementarity is
already impossible. -/
theorem not_stationaryGainComplementary_of_false_positive
    (selectedRoot : Bool → PMF Bool)
    (hpositive : 0 < (selectedRoot false true).toReal) :
    ¬ IsQuittingStationaryGainComplementary reward selectedRoot := by
  intro hcomp
  have htrue := (hcomp true).1
  rw [stationaryGain_true] at htrue
  have hb0 : 0 ≤ (selectedRoot true false).toReal := ENNReal.toReal_nonneg
  have ha2 : 0 < (selectedRoot false true).toReal ^ 2 := sq_pos_of_pos hpositive
  have hbzero : (selectedRoot true false).toReal = 0 := by
    nlinarith
  have hbquit : (selectedRoot true true).toReal = 1 := by
    have hsum :=
      quittingRoot_continueProbability_add_quitProbability selectedRoot true
    linarith
  have hfalse := (hcomp false).2
  rw [stationaryGain_false, hbquit] at hfalse
  nlinarith

/-- No stationary behavior profile is an exact terminal equilibrium.  The
positive-hazard case fails finite root complementarity; when player one never
quits, either Never itself is exploitable or player two can remove the only
remaining absorption by continuing forever. -/
theorem no_stationary_exact_terminal_equilibrium
    (selectedRoot : Bool → PMF Bool) :
    ¬ (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward selectedRoot) := by
  intro hnash
  let a := (selectedRoot false true).toReal
  let b := (selectedRoot true true).toReal
  by_cases ha : a = 0
  · have hfalseMarginal : selectedRoot false = PMF.pure false :=
      pmf_eq_pure_false_of_apply_true_toReal_eq_zero
        (selectedRoot false) (by simpa [a] using ha)
    by_cases hb : b = 0
    · have htrueMarginal : selectedRoot true = PMF.pure false :=
        pmf_eq_pure_false_of_apply_true_toReal_eq_zero
          (selectedRoot true) (by simpa [b] using hb)
      have hroot : selectedRoot = quittingAllContinueRoot := by
        funext who
        cases who
        · simpa [quittingAllContinueRoot] using hfalseMarginal
        · simpa [quittingAllContinueRoot] using htrueMarginal
      have hnever :
          (quittingStationaryProfile reward selectedRoot) =
            quittingAlwaysContinueProfile reward := by
        rw [hroot]
        rfl
      rw [hnever] at hnash
      have hcriterion :=
        (isεAsymptoticNash_quittingAlwaysContinue_iff reward le_rfl).1
          hnash false
      simp [reward, quittingSingletonTerminal] at hcriterion
      norm_num at hcriterion
    · have hbpositive : 0 < b := by
        have hbnonneg : 0 ≤ b := ENNReal.toReal_nonneg
        exact lt_of_le_of_ne hbnonneg (Ne.symm hb)
      have hroot : selectedRoot =
          quittingSoloStationaryRoot true (selectedRoot true) := by
        funext who
        cases who
        · simp [quittingSoloStationaryRoot, hfalseMarginal]
        · simp [quittingSoloStationaryRoot]
      have hprescribed :
          quittingTerminalPayoff reward
              (quittingStationaryProfile reward selectedRoot) true = -1 := by
        rw [hroot]
        simpa [quittingSoloReward, reward, quittingSingletonTerminal] using
          (quittingTerminalPayoff_soloStationary reward true true
            (selectedRoot true) (by simpa [b] using hbpositive))
      have hprofileUpdate :
          Function.update (quittingStationaryProfile reward selectedRoot) true
              (quittingAlwaysContinueStrategy reward true) =
            quittingAlwaysContinueProfile reward := by
        rw [hroot]
        funext who time history
        cases who
        · simp [quittingStationaryProfile, quittingSoloStationaryRoot,
            quittingAlwaysContinueProfile,
            StochasticGame.stationaryBehaviorProfile]
          rfl
        · rfl
      have hdeviation :=
        hnash true (quittingAlwaysContinueStrategy reward true)
      rw [hprofileUpdate, quittingTerminalPayoff_quittingAlwaysContinue,
        hprescribed] at hdeviation
      norm_num at hdeviation
  · have hapositive : 0 < a := by
      have hanonneg : 0 ≤ a := ENNReal.toReal_nonneg
      exact lt_of_le_of_ne hanonneg (Ne.symm ha)
    have habsorption : 0 < quittingRootAbsorptionMass selectedRoot := by
      rw [quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul
        selectedRoot false,
        stationaryFixedOpponentsContinueMass_false]
      have hsum :=
        quittingRoot_continueProbability_add_quitProbability selectedRoot false
      have hb0 : 0 ≤ (selectedRoot true false).toReal :=
        ENNReal.toReal_nonneg
      have hb1 : (selectedRoot true false).toReal ≤ 1 := by
        have hsumTrue :=
          quittingRoot_continueProbability_add_quitProbability selectedRoot true
        have hquit0 : 0 ≤ (selectedRoot true true).toReal :=
          ENNReal.toReal_nonneg
        linarith
      dsimp only [a] at hapositive
      have ha1 : (selectedRoot false true).toReal ≤ 1 := by
        have hcontinue0 : 0 ≤ (selectedRoot false false).toReal :=
          ENNReal.toReal_nonneg
        linarith
      have hcontinue : (selectedRoot false false).toReal =
          1 - (selectedRoot false true).toReal := by linarith
      rw [hcontinue]
      have hproduct : 0 ≤
          (1 - (selectedRoot false true).toReal) *
            (1 - (selectedRoot true false).toReal) :=
        mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)
      nlinarith
    have hrootNash :=
      isεQuittingRootNash_of_isεAsymptoticNash_stationary
        reward selectedRoot 0 hnash
    have hendpoint :=
      (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
        reward
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward selectedRoot) player)
        0 selectedRoot).2 hrootNash
    have hcomp :=
      (isQuittingStationaryGainComplementary_iff_endpointNash
        reward selectedRoot habsorption).2 hendpoint
    exact not_stationaryGainComplementary_of_false_positive
      selectedRoot (by simpa [a] using hapositive) hcomp

/-! ## Vanishing-error stationary calibration

The exact stationary no-go is sharp.  Give player one hazard `a > 0` and
player two hazard `2/3`.  Player one's stationary regret is zero, while
player two's complete behavioral-deviation cap gap is `a²/(a+2)`.  Thus
these stationary profiles are approximate terminal equilibria with error
tending to zero as `a ↓0`.
-/

/-- A local Boolean coin, returning `true` with probability `p`. -/
def coin (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  PMF.ofFintype
    (fun action => if action then ENNReal.ofReal p
      else ENNReal.ofReal (1 - p))
    (by
      rw [Fintype.sum_bool]
      simp only [if_true, if_false, Bool.false_eq_true]
      rw [← ENNReal.ofReal_add hp0 (by linarith)]
      norm_num)

@[simp] theorem coin_true_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coin p hp0 hp1 true).toReal = p := by
  simp [coin, PMF.ofFintype_apply, hp0]

@[simp] theorem coin_false_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coin p hp0 hp1 false).toReal = 1 - p := by
  simp [coin, PMF.ofFintype_apply, ENNReal.toReal_ofReal, hp1]

/-- The stationary calibration root with hazards `(a,2/3)`. -/
def approximateRoot (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Bool → PMF Bool :=
  fun who =>
    if who then
      coin (2 / 3) (by norm_num) (by norm_num)
    else coin a ha0 ha1

@[simp] theorem approximateRoot_false_true
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ((approximateRoot a ha0 ha1 false) true).toReal = a := by
  simp [approximateRoot,
    coin_true_toReal]

@[simp] theorem approximateRoot_false_false
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ((approximateRoot a ha0 ha1 false) false).toReal = 1 - a := by
  simp [approximateRoot,
    coin_false_toReal]

@[simp] theorem approximateRoot_true_true
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ((approximateRoot a ha0 ha1 true) true).toReal = 2 / 3 := by
  norm_num [approximateRoot,
    coin_true_toReal]

@[simp] theorem approximateRoot_true_false
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ((approximateRoot a ha0 ha1 true) false).toReal = 1 / 3 := by
  norm_num [approximateRoot,
    coin_false_toReal]

theorem stationaryContinueMass_approximateRoot
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    quittingStationaryContinueMass (approximateRoot a ha0 ha1) =
      (1 - a) / 3 := by
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply]
  simp [quittingAllContinueAction]
  ring

theorem rootAbsorptionMass_approximateRoot
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    quittingRootAbsorptionMass (approximateRoot a ha0 ha1) =
      (a + 2) / 3 := by
  rw [quittingRootAbsorptionMass,
    stationaryContinueMass_approximateRoot]
  ring

theorem rootAbsorbingContribution_approximateRoot_false
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    quittingRootAbsorbingContribution reward
        (approximateRoot a ha0 ha1) false = -(a + 2) / 3 := by
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix
    reward (0 : Payoff Bool) (approximateRoot a ha0 ha1) false
  rw [false_quitPayoff, false_continuePayoff] at hmix
  change quittingRootExpectedPayoff reward (0 : Payoff Bool)
    (approximateRoot a ha0 ha1) false = -(a + 2) / 3
  change quittingRootExpectedPayoff reward (0 : Payoff Bool)
    (approximateRoot a ha0 ha1) false = _ at hmix
  rw [hmix]
  simp only [approximateRoot_false_true, approximateRoot_false_false,
    approximateRoot_true_true, approximateRoot_true_false, Pi.zero_apply,
    mul_zero, add_zero]
  ring

theorem rootAbsorbingContribution_approximateRoot_true
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    quittingRootAbsorbingContribution reward
        (approximateRoot a ha0 ha1) true = (a - 2) / 3 := by
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix
    reward (0 : Payoff Bool) (approximateRoot a ha0 ha1) true
  rw [true_quitPayoff, true_continuePayoff] at hmix
  change quittingRootExpectedPayoff reward (0 : Payoff Bool)
    (approximateRoot a ha0 ha1) true = (a - 2) / 3
  change quittingRootExpectedPayoff reward (0 : Payoff Bool)
    (approximateRoot a ha0 ha1) true = _ at hmix
  rw [hmix]
  simp only [approximateRoot_false_true, approximateRoot_false_false,
    approximateRoot_true_true, approximateRoot_true_false, Pi.zero_apply,
    mul_zero, add_zero]
  ring

/-- The stationary terminal payoff is
`(-1, (a-2)/(a+2))`. -/
theorem terminalPayoff_approximateRoot
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (who : Bool) :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward (approximateRoot a ha0 ha1)) who =
      if who then (a - 2) / (a + 2) else -1 := by
  have hcontinue :
      quittingStationaryContinueMass (approximateRoot a ha0 ha1) < 1 := by
    rw [stationaryContinueMass_approximateRoot]
    nlinarith
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div
    reward (approximateRoot a ha0 ha1) who hcontinue,
    stationaryContinueMass_approximateRoot]
  have hden : a + 2 ≠ 0 := by nlinarith
  have hden' : 2 + a ≠ 0 := by nlinarith
  have hscaledDen : (a + 2) / 3 ≠ 0 := div_ne_zero hden (by norm_num)
  rw [show 1 - (1 - a) / 3 = (a + 2) / 3 by ring]
  cases who
  · rw [rootAbsorbingContribution_approximateRoot_false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply (div_eq_iff hscaledDen).2
    ring
  · rw [rootAbsorbingContribution_approximateRoot_true]
    simp only [if_true]
    field_simp [hden, hden', hscaledDen]

theorem unilateralCap_approximateRoot_false
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    quittingStationaryUnilateralCap reward
        (approximateRoot a ha0 ha1) false = -1 := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [stationaryFixedOpponentsQuitValue_false,
    stationaryFixedOpponentsContinueReward_false,
    stationaryFixedOpponentsContinueMass_false]
  norm_num

theorem unilateralCap_approximateRoot_true
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hapositive : 0 < a) :
    quittingStationaryUnilateralCap reward
        (approximateRoot a ha0 ha1) true = a - 1 := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [stationaryFixedOpponentsQuitValue_true,
    stationaryFixedOpponentsContinueReward_true,
    stationaryFixedOpponentsContinueMass_true]
  rw [approximateRoot_false_true, approximateRoot_false_false]
  have hane : a ≠ 0 := ne_of_gt hapositive
  rw [show -a / (1 - (1 - a)) = -1 by
    field_simp [hane]
    ring]
  rw [max_eq_left]
  linarith

/-- Exact error of the vanishing-hazard stationary family. -/
def approximationError (a : ℝ) : ℝ := a ^ 2 / (a + 2)

theorem approximationError_nonneg
    (a : ℝ) (ha0 : 0 ≤ a) : 0 ≤ approximationError a := by
  unfold approximationError
  positivity

/-- Every behavioral unilateral deviation is capped with error
`a²/(a+2)`. -/
theorem isεAsymptoticNash_approximateRoot
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hapositive : 0 < a) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (approximationError a)
      (quittingStationaryProfile reward (approximateRoot a ha0 ha1)) := by
  apply isεAsymptoticNash_stationary_of_unilateralCap_le
  · intro who
    cases who
    · rw [stationaryFixedOpponentsContinueMass_false]
      norm_num
    · rw [stationaryFixedOpponentsContinueMass_true]
      simp
      linarith
  · intro who
    cases who
    · rw [unilateralCap_approximateRoot_false,
        terminalPayoff_approximateRoot]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact le_add_of_nonneg_right (approximationError_nonneg a ha0)
    · rw [unilateralCap_approximateRoot_true a ha0 ha1 hapositive,
        terminalPayoff_approximateRoot]
      simp only [if_true]
      unfold approximationError
      have hden : a + 2 ≠ 0 := by nlinarith
      field_simp [hden]
      ring_nf
      rfl

/-- A concrete positive hazard tending to zero. -/
def smallHazard (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem smallHazard_pos (n : ℕ) : 0 < smallHazard n := by
  unfold smallHazard
  positivity

theorem smallHazard_le_one (n : ℕ) : smallHazard n ≤ 1 := by
  unfold smallHazard
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  exact (div_le_one (by positivity)).2 (by linarith)

/-- The stationary calibration errors converge to zero. -/
theorem tendsto_approximationError_smallHazard :
    Filter.Tendsto (fun n : ℕ ↦ approximationError (smallHazard n))
      Filter.atTop (nhds 0) := by
  have hhazard : Filter.Tendsto smallHazard Filter.atTop (nhds 0) := by
    rw [show smallHazard = (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) by rfl]
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcontinuous : ContinuousAt (fun a : ℝ ↦ a ^ 2 / (a + 2)) 0 := by
    exact (continuousAt_id.pow 2).div
      (continuousAt_id.add continuousAt_const) (by norm_num)
  simpa [approximationError, Function.comp_def] using
    hcontinuous.tendsto.comp hhazard

/-- Consequently the same game has exact stationary
`approximationError(smallHazard n)`-equilibria for every `n`, with errors
tending to zero. -/
theorem stationary_approximation_family (n : ℕ) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (approximationError (smallHazard n))
      (quittingStationaryProfile reward
        (approximateRoot (smallHazard n) (smallHazard_pos n).le
          (smallHazard_le_one n))) :=
  isεAsymptoticNash_approximateRoot
    (smallHazard n) (smallHazard_pos n).le (smallHazard_le_one n)
      (smallHazard_pos n)

/-- In particular, neither stationary singleton-First root is an exact
terminal equilibrium. -/
theorem no_stationary_singletonFirst_exact_terminal_equilibrium
    (owner : Bool) (hazard : PMF Bool)
    (_hpositive : 0 < (hazard true).toReal) :
    ¬ (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot owner hazard)) :=
  no_stationary_exact_terminal_equilibrium
    (quittingSoloStationaryRoot owner hazard)

/-- The exact regression packet: positive debt and a nonvanishing strict
joining-loss atom coexist with failure of every stationary terminal
fallback. -/
theorem positive_packet_without_stationary_fallback :
    0 < currentDebt false ∧
    0 < (root true true).toReal ∧
    0 < reward (quittingSingletonTerminal true) false -
      reward ⟨{false, true}, by simp⟩ false ∧
    (∀ selectedRoot : Bool → PMF Bool,
      ¬ (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward selectedRoot)) := by
  refine ⟨by norm_num [currentDebt], terminalOpponentAtom_nonvanishing,
    ?_, no_stationary_exact_terminal_equilibrium⟩
  rw [terminalOpponentAtom_joiningLoss_eq_one]
  norm_num

end QuittingTerminalPacketSimpleFallbackCounterexample

end GameTheory
