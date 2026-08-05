/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteDynamicDebtChains
import GameTheory.Concepts.Stochastic.QuittingFiniteNashBellmanMinimizer
import GameTheory.Concepts.Stochastic.QuittingExactDynamicDebtVanishingCounterexample

/-!
# A two-player table with a debt plateau inside the zero-pinned chain family

The table is

`r({1}) = (1/4, 0)`, `r({2}) = (1, -1/4)`, `r({1,2}) = (3/4, 1/4)`,

with `max 0 r_1({1}) = 1/4 > 0` and `max 0 r_2({2}) = 0`.

## What is shown

Within the *zero-pinned* exact zero-boundary Nash--Bellman chain family
(`quittingFiniteZeroBoundaryNashBellmanChainSet`, which forces the displayed
payoff to be exactly `0` at the chain's terminal state), the optimized
finite-chain dynamic debt stays bounded away from zero.  For every cutoff
`cutoff = m ≥ 1` we exhibit an explicit legal chain `plateauPath cutoff`
whose date-zero exact dynamic debt is literally `(1/8, 0)`, independent of
`cutoff`.  Its structure is:

* rows `0, …, m - 2` (if any) are the all-Continue root, carrying zero
  absorption mass and zero opponent-only hazard, and preserve a constant
  displayed payoff `(1/2, 0)`;
* row `m - 1`, the last row, is the exact (`ε = 0`) zero-tail Nash root at
  which both players Quit with probability one half.  It carries all of the
  chain's absorption mass, `3/4`.

The all-Continue prefix can be made arbitrarily long: the entire absorbing
mass recedes into a single terminal row as the cutoff grows, while the
date-zero debt itself stays pinned at `1/8`.

We prove this explicit chain is legal and compute its exact dynamic debt
directly, for both players, at every cutoff.  We do **not** prove that this
chain is the debt-minimizing chain at each cutoff; that stronger optimality
statement is not established here.  A hand computation (not formalized in
this file) suggests the zero-tail root at row `m - 1` is the *unique* exact
endpoint-Nash root against a zero continuation value for this table, which
would be the structural reason a minimizing search cannot avoid this
positive-debt row -- but that uniqueness claim itself carries no Lean proof
here and should be treated as an unverified hint, not a theorem.

## What is not shown

This file does **not** show that the underlying game is hard, and does
**not** show that equilibrium fails for this table.  The zero-boundary chain
family pins the terminal continuation to exactly `0`; an actual equilibrium
of the quitting game need not respect that pin, so it may lie entirely
outside the geometry this file explores.  Two-player quitting games are
known externally to admit stationary approximate equilibria for every
positive error (Solan--Vieille, *Quitting Games -- An Example*, 2002, §2.1,
citing Flesch--Thuijsman--Vrieze 1996), so nothing here suggests this table
poses any obstruction to approximate equilibrium.

The positive plateau proved below may simply be an artifact of pinning the
terminal continuation to zero rather than a property of the game.  A
by-hand (unformalized) check at the end of this file, done at the
coordinator's request, finds a candidate exact zero-debt stationary
equilibrium for this exact table once the terminal continuation is freed --
consistent with exactly that "pinning artifact" reading.  See the postscript
after `plateauPath_dynamicDebt` below for the computation and its caveats.

That check has since been turned into Lean theorems: the final section of
this file proves `stationaryRoot_isEndpointNash` (an exact, `ε = 0`,
endpoint-Nash certificate for the stationary row against its own value
`(1/4, 0)`) and `quittingConstantDynamicDebt_eq_zero` (the same dynamic-debt
recursion, run against that free continuation with terminal debt `0`, is
exactly zero at every fuel and start, for both players).  So the `1/8`
plateau is manufactured by the zero pin, not by the game.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
  Math.ProbabilityMassFunction

namespace QuittingPositiveDebtPlateauTable

/-! We use `false` for player one and `true` for player two, following the
established convention. -/

/-- The reward table `r({1}) = (1/4, 0)`, `r({2}) = (1, -1/4)`, and
`r({1,2}) = (3/4, 1/4)`. -/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if false ∈ quitters.1 then
      if true ∈ quitters.1 then
        if who then 1 / 4 else 3 / 4
      else
        if who then 0 else 1 / 4
    else
      if who then -1 / 4 else 1

/-- Player one's positive-singleton debt cap is `1/4`. -/
@[simp] theorem positiveSingletonDebtCap_false :
    quittingPositiveSingletonDebtCap reward false = 1 / 4 := by
  norm_num [quittingPositiveSingletonDebtCap, reward, quittingSingletonTerminal]

/-- Player two's positive-singleton debt cap is `0`. -/
@[simp] theorem positiveSingletonDebtCap_true :
    quittingPositiveSingletonDebtCap reward true = 0 := by
  norm_num [quittingPositiveSingletonDebtCap, reward, quittingSingletonTerminal]

/-! ## The terminal row: both players Quit with probability one half -/

/-- Both players independently Quit with probability one half. -/
def terminalRoot : Bool → PMF Bool := fun _ => PMF.uniformOfFintype Bool

/-- The exact zero-tail value of the terminal row, `(1/2, 0)`. -/
def terminalValue : Payoff Bool := fun who => if who then 0 else 1 / 2

/-- Simplex presentation of `terminalRoot`. -/
def terminalSimplexRoot : QuittingRootSimplex Bool :=
  fun who => stdSimplexEquiv (terminalRoot who)

/-- The current point of the terminal row. -/
def terminalCurrent : QuittingNashBellmanPoint Bool :=
  (terminalValue, terminalSimplexRoot)

/-- Expand a Boolean product expectation into nested single-player
expectations, reusing the repo's general two-player unfolding. -/
theorem expect_pmfPi_bool (selectedRoot : Bool → PMF Bool)
    (f : (Bool → Bool) → ℝ) :
    expect (pmfPi selectedRoot) f =
      expect (selectedRoot false) (fun first ↦
        expect (selectedRoot true) (fun second ↦
          f (fun who ↦ if who then second else first))) :=
  QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool
    selectedRoot f

/-- `terminalRoot` unfolds to the uniform coin at every player. -/
@[simp] theorem terminalRoot_apply (who : Bool) :
    terminalRoot who = PMF.uniformOfFintype Bool := rfl

/-- The simplex terminal root converts back to `terminalRoot`. -/
@[simp] theorem quittingRootOfSimplex_terminalSimplexRoot :
    quittingRootOfSimplex terminalSimplexRoot = terminalRoot := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (terminalRoot who)

/-- Player one's pure-Quit endpoint at the terminal row is `1/2`. -/
theorem quitPayoff_terminalRoot_false :
    quittingRootQuitPayoff reward (0 : Payoff Bool) terminalRoot false = 1 / 2 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [quittingRootPayoff, reward, terminalRoot, PMF.uniformOfFintype_apply,
    quittingSingletonTerminal]

/-- Player one's pure-Continue endpoint at the terminal row is `1/2`. -/
theorem continuePayoff_terminalRoot_false :
    quittingRootContinuePayoff reward (0 : Payoff Bool) terminalRoot false = 1 / 2 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [quittingRootPayoff, reward, terminalRoot, PMF.uniformOfFintype_apply,
    quittingSingletonTerminal]

/-- Player two's pure-Quit endpoint at the terminal row is `0`. -/
theorem quitPayoff_terminalRoot_true :
    quittingRootQuitPayoff reward (0 : Payoff Bool) terminalRoot true = 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [quittingRootPayoff, reward, terminalRoot, PMF.uniformOfFintype_apply,
    quittingSingletonTerminal]

/-- Player two's pure-Continue endpoint at the terminal row is `0`. -/
theorem continuePayoff_terminalRoot_true :
    quittingRootContinuePayoff reward (0 : Payoff Bool) terminalRoot true = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  norm_num [quittingRootPayoff, reward, terminalRoot, PMF.uniformOfFintype_apply,
    quittingSingletonTerminal]

/-- Both players are exactly indifferent at the terminal row. -/
theorem terminalRoot_isEndpointNash_zero :
    IsεQuittingRootEndpointNash reward (0 : Payoff Bool) 0 terminalRoot := by
  intro who
  cases who
  · rw [quittingRootEndpointDifference, quitPayoff_terminalRoot_false,
      continuePayoff_terminalRoot_false]
    norm_num
  · rw [quittingRootEndpointDifference, quitPayoff_terminalRoot_true,
      continuePayoff_terminalRoot_true]
    norm_num

/-- The terminal row sends the zero tail to `terminalValue`. -/
theorem terminalRoot_successor_zero :
    quittingRootSuccessorPayoff reward (0 : Payoff Bool) terminalRoot =
      terminalValue := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  cases who
  · rw [quitPayoff_terminalRoot_false, continuePayoff_terminalRoot_false]
    norm_num [terminalRoot, PMF.uniformOfFintype_apply, terminalValue]
  · rw [quitPayoff_terminalRoot_true, continuePayoff_terminalRoot_true]
    norm_num [terminalRoot, PMF.uniformOfFintype_apply, terminalValue]

/-- The terminal row's total absorption mass is `3/4`. -/
theorem terminalRoot_absorptionMass :
    quittingRootAbsorptionMass terminalRoot = 3 / 4 := by
  unfold quittingRootAbsorptionMass quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  norm_num [quittingAllContinueAction, terminalRoot, PMF.uniformOfFintype_apply,
    Fintype.prod_bool]

/-- The terminal row is an exact zero-boundary Nash--Bellman edge into any
state whose displayed payoff is zero. -/
theorem terminal_edge (successor : QuittingNashBellmanPoint Bool)
    (hsuccessor : successor.1 = (0 : Payoff Bool)) :
    IsQuittingNashBellmanEdge reward terminalCurrent successor := by
  constructor
  · rw [hsuccessor]
    simpa [terminalCurrent, quittingRootOfSimplex_terminalSimplexRoot] using
      terminalRoot_successor_zero.symm
  · rw [hsuccessor]
    simpa [terminalCurrent, quittingRootOfSimplex_terminalSimplexRoot] using
      terminalRoot_isEndpointNash_zero

/-! ## All-Continue rows -/

/-- Pure Quit against the all-Continue opponent receives the singleton
reward, independent of the continuation value. -/
@[simp] theorem quitPayoff_allContinue (tail : Payoff Bool) (who : Bool) :
    quittingRootQuitPayoff reward tail quittingAllContinueRoot who =
      reward (quittingSingletonTerminal who) who := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;>
    simp [quittingAllContinueRoot, quittingRootPayoff, reward,
      quittingSingletonTerminal]

/-- Pure Continue against the all-Continue opponent preserves the
continuation value. -/
@[simp] theorem continuePayoff_allContinue (tail : Payoff Bool) (who : Bool) :
    quittingRootContinuePayoff reward tail quittingAllContinueRoot who =
      tail who := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;> simp [quittingAllContinueRoot, quittingRootPayoff]

/-- Every all-Continue row carries zero absorption mass: opponent-only
hazard vanishes there. -/
theorem allContinueRoot_absorptionMass :
    quittingRootAbsorptionMass (quittingAllContinueRoot : Bool → PMF Bool) = 0 := by
  unfold quittingRootAbsorptionMass quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  norm_num [quittingAllContinueAction, quittingAllContinueRoot, Fintype.prod_bool]

/-- Player one's singleton reward is below the terminal-row value. -/
theorem singleton_false_le_terminalValue :
    reward (quittingSingletonTerminal false) false ≤ terminalValue false := by
  norm_num [reward, quittingSingletonTerminal, terminalValue]

/-- Player two's singleton reward is below the terminal-row value. -/
theorem singleton_true_le_terminalValue :
    reward (quittingSingletonTerminal true) true ≤ terminalValue true := by
  norm_num [reward, quittingSingletonTerminal, terminalValue]

/-- The all-Continue root is exact endpoint Nash against any tail dominating
both singleton rewards. -/
theorem allContinueRoot_isEndpointNash (tail : Payoff Bool)
    (hfalse : reward (quittingSingletonTerminal false) false ≤ tail false)
    (htrue : reward (quittingSingletonTerminal true) true ≤ tail true) :
    IsεQuittingRootEndpointNash reward tail 0 quittingAllContinueRoot := by
  intro who
  cases who
  · rw [quittingRootEndpointDifference, quitPayoff_allContinue,
      continuePayoff_allContinue]
    constructor
    · simp [quittingAllContinueRoot]
      linarith
    · simp [quittingAllContinueRoot]
  · rw [quittingRootEndpointDifference, quitPayoff_allContinue,
      continuePayoff_allContinue]
    constructor
    · simp [quittingAllContinueRoot]
      linarith
    · simp [quittingAllContinueRoot]

/-- An all-Continue row is an exact Nash--Bellman edge into any state whose
displayed payoff is `terminalValue`. -/
theorem allContinue_edge (successor : QuittingNashBellmanPoint Bool)
    (hsuccessor : successor.1 = terminalValue) :
    IsQuittingNashBellmanEdge reward
      (terminalValue, quittingAllContinueSimplexRoot) successor := by
  constructor
  · rw [hsuccessor]
    simpa [quittingRootOfSimplex_allContinueSimplexRoot] using
      (quittingRootSuccessorPayoff_allContinueRoot_eq reward terminalValue).symm
  · rw [hsuccessor, quittingRootOfSimplex_allContinueSimplexRoot]
    exact allContinueRoot_isEndpointNash terminalValue
      singleton_false_le_terminalValue singleton_true_le_terminalValue

/-! ## The explicit chain -/

/-- The `ℕ`-indexed state family: `terminalValue` paired with the
all-Continue root before the last row `cutoff - 1`, `terminalValue` paired
with the terminal root exactly at row `cutoff - 1`, and the zero terminal
state from `cutoff` onward. -/
def plateauState (cutoff time : ℕ) : QuittingNashBellmanPoint Bool :=
  if time < cutoff then
    (terminalValue,
      if time + 1 = cutoff then terminalSimplexRoot
      else quittingAllContinueSimplexRoot)
  else
    ((0 : Payoff Bool), quittingAllContinueSimplexRoot)

/-- The explicit `cutoff`-chain, restricting `plateauState` to
`Fin (cutoff + 1)`. -/
def plateauPath (cutoff : ℕ) : QuittingFiniteNashBellmanPath Bool cutoff :=
  fun time => plateauState cutoff time

/-- The displayed payoff of `plateauState` is `terminalValue` before the
cutoff and zero from the cutoff onward. -/
theorem plateauState_fst (cutoff time : ℕ) :
    (plateauState cutoff time).1 = if time < cutoff then terminalValue else 0 := by
  unfold plateauState
  split_ifs <;> rfl

/-- The operational root read off `plateauState` is the terminal root
exactly at row `cutoff - 1` and all-Continue everywhere else. -/
theorem plateauState_snd (cutoff time : ℕ) :
    quittingRootOfSimplex (plateauState cutoff time).2 =
      if time + 1 = cutoff then terminalRoot else quittingAllContinueRoot := by
  by_cases hlast : time + 1 = cutoff
  · have hlt : time < cutoff := by omega
    simp [plateauState, hlt, hlast, quittingRootOfSimplex_terminalSimplexRoot]
  · by_cases hlt : time < cutoff
    · simp [plateauState, hlt, hlast, quittingRootOfSimplex_allContinueSimplexRoot]
    · simp [plateauState, hlt, hlast, quittingRootOfSimplex_allContinueSimplexRoot]

/-- The canonical reward bound for this table is at least `1`. -/
theorem one_le_quittingRewardBound : (1 : ℝ) ≤ quittingRewardBound reward := by
  have h := abs_reward_le_quittingRewardBound reward
    (quittingSingletonTerminal true) false
  norm_num [reward, quittingSingletonTerminal] at h
  linarith

/-- Every displayed `plateauState` lies in the canonical compact box. -/
theorem plateauState_mem_box (cutoff time : ℕ) :
    plateauState cutoff time ∈ quittingNashBellmanBox (quittingRewardBound reward) := by
  have hbound := one_le_quittingRewardBound
  have hbound0 : (0 : ℝ) ≤ quittingRewardBound reward := by linarith
  rw [quittingNashBellmanBox, Set.mem_setOf_eq, plateauState_fst]
  split_ifs with htime
  · refine ⟨fun who => ?_, fun who => ?_⟩ <;>
      (cases who <;> simp [terminalValue] <;> linarith)
  · refine ⟨fun who => ?_, fun who => ?_⟩ <;> (simp; linarith)

/-- The explicit chain is an admissible zero-boundary exact Nash--Bellman
chain at every cutoff. -/
theorem plateauPath_mem (cutoff : ℕ) :
    plateauPath cutoff ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff := by
  refine ⟨fun time => plateauState_mem_box cutoff time, ?_, ?_⟩
  · change (plateauState cutoff cutoff).1 = 0
    rw [plateauState_fst, if_neg (lt_irrefl cutoff)]
  · intro t
    change IsQuittingNashBellmanEdge reward
      (plateauState cutoff t.val) (plateauState cutoff (t.val + 1))
    by_cases hlast : t.val + 1 = cutoff
    · have hlt : t.val < cutoff := by omega
      have hcurrent : plateauState cutoff t.val = terminalCurrent := by
        simp [plateauState, terminalCurrent, hlt, hlast]
      rw [hcurrent]
      apply terminal_edge
      rw [plateauState_fst, if_neg (show ¬ t.val + 1 < cutoff by omega)]
    · have hlt : t.val < cutoff := t.isLt
      have hcurrent : plateauState cutoff t.val =
          (terminalValue, quittingAllContinueSimplexRoot) := by
        simp [plateauState, hlt, hlast]
      rw [hcurrent]
      apply allContinue_edge
      rw [plateauState_fst, if_pos (show t.val + 1 < cutoff by omega)]

/-- The operational value extension of the explicit chain agrees with
`plateauState`'s displayed payoff at every `ℕ` time, including padding. -/
theorem plateauPathValue_eq (cutoff time : ℕ) :
    quittingFiniteNashBellmanPathValue cutoff (plateauPath cutoff) time =
      (plateauState cutoff time).1 := by
  unfold quittingFiniteNashBellmanPathValue plateauPath
  split_ifs with h
  · rfl
  · rw [plateauState_fst, if_neg (show ¬ time < cutoff by omega)]

/-- The operational root extension of the explicit chain agrees with
`plateauState`'s root at every `ℕ` time, including padding. -/
theorem plateauPathRoots_eq (cutoff time : ℕ) :
    quittingFiniteNashBellmanPathRoots cutoff (plateauPath cutoff) time =
      if time + 1 = cutoff then terminalRoot else quittingAllContinueRoot := by
  unfold quittingFiniteNashBellmanPathRoots
  by_cases hlt : time < cutoff
  · rw [dif_pos hlt]
    simpa [plateauPath] using plateauState_snd cutoff time
  · rw [dif_neg hlt, if_neg (show ¬ time + 1 = cutoff by omega)]

/-- **Absorption-mass structure of the explicit chain.**  Every row before
the last carries zero absorption mass; the last row, `cutoff - 1`, carries
all `3/4` of it.  This is the concrete statement behind "an arbitrarily long
inert region followed by a single terminal row carrying all the mass". -/
theorem plateauPathRoots_absorptionMass (cutoff time : ℕ) :
    quittingRootAbsorptionMass
        (quittingFiniteNashBellmanPathRoots cutoff (plateauPath cutoff) time) =
      if time + 1 = cutoff then 3 / 4 else 0 := by
  rw [plateauPathRoots_eq]
  split_ifs with h
  · exact terminalRoot_absorptionMass
  · exact allContinueRoot_absorptionMass

/-! ## The exact dynamic debt of the explicit chain -/

/-- Player `who`'s one-stage Quit value at the terminal row `cutoff - 1`. -/
theorem quittingFixedOpponentsQuitValue_terminalRow (cutoff : ℕ) (who : Bool)
    (time : ℕ) (htime : time + 1 = cutoff) :
    quittingFixedOpponentsQuitValue reward
        (quittingFiniteNashBellmanPathRoots cutoff (plateauPath cutoff)) who time =
      quittingRootQuitPayoff reward (0 : Payoff Bool) terminalRoot who := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
    (quittingFiniteNashBellmanPathRoots cutoff (plateauPath cutoff)) who
    (0 : Payoff Bool) time, plateauPathRoots_eq, if_pos htime]

/-- Player `who`'s one-stage Continue reward at the terminal row
`cutoff - 1`. -/
theorem quittingFixedOpponentsContinueReward_terminalRow (cutoff : ℕ) (who : Bool)
    (time : ℕ) (htime : time + 1 = cutoff) :
    quittingFixedOpponentsContinueReward reward
        (quittingFiniteNashBellmanPathRoots cutoff (plateauPath cutoff)) who time =
      quittingRootContinuePayoff reward (0 : Payoff Bool) terminalRoot who := by
  have h := quittingRootContinuePayoff_eq_fixedOpponents reward
    (quittingFiniteNashBellmanPathRoots cutoff (plateauPath cutoff)) who
    (0 : Payoff Bool) time
  rw [plateauPathRoots_eq, if_pos htime] at h
  simpa using h.symm

/-- The one-stage opponent-Continue mass at the terminal row `cutoff - 1`
is `1/2`, both players' marginals being uniform. -/
theorem quittingFixedOpponentsContinueMass_terminalRow (cutoff : ℕ) (who : Bool)
    (time : ℕ) (htime : time + 1 = cutoff) :
    quittingFixedOpponentsContinueMass
        (quittingFiniteNashBellmanPathRoots cutoff (plateauPath cutoff)) who time =
      1 / 2 := by
  unfold quittingFixedOpponentsContinueMass
  rw [plateauPathRoots_eq, if_pos htime]
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  cases who <;>
    norm_num [quittingAllContinueAction, terminalRoot, PMF.uniformOfFintype_apply,
      Function.update, Fintype.prod_bool]

/-- Player `who`'s one-stage Quit value at an all-Continue row is the
singleton reward, independent of `tail`. -/
theorem quittingFixedOpponentsQuitValue_allContinueRow (cutoff : ℕ) (who : Bool)
    (time : ℕ) (htime : time + 1 ≠ cutoff) :
    quittingFixedOpponentsQuitValue reward
        (quittingFiniteNashBellmanPathRoots cutoff (plateauPath cutoff)) who time =
      reward (quittingSingletonTerminal who) who := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
    (quittingFiniteNashBellmanPathRoots cutoff (plateauPath cutoff)) who
    (0 : Payoff Bool) time, plateauPathRoots_eq, if_neg htime, quitPayoff_allContinue]

/-- Player `who`'s one-stage Continue reward at an all-Continue row
vanishes. -/
theorem quittingFixedOpponentsContinueReward_allContinueRow (cutoff : ℕ) (who : Bool)
    (time : ℕ) (htime : time + 1 ≠ cutoff) :
    quittingFixedOpponentsContinueReward reward
        (quittingFiniteNashBellmanPathRoots cutoff (plateauPath cutoff)) who time =
      0 := by
  have h := quittingRootContinuePayoff_eq_fixedOpponents reward
    (quittingFiniteNashBellmanPathRoots cutoff (plateauPath cutoff)) who
    (0 : Payoff Bool) time
  rw [plateauPathRoots_eq, if_neg htime, continuePayoff_allContinue] at h
  simpa using h.symm

/-- The one-stage opponent-Continue mass at an all-Continue row is `1`. -/
theorem quittingFixedOpponentsContinueMass_allContinueRow (cutoff : ℕ) (who : Bool)
    (time : ℕ) (htime : time + 1 ≠ cutoff) :
    quittingFixedOpponentsContinueMass
        (quittingFiniteNashBellmanPathRoots cutoff (plateauPath cutoff)) who time =
      1 := by
  unfold quittingFixedOpponentsContinueMass
  rw [plateauPathRoots_eq, if_neg htime]
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  cases who <;>
    norm_num [quittingAllContinueAction, quittingAllContinueRoot, Function.update,
      Fintype.prod_bool]

/-- The target playerwise exact dynamic debt: `1/8` for player one, `0` for
player two. -/
def target : Payoff Bool := fun who => if who then 0 else 1 / 8

/-- The core backward induction: at every row before the cutoff, the exact
dynamic debt of the explicit chain is already `target who`, independent of
how many all-Continue rows precede the terminal row. -/
theorem plateauDebt_core (cutoff : ℕ) (who : Bool) :
    ∀ steps t : ℕ, t + steps + 1 = cutoff →
      quittingFiniteDynamicDebt reward
          (quittingFiniteNashBellmanPathRoots cutoff (plateauPath cutoff)) who
          (fun liveTime ↦
            quittingFiniteNashBellmanPathValue cutoff (plateauPath cutoff) liveTime who)
          (quittingPositiveSingletonDebtCap reward who) t (steps + 1) =
        target who := by
  intro steps
  induction steps with
  | zero =>
      intro t ht
      have htlast : t + 1 = cutoff := by omega
      rw [quittingFiniteDynamicDebt_succ, quittingFiniteDynamicDebt_zero]
      simp only [plateauPathValue_eq]
      rw [plateauState_fst cutoff t, if_pos (show t < cutoff by omega),
        plateauState_fst cutoff (t + 1), if_neg (show ¬ t + 1 < cutoff by omega),
        quittingFixedOpponentsQuitValue_terminalRow cutoff who t htlast,
        quittingFixedOpponentsContinueReward_terminalRow cutoff who t htlast,
        quittingFixedOpponentsContinueMass_terminalRow cutoff who t htlast]
      cases who <;>
        norm_num [quitPayoff_terminalRoot_false, quitPayoff_terminalRoot_true,
          continuePayoff_terminalRoot_false, continuePayoff_terminalRoot_true,
          terminalValue, target, positiveSingletonDebtCap_false,
          positiveSingletonDebtCap_true]
  | succ steps ih =>
      intro t ht
      have htnotlast : t + 1 ≠ cutoff := by omega
      have hnext : (t + 1) + steps + 1 = cutoff := by omega
      rw [quittingFiniteDynamicDebt_succ, ih (t + 1) hnext]
      simp only [plateauPathValue_eq]
      rw [plateauState_fst cutoff t, if_pos (show t < cutoff by omega),
        plateauState_fst cutoff (t + 1), if_pos (show t + 1 < cutoff by omega),
        quittingFixedOpponentsQuitValue_allContinueRow cutoff who t htnotlast,
        quittingFixedOpponentsContinueReward_allContinueRow cutoff who t htnotlast,
        quittingFixedOpponentsContinueMass_allContinueRow cutoff who t htnotlast]
      cases who <;>
        norm_num [terminalValue, target, reward, quittingSingletonTerminal, max_def]

/-- **Headline.**  The explicit chain `plateauPath cutoff` is, for every
positive cutoff, a legal zero-boundary exact Nash--Bellman chain whose
date-zero exact dynamic debt is literally `(1/8, 0)`, independent of the
cutoff.  Player one's debt is bounded away from zero: this is a genuine
positive plateau of the finite-chain exact-debt objective. -/
theorem plateauPath_dynamicDebt (cutoff : ℕ) (hcutoff : 0 < cutoff) :
    plateauPath cutoff ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff ∧
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff (plateauPath cutoff)
          false 0 = 1 / 8 ∧
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff (plateauPath cutoff)
          true 0 = 0 := by
  refine ⟨plateauPath_mem cutoff, ?_, ?_⟩
  · have h := plateauDebt_core cutoff false (cutoff - 1) 0 (by omega)
    simpa [quittingFiniteNashBellmanPathDynamicDebt, show cutoff - 0 = cutoff from rfl,
      show cutoff - 1 + 1 = cutoff by omega, target] using h
  · have h := plateauDebt_core cutoff true (cutoff - 1) 0 (by omega)
    simpa [quittingFiniteNashBellmanPathDynamicDebt, show cutoff - 0 = cutoff from rfl,
      show cutoff - 1 + 1 = cutoff by omega, target] using h

/-! ## Postscript: a free-continuation stationary check (not formalized)

Everything above is about the *zero-pinned* chain family.  This postscript
reports a by-hand check of whether the plateau survives once the terminal
continuation is freed to a profile's own value, per the module docstring.
**None of this postscript is a Lean proof**; it is prose only, to be
verified or refuted by later formalization work.

Consider the stationary profile in which player one (`false`) Quits with
probability `1/2` every stage and player two (`true`) never Quits: hazards
`a = 1/2`, `b = 0`.

* `quittingTerminalPayoff_soloStationary` (already proved in
  `QuittingExceptionalTailFallback.lean`) gives the free terminal payoff of
  *any* stationary profile in which player one alone has positive hazard as
  exactly `quittingSoloReward reward false = (1/4, 0)`, independent of the
  specific positive hazard chosen; in particular this covers `a = 1/2`.
* Solving the general two-hazard fixed point directly (not restricted to
  positive `a`) gives the same value at `(a, b) = (1/2, 0)`: writing
  `W(a, b)` for the self-consistent stationary terminal payoff,
  `W_true(1/2, b) = 0` for *every* `b ∈ [0, 1]` (the numerator
  `b * (-1/4 + a/2)` vanishes identically at `a = 1/2`), and
  `W_false(1/2, 0) = 1/4`, matching the solo-stationary value exactly.
* Against that free continuation `(1/4, 0)`: player one's Quit and Continue
  endpoints coincide exactly (`1/4 = 1/4`), so player one is exactly
  indifferent to their own hazard, and in particular gains nothing from the
  discontinuous full-Continue deviation, which instead yields the strictly
  worse `(0, 0)` (`quittingTerminalPayoff_quittingAlwaysContinue`).  Player
  two's Quit endpoint against the same continuation is
  `-1/4 + a/2 = -1/4 + 1/4 = 0`, exactly matching player two's own Continue
  value `0`: player two is likewise exactly indifferent between Quitting
  and never Quitting.

Both players are therefore exactly indifferent to every one of their own
unilateral one-shot choices at this profile, which is the standard
signature of an exact stationary equilibrium.  If this check is right, the
positive plateau proved above is a pinning artifact of
`quittingFiniteZeroBoundaryNashBellmanChainSet`'s zero terminal boundary for
this table too, exactly as it was for the companion table referenced in the
module docstring, and not a hard instance.

**Caveats.**  This computation is not a Lean theorem, and the author caught
and corrected one own error while producing it: an initial claim that the
solo-Quit-by-player-two profile `(a, b) = (0, 1)` was an equilibrium is
wrong -- there player two has a strictly profitable deviation to never
Quitting (from `-1/4` up to `0`), missed by naively plugging `b = 1` into
the finite two-hazard fixed-point formula without checking that player
two's own fixed-opponents-continue-mass is exactly `1` there, which
invalidates that formula.  The `(a, b) = (1/2, 0)` computation above avoids
that specific trap (`a = 1/2 > 0` keeps every relevant continuation mass
strictly below `1`), and gives an *exact* (not merely approximate)
indifference on both sides, which is reassuring, but reaching a genuine
Lean theorem would still need the same kind of behavioral-deviation
case analysis as
`QuittingTerminalPacketSimpleFallbackCounterexample.no_stationary_exact_terminal_equilibrium`
uses to rule equilibria *out*, run in the opposite direction to rule one
*in*.  Treat the indifference computation above as a lead, not a result.

**Update.**  The endpoint half of the lead is no longer prose: the section
below formalizes it.  `stationaryRoot_isEndpointNash` is the exact
(`ε = 0`) endpoint-Nash certificate at `(a, b) = (1/2, 0)` against the free
continuation `(1/4, 0)`, `stationaryRoot_successor_eq` verifies that this
continuation is that row's own value (so the profile really is stationary),
and `quittingConstantDynamicDebt_eq_zero` computes the dynamic debt against
it as exactly `0` at every fuel and start, for both players.  What is still
prose is only the *behavioral* deviation analysis (deviations that are not
unilateral one-shot root deviations); the endpoint certificate is the same
kind of certificate the zero-pinned chain family above is built from, so it
is exactly the right comparison object for the plateau claim.
-/

/-! ## The `1/8` plateau is manufactured by the zero pin

Everything before this point pins the terminal continuation to `0`.  Freeing
it to the game's own stationary value `(1/4, 0)` erases the plateau
completely.  The declarations here mirror
`QuittingBoundedSurgeryDescentCounterexample.stationaryRoot_isEndpointNash`
and `.quittingConstantDynamicDebt_eq_zero` for this table.
-/

/-! ### Exact root endpoint formulas for this table -/

/-- Player one's pure-Quit endpoint is `1/4 + q/2`, where `q` is player two's
Quit probability.  It does not depend on the continuation value. -/
theorem false_quitPayoff (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff reward tail root false =
      1 / 4 + (root true true).toReal / 2 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  have hc : (root true false).toReal = 1 - (root true true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, hc]
  ring

/-- Player one's pure-Continue endpoint is `(1 - q) tail_1 + q`, where `q` is
player two's Quit probability. -/
theorem false_continuePayoff (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootContinuePayoff reward tail root false =
      (1 - (root true true).toReal) * tail false + (root true true).toReal := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  have hc : (root true false).toReal = 1 - (root true true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, hc]
  ring

/-- Player two's pure-Quit endpoint is `p/2 - 1/4`, where `p` is player one's
Quit probability.  It does not depend on the continuation value. -/
theorem true_quitPayoff (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff reward tail root true =
      (root false true).toReal / 2 - 1 / 4 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hc : (root false false).toReal = 1 - (root false true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, hc]
  ring

/-- Player two's pure-Continue endpoint is `(1 - p) tail_2`, where `p` is
player one's Quit probability. -/
theorem true_continuePayoff (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootContinuePayoff reward tail root true =
      (1 - (root false true).toReal) * tail true := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hc : (root false false).toReal = 1 - (root false true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, hc]

/-- Player one's endpoint difference against a `(t1, 0)`-shaped tail. -/
theorem false_endpointDifference (t1 : ℝ) (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward
        (fun who => if who then (0 : ℝ) else t1) root false =
      (1 - (root true true).toReal) * (1 / 4 - t1) - (root true true).toReal / 4 := by
  rw [quittingRootEndpointDifference, false_quitPayoff, false_continuePayoff]
  simp
  ring

/-- Player two's endpoint difference against a `(t1, 0)`-shaped tail. -/
theorem true_endpointDifference (t1 : ℝ) (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward
        (fun who => if who then (0 : ℝ) else t1) root true =
      (root false true).toReal / 2 - 1 / 4 := by
  rw [quittingRootEndpointDifference, true_quitPayoff, true_continuePayoff]
  simp

/-! ### The free-continuation stationary equilibrium -/

/-- The stationary root freeing the terminal continuation: player one Quits
with probability one half at every stage, player two never Quits. -/
def stationaryRoot : Bool → PMF Bool :=
  fun who => if who then PMF.pure false else PMF.uniformOfFintype Bool

/-- The stationary root's own value, `(1/4, 0)`. -/
def stationaryValue : Payoff Bool := fun who => if who then 0 else 1 / 4

/-- `stationaryValue` in the `(t1, 0)` shape used by the endpoint-difference
formulas. -/
theorem stationaryValue_eq :
    stationaryValue = fun who => if who then (0 : ℝ) else 1 / 4 := rfl

@[simp] theorem stationaryRoot_false_true :
    (stationaryRoot false true).toReal = 1 / 2 := by
  norm_num [stationaryRoot, PMF.uniformOfFintype_apply]

@[simp] theorem stationaryRoot_false_false :
    (stationaryRoot false false).toReal = 1 / 2 := by
  norm_num [stationaryRoot, PMF.uniformOfFintype_apply]

@[simp] theorem stationaryRoot_true_true :
    (stationaryRoot true true).toReal = 0 := by simp [stationaryRoot]

/-- The stationary row absorbs with probability `1/2` at every stage.  This is
the non-degeneracy guard behind `stationaryRoot_successor_eq`: for the
all-Continue row *every* tail is a fixed point of the successor map, so a
fixed-point equation alone certifies nothing; here the row absorbs at a
uniformly positive rate, so play is absorbed with probability one and
`(1/4, 0)` is a genuine expected terminal payoff. -/
theorem stationaryRoot_absorptionMass :
    quittingRootAbsorptionMass stationaryRoot = 1 / 2 := by
  unfold quittingRootAbsorptionMass quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  norm_num [quittingAllContinueAction, stationaryRoot, PMF.uniformOfFintype_apply,
    Fintype.prod_bool]

/-- The stationary root, run against the constant continuation `(1/4, 0)`,
reproduces exactly that continuation: it is a genuine stationary root, not
merely an approximate one.  This is what makes `(1/4, 0)` the honest
continuation to compare the zero pin against. -/
theorem stationaryRoot_successor_eq :
    quittingRootSuccessorPayoff reward stationaryValue stationaryRoot =
      stationaryValue := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  cases who
  · rw [false_quitPayoff, false_continuePayoff, stationaryRoot_true_true,
      stationaryRoot_false_true, stationaryRoot_false_false]
    norm_num [stationaryValue]
  · rw [true_quitPayoff, true_continuePayoff, stationaryRoot_false_true,
      stationaryRoot_true_true]
    norm_num [stationaryValue]

/-- **The `1/8` plateau is manufactured by the zero pin, not by the game
(endpoint half).**  Against its own constant continuation `(1/4, 0)` both
players of this table are *exactly* indifferent between Quitting and
Continuing, so the stationary row is an exact (`ε = 0`) endpoint-Nash root --
the very certificate the zero-pinned chain family above is built from.  The
positive `1/8` debt therefore comes from pinning the terminal continuation
to `0` rather than to `(1/4, 0)`. -/
theorem stationaryRoot_isEndpointNash :
    IsεQuittingRootEndpointNash reward stationaryValue 0 stationaryRoot := by
  intro who
  rw [stationaryValue_eq]
  cases who
  · rw [false_endpointDifference, stationaryRoot_true_true]
    norm_num
  · rw [true_endpointDifference, stationaryRoot_false_true]
    norm_num

/-- **The `1/8` plateau is manufactured by the zero pin, not by the game
(debt half).**  Run the exact same dynamic-debt Bellman recursion used for
`plateauPath_dynamicDebt`, but against the game's own stationary
continuation `(1/4, 0)` instead of the zero-boundary pin, and with the
honest terminal debt `0` instead of the positive singleton cap: the debt is
exactly zero at every fuel, every start and both players.  Contrast
`plateauPath_dynamicDebt`, whose zero-pinned date-zero debt is the strictly
positive `1/8`. -/
theorem quittingConstantDynamicDebt_eq_zero (who : Bool) :
    ∀ fuel start : ℕ,
      quittingFiniteDynamicDebt reward (fun _ => stationaryRoot) who
        (fun _ => stationaryValue who) 0 start fuel = 0 := by
  intro fuel
  induction fuel with
  | zero => intro start; rfl
  | succ fuel ih =>
      intro start
      rw [quittingFiniteDynamicDebt_succ_eq_endpoints, ih (start + 1)]
      cases who
      · rw [false_quitPayoff, false_continuePayoff, stationaryRoot_true_true]
        norm_num [stationaryValue]
      · rw [true_quitPayoff, true_continuePayoff, stationaryRoot_false_true]
        norm_num [stationaryValue]

end QuittingPositiveDebtPlateauTable

end GameTheory
