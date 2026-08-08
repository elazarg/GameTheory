/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtChains
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Debt.Dynamic.ExactDynamicDebtVanishingCounterexample

/-!
# Zero-pinned finite chains cannot uniformly decrement their optimized debt

This is the explicit two-player table from the descent-refutation record.  For
a parameter `0 < a < 1`,

`r({1}) = (a, 0)`, `r({2}) = (1, -1)`, `r({1, 2}) = (0, 1)`.

## What this module shows

Restrict attention to the *zero-boundary* exact Nash--Bellman chain family:
finite chains whose terminal continuation is pinned to `0`, padded beyond the
cutoff by the positive singleton debt cap.  On this table that family is a
singleton at every cutoff `m`: at every backward step the stage game has a
unique Nash equilibrium, in which player two mixes half--half and player one
mixes with a hazard depending on the current tail.  The resulting value
sequence and the resulting exact dynamic debt both have exact closed forms,

`x_k = a(1 - a^k) / (1 - a^(k+1))`, `d_m = a(1 - a) / (1 - a^(m+1))`,

where `x_k` is player one's displayed payoff at reverse distance `k` from the
zero boundary and `d_m` is player one's exact dynamic debt at cutoff `m`
(player two's debt is forced to zero at every cutoff, since its terminal
singleton cap is zero).  Since the family is a singleton, `d_m` is exactly the
optimized (min-max) debt at cutoff `m`, not merely a witnessed upper bound.
The sequence `d_m` never falls below the strictly positive plateau `a(1 - a)`,
and for every fixed extra horizon length `L` the drop `d_m - d_{m+L}` tends to
zero as `m → ∞`.  **Within the zero-pinned chain family, no bounded-length
extension can decrement the optimized debt by a cutoff-independent amount.**

## What this module does not show

This is not evidence that the underlying two-player game is hard, or that it
lacks an equilibrium.  The game has an explicit exact **stationary**
equilibrium with **zero** debt: player one quits with probability `1/2` at
every stage, player two never quits, giving terminal payoff `(a, 0)`.  Both
players are exactly indifferent against that continuation: player one's
Quit endpoint is `a` and its Continue endpoint is also `a` (against the
constant continuation `a`), while player two's Quit endpoint is
`2 * (1/2) - 1 = 0` and its Continue endpoint is `(1/2) * 0 = 0` (against the
constant continuation `0`).  See `stationaryRoot_isEndpointNash` below, an
exact (`ε = 0`) endpoint-Nash certificate, not merely an approximate one.

The positive plateau `d_m → a(1 - a)` is manufactured entirely by pinning the
terminal continuation to `0` rather than to the game's own equilibrium value
`(a, 0)`.  Pinning to `0` forces a strictly positive gap `a - 0 = a` at every
finite horizon between the singleton cap and the true continuation; that gap
forces the opponent's survival product strictly below `1` at every step
(since player one must mix, not play a corner action, to stay indifferent
against a nonzero tail), which is exactly what manufactures the debt.  Using
the constant continuation `(a, 0)` instead of `0` erases the gap and, with
it, the debt: see `quittingConstantDynamicDebt_eq_zero` below, which computes
the same debt recursion against the honest continuation `(a, 0)` and gets
`0` at every horizon.  The result therefore bounds the zero-pinned finite-
chain *method*, not the game.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

namespace QuittingBoundedSurgeryDescentCounterexample

/-! We use `false` for player one and `true` for player two. -/

/-- Payoffs `r({1}) = (a, 0)`, `r({2}) = (1, -1)`, and `r({1, 2}) = (0, 1)`. -/
def reward (a : ℝ) (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if false ∈ quitters.1 then
      if true ∈ quitters.1 then
        if who then 1 else 0
      else
        if who then 0 else a
    else
      if who then -1 else 1

/-- Player one's terminal singleton reward is `a`, so its positive cap is
`a`. -/
@[simp] theorem positiveSingletonDebtCap_false (a : ℝ) (ha0 : 0 < a) :
    quittingPositiveSingletonDebtCap (reward a) false = a := by
  unfold quittingPositiveSingletonDebtCap
  simp only [reward, quittingSingletonTerminal, Finset.mem_singleton]
  norm_num
  exact ha0.le

/-- Player two's terminal singleton reward is `-1`, so its positive cap is
`0`. -/
@[simp] theorem positiveSingletonDebtCap_true (a : ℝ) :
    quittingPositiveSingletonDebtCap (reward a) true = 0 := by
  unfold quittingPositiveSingletonDebtCap
  simp only [reward, quittingSingletonTerminal, Finset.mem_singleton]
  norm_num

/-- A Boolean coin, returning `true` (Quit) with probability `p`. -/
def coin (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  PMF.ofFintype
    (fun action => if action then ENNReal.ofReal p else ENNReal.ofReal (1 - p))
    (by
      rw [Fintype.sum_bool]
      simp only [if_true, if_false, Bool.false_eq_true]
      rw [← ENNReal.ofReal_add hp0 (by linarith)]
      norm_num)

@[simp] theorem coin_true_toReal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coin p hp0 hp1 true).toReal = p := by
  simp [coin, PMF.ofFintype_apply, hp0]

@[simp] theorem coin_false_toReal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coin p hp0 hp1 false).toReal = 1 - p := by
  simp [coin, PMF.ofFintype_apply, ENNReal.toReal_ofReal, hp1]

/-- A Boolean marginal with prescribed real Quit mass `p` is exactly the
`p`-coin. -/
theorem pmf_bool_eq_coin_of_apply_true_toReal_eq
    (marginal : PMF Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (htrue : (marginal true).toReal = p) :
    marginal = coin p hp0 hp1 := by
  ext action
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top marginal action)
    (PMF.apply_ne_top (coin p hp0 hp1) action)).mp
  cases action
  · have hsum : (marginal false).toReal + (marginal true).toReal = 1 := by
      simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one marginal
    rw [htrue] at hsum
    rw [coin_false_toReal p hp0 hp1]
    linarith
  · rw [coin_true_toReal p hp0 hp1]
    exact htrue

/-! ## Exact root endpoint formulas -/

/-- Player one's pure-Quit endpoint is `(1 - q) a`, where `q` is player two's
Quit probability. -/
theorem false_quitPayoff (a : ℝ) (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff (reward a) tail root false =
      (1 - (root true true).toReal) * a := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  have hc : (root true false).toReal = 1 - (root true true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, hc]

/-- Player one's pure-Continue endpoint is `(1 - q) tail_1 + q`, where `q` is
player two's Quit probability. -/
theorem false_continuePayoff (a : ℝ) (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootContinuePayoff (reward a) tail root false =
      (1 - (root true true).toReal) * tail false + (root true true).toReal := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  have hc : (root true false).toReal = 1 - (root true true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, hc]
  ring

/-- Player two's pure-Quit endpoint is `2p - 1`, where `p` is player one's
Quit probability. -/
theorem true_quitPayoff (a : ℝ) (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff (reward a) tail root true =
      2 * (root false true).toReal - 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hc : (root false false).toReal = 1 - (root false true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, hc]
  ring

/-- Player two's pure-Continue endpoint is `(1 - p) tail_2`, where `p` is
player one's Quit probability. -/
theorem true_continuePayoff (a : ℝ) (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootContinuePayoff (reward a) tail root true =
      (1 - (root false true).toReal) * tail true := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hc : (root false false).toReal = 1 - (root false true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, hc]

/-- Player one's endpoint difference against a `(t1, 0)`-shaped tail. -/
theorem false_endpointDifference (a t1 : ℝ) (root : Bool → PMF Bool) :
    quittingRootEndpointDifference (reward a)
        (fun who => if who then (0 : ℝ) else t1) root false =
      (1 - (root true true).toReal) * (a - t1) - (root true true).toReal := by
  rw [quittingRootEndpointDifference, false_quitPayoff, false_continuePayoff]
  simp
  ring

/-- Player two's endpoint difference against a `(t1, 0)`-shaped tail. -/
theorem true_endpointDifference (a t1 : ℝ) (root : Bool → PMF Bool) :
    quittingRootEndpointDifference (reward a)
        (fun who => if who then (0 : ℝ) else t1) root true =
      2 * (root false true).toReal - 1 := by
  rw [quittingRootEndpointDifference, true_quitPayoff, true_continuePayoff]
  simp

/-- Against a tail with second coordinate zero and first coordinate strictly
below `a`, exact endpoint Nash forces player one to mix half--half and
forces player two's hazard to the unique value solving player one's
indifference equation.  This is the singleton-chain uniqueness step. -/
theorem root_forced_of_endpointNash
    (a t1 : ℝ) (_ht0 : 0 ≤ t1) (ht1 : t1 < a) (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootEndpointNash (reward a)
      (fun who => if who then (0 : ℝ) else t1) 0 root) :
    (root false true).toReal = 1 / 2 ∧
      (root true true).toReal = (a - t1) / (a - t1 + 1) := by
  have hfalse := hnash false
  have htrue := hnash true
  rw [false_endpointDifference] at hfalse
  rw [true_endpointDifference] at htrue
  simp only [neg_zero] at hfalse htrue
  set p : ℝ := (root false true).toReal with hp_def
  set q : ℝ := (root true true).toReal with hq_def
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root false
    nlinarith [ENNReal.toReal_nonneg (a := root false false)]
  have hq1 : q ≤ 1 := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root true
    nlinarith [ENNReal.toReal_nonneg (a := root true false)]
  have hp : p = 1 / 2 := by
    rcases lt_trichotomy p (1 / 2) with hlt | heq | hgt
    · have hd2 : 2 * p - 1 < 0 := by linarith
      have hq_eq0 : q = 0 := by
        apply le_antisymm
        · by_contra hnot
          have hqpos : 0 < q := lt_of_not_ge hnot
          exact absurd htrue.2 (not_le.mpr (mul_neg_of_pos_of_neg hqpos hd2))
        · exact hq0
      have hcont : (root false false).toReal = 1 - p := by
        have hsum := quittingRoot_continueProbability_add_quitProbability root false
        linarith
      rw [hcont, hq_eq0] at hfalse
      nlinarith [hfalse.1, ht1]
    · exact heq
    · have hd2 : 0 < 2 * p - 1 := by linarith
      have hq_eq1 : q = 1 := by
        apply le_antisymm hq1
        by_contra hnot
        have hqlt : q < 1 := lt_of_not_ge hnot
        have hcontinue : (root true false).toReal = 1 - q := by
          have hsum := quittingRoot_continueProbability_add_quitProbability root true
          linarith
        rw [hcontinue] at htrue
        have hpos : 0 < (1 - q) * (2 * p - 1) := mul_pos (by linarith) hd2
        exact absurd htrue.1 (not_le.mpr hpos)
      rw [hq_eq1] at hfalse
      nlinarith [hfalse.2, hgt]
  refine ⟨hp, ?_⟩
  have hcont : (root false false).toReal = 1 - p := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root false
    linarith
  rw [hcont, hp] at hfalse
  have hD1le : (1 - q) * (a - t1) - q ≤ 0 := by nlinarith [hfalse.1]
  have hD1ge : 0 ≤ (1 - q) * (a - t1) - q := by nlinarith [hfalse.2]
  have hD1 : (1 - q) * (a - t1) - q = 0 := le_antisymm hD1le hD1ge
  have hne : a - t1 + 1 ≠ 0 := by linarith
  rw [eq_div_iff hne]
  nlinarith [hD1]

/-- Player one's terminal singleton reward gives a bound witness. -/
theorem le_quittingRewardBound (a : ℝ) (ha0 : 0 < a) :
    a ≤ quittingRewardBound (reward a) := by
  have h := abs_reward_le_quittingRewardBound (reward a)
    (quittingSingletonTerminal false) false
  have heq : reward a (quittingSingletonTerminal false) false = a := by
    simp [reward, quittingSingletonTerminal]
  rw [heq, abs_of_pos ha0] at h
  exact h

/-- Player two's exact dynamic debt is forced to zero at every admissible
zero-boundary chain: its terminal singleton cap is zero, and debt is
squeezed between zero and the cap. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_true_eq_zero (a : ℝ) (m : ℕ)
    (path : QuittingFiniteNashBellmanPath Bool m)
    (hpath : path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet (reward a) m) :
    quittingFiniteNashBellmanPathDynamicDebt (reward a) m path true 0 = 0 := by
  have hnn := quittingFiniteNashBellmanPathDynamicDebt_nonneg (reward a) m path hpath true 0
  have hle := quittingFiniteNashBellmanPathDynamicDebt_le_cap (reward a) m path hpath true 0
    (Nat.zero_le m)
  rw [positiveSingletonDebtCap_true a] at hle
  linarith

/-- Player one's displayed payoff at reverse distance `k` from the zero
boundary. -/
def xVal (a : ℝ) (k : ℕ) : ℝ := a * (1 - a ^ k) / (1 - a ^ (k + 1))

/-- The exact optimized dynamic-debt closed form at reverse distance `k`. -/
def dVal (a : ℝ) (k : ℕ) : ℝ := a * (1 - a) / (1 - a ^ (k + 1))

/-- Player two's Quit probability used to advance from reverse distance `k`
to reverse distance `k + 1`. -/
def p2Val (a : ℝ) (k : ℕ) : ℝ := (a - xVal a k) / (a - xVal a k + 1)

/-- The value sequence starts exactly at the zero boundary. -/
theorem xVal_zero (a : ℝ) : xVal a 0 = 0 := by simp [xVal]

/-! ## Closed forms for the forced value and debt sequences -/

section

variable (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
include ha0 ha1

/-- The debt-recursion denominator `1 - a^(k+1)` is strictly positive. -/
theorem one_sub_pow_pos (k : ℕ) : 0 < 1 - a ^ (k + 1) := by
  have h : a ^ (k + 1) < 1 := pow_lt_one₀ ha0.le ha1 (by omega)
  linarith

/-- The value sequence is nonnegative at every reverse distance. -/
theorem xVal_nonneg (k : ℕ) : 0 ≤ xVal a k := by
  unfold xVal
  have hnum : 0 ≤ 1 - a ^ k := by
    have := pow_le_one₀ ha0.le ha1.le (n := k)
    linarith
  have hden := one_sub_pow_pos a ha0 ha1 k
  positivity

/-- The value sequence stays strictly below the terminal singleton
reward `a`, so the step hazard `p2Val` is always a genuine probability. -/
theorem xVal_lt_a (k : ℕ) : xVal a k < a := by
  unfold xVal
  have hden := one_sub_pow_pos a ha0 ha1 k
  rw [div_lt_iff₀ hden]
  have hpow : a ^ (k + 1) < a ^ k := by
    rw [pow_succ]
    have hpowpos : 0 < a ^ k := pow_pos ha0 k
    nlinarith
  nlinarith

/-- The step-`k` hazard is a nonnegative real number. -/
theorem p2Val_nonneg (k : ℕ) : 0 ≤ p2Val a k := by
  unfold p2Val
  have hlt := xVal_lt_a a ha0 ha1 k
  have hden : 0 < a - xVal a k + 1 := by linarith
  positivity

/-- The step-`k` hazard is at most one. -/
theorem p2Val_le_one (k : ℕ) : p2Val a k ≤ 1 := by
  unfold p2Val
  have hlt := xVal_lt_a a ha0 ha1 k
  have hden : 0 < a - xVal a k + 1 := by linarith
  rw [div_le_one hden]
  linarith

/-- The Möbius recursion satisfied by the closed-form value sequence. -/
theorem xVal_mobius (k : ℕ) :
    xVal a (k + 1) * (a + 1 - xVal a k) = a := by
  have hden1 := (one_sub_pow_pos a ha0 ha1 k).ne'
  have hden2 := (one_sub_pow_pos a ha0 ha1 (k + 1)).ne'
  unfold xVal
  field_simp
  ring

/-- The successor value equation: player one's Quit endpoint against the
step-`k` hazard equals the closed-form value `x_{k+1}`. -/
theorem xVal_succ_eq (k : ℕ) :
    a * (1 - p2Val a k) = xVal a (k + 1) := by
  have hlt := xVal_lt_a a ha0 ha1 k
  have hne2 : a + 1 - xVal a k ≠ 0 := by linarith
  have hmobius := xVal_mobius a ha0 ha1 k
  have hxsucc : xVal a (k + 1) = a / (a + 1 - xVal a k) := by
    rw [eq_div_iff hne2]; exact hmobius
  rw [hxsucc, p2Val, show a - xVal a k + 1 = a + 1 - xVal a k by ring]
  field_simp
  ring

/-- The debt recursion: `d_{k+1} = d_k * x_{k+1} / a`. -/
theorem dVal_succ_eq (k : ℕ) :
    dVal a (k + 1) = dVal a k * (xVal a (k + 1) / a) := by
  have hden1 := (one_sub_pow_pos a ha0 ha1 k).ne'
  have hden2 := (one_sub_pow_pos a ha0 ha1 (k + 1)).ne'
  unfold dVal xVal
  field_simp

/-! ## The forced backward root and its successor equation -/

/-- The unique backward Nash root at reverse distance `k`: player one mixes
half--half and player two mixes with the hazard solving player one's
indifference equation. -/
def stepRoot (k : ℕ) : Bool → PMF Bool :=
  fun who =>
    if who then
      coin (p2Val a k) (p2Val_nonneg a ha0 ha1 k) (p2Val_le_one a ha0 ha1 k)
    else coin (1 / 2) (by norm_num) (by norm_num)

@[simp] theorem stepRoot_false_true (k : ℕ) :
    (stepRoot a ha0 ha1 k false true).toReal = 1 / 2 := by simp [stepRoot]

@[simp] theorem stepRoot_false_false (k : ℕ) :
    (stepRoot a ha0 ha1 k false false).toReal = 1 / 2 := by norm_num [stepRoot]

@[simp] theorem stepRoot_true_true (k : ℕ) :
    (stepRoot a ha0 ha1 k true true).toReal = p2Val a k := by simp [stepRoot]

/-- The forced root is exact endpoint Nash against its own tail value. -/
theorem stepRoot_isEndpointNash (k : ℕ) :
    IsεQuittingRootEndpointNash (reward a)
        (fun who => if who then (0 : ℝ) else xVal a k) 0 (stepRoot a ha0 ha1 k) := by
  have hlt := xVal_lt_a a ha0 ha1 k
  have hne : a - xVal a k + 1 ≠ 0 := by linarith
  intro who
  cases who
  · rw [false_endpointDifference, stepRoot_true_true]
    unfold p2Val
    have : (1 - (a - xVal a k) / (a - xVal a k + 1)) * (a - xVal a k) -
        (a - xVal a k) / (a - xVal a k + 1) = 0 := by
      field_simp
      ring
    rw [this]
    norm_num
  · rw [true_endpointDifference, stepRoot_false_true]
    norm_num

/-- Player one's pure-Quit endpoint at the forced step-`k` root equals the
closed-form successor value `x_{k+1}`. -/
theorem stepRoot_false_quitPayoff_eq (k : ℕ) :
    quittingRootQuitPayoff (reward a) (fun who => if who then (0 : ℝ) else xVal a k)
        (stepRoot a ha0 ha1 k) false =
      xVal a (k + 1) := by
  rw [false_quitPayoff, stepRoot_true_true, mul_comm]
  exact xVal_succ_eq a ha0 ha1 k

/-- Player one's pure-Continue endpoint at the forced step-`k` root also
equals the closed-form successor value `x_{k+1}`: the two endpoints coincide
because the step root makes player one exactly indifferent. -/
theorem stepRoot_false_continuePayoff_eq (k : ℕ) :
    quittingRootContinuePayoff (reward a) (fun who => if who then (0 : ℝ) else xVal a k)
        (stepRoot a ha0 ha1 k) false =
      xVal a (k + 1) := by
  rw [false_continuePayoff, stepRoot_true_true]
  simp only [Bool.false_eq_true, if_false]
  have hQ := xVal_succ_eq a ha0 ha1 k
  have hlt := xVal_lt_a a ha0 ha1 k
  have hne : a - xVal a k + 1 ≠ 0 := by linarith
  rw [← hQ]
  unfold p2Val
  field_simp
  ring

/-- The forced root's successor equation: since both endpoints coincide, the
successor payoff is exactly the closed-form value at reverse distance
`k + 1`, for both players simultaneously. -/
theorem stepRoot_successor_eq (k : ℕ) :
    quittingRootSuccessorPayoff (reward a)
        (fun who => if who then (0 : ℝ) else xVal a k) (stepRoot a ha0 ha1 k) =
      (fun who => if who then (0 : ℝ) else xVal a (k + 1)) := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  cases who
  · rw [stepRoot_false_quitPayoff_eq, stepRoot_false_continuePayoff_eq,
      stepRoot_false_true, stepRoot_false_false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    ring
  · rw [true_quitPayoff, true_continuePayoff, stepRoot_false_true]
    norm_num

/-! ## The forced finite zero-boundary chain -/

/-- Simplex presentation of the reverse-distance-`k` step root. -/
def stepSimplexRoot (k : ℕ) : QuittingRootSimplex Bool :=
  fun who => stdSimplexEquiv (stepRoot a ha0 ha1 k who)

@[simp] theorem quittingRootOfSimplex_stepSimplexRoot (k : ℕ) :
    quittingRootOfSimplex (stepSimplexRoot a ha0 ha1 k) = stepRoot a ha0 ha1 k := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (stepRoot a ha0 ha1 k who)

/-- One padded Nash--Bellman point at reverse distance `j` from the zero
boundary: value `x_j` for player one and `0` for player two, together with
the root used to advance from `j` to `j - 1` (irrelevant when `j = 0`, since
the chain set leaves the terminal root unconstrained). -/
def chainState (j : ℕ) : QuittingNashBellmanPoint Bool :=
  ((fun who => if who then (0 : ℝ) else xVal a j), stepSimplexRoot a ha0 ha1 (j - 1))

/-- The finite Nash--Bellman path at cutoff `m`, reading reverse distance
`m - time` at displayed time `time`. -/
def chainPath (m : ℕ) : QuittingFiniteNashBellmanPath Bool m :=
  fun time => chainState a ha0 ha1 (m - time.val)

/-- Every padded state lies in the compact Nash--Bellman box. -/
theorem chainState_mem_box (j : ℕ) :
    chainState a ha0 ha1 j ∈ quittingNashBellmanBox (quittingRewardBound (reward a)) := by
  have hM := quittingRewardBound_nonneg (reward a)
  have haM := le_quittingRewardBound a ha0
  have hx0 := xVal_nonneg a ha0 ha1 j
  have hxa := (xVal_lt_a a ha0 ha1 j).le
  change (chainState a ha0 ha1 j).1 ∈
      Set.Icc (fun _ : Bool => -(quittingRewardBound (reward a)))
        (fun _ => quittingRewardBound (reward a))
  constructor
  · intro who
    cases who <;> simp only [chainState] <;> dsimp <;> linarith
  · intro who
    cases who <;> simp only [chainState] <;> dsimp <;> linarith

/-- The reverse-distance-`0` state has zero value: the forced boundary. -/
theorem chainState_zero_value : (chainState a ha0 ha1 0).1 = 0 := by
  funext who
  cases who <;> simp [chainState, xVal_zero a]

/-- The chain's terminal displayed state has zero value. -/
theorem chainPath_last_value (m : ℕ) :
    (chainPath a ha0 ha1 m (Fin.last m)).1 = 0 := by
  have hzero : m - (Fin.last m).val = 0 := by simp
  simp only [chainPath, hzero]
  exact chainState_zero_value a ha0 ha1

/-- Every pre-terminal edge of the chain is a genuine exact Nash--Bellman
edge, using the forced backward root at the corresponding reverse
distance. -/
theorem chainPath_edge (m : ℕ) (time : Fin m) :
    IsQuittingNashBellmanEdge (reward a)
      (chainPath a ha0 ha1 m (Fin.castSucc time))
      (chainPath a ha0 ha1 m (Fin.succ time)) := by
  have hval : (Fin.castSucc time).val = time.val := rfl
  have hval' : (Fin.succ time).val = time.val + 1 := rfl
  have hj : m - time.val = (m - time.val - 1) + 1 := by omega
  have hj' : m - (time.val + 1) = m - time.val - 1 := by omega
  set k := m - time.val - 1 with hk_def
  change IsQuittingNashBellmanEdge (reward a)
      (chainState a ha0 ha1 (m - time.val)) (chainState a ha0 ha1 (m - (time.val + 1)))
  rw [hj, hj']
  constructor
  · change (fun who => if who then (0 : ℝ) else xVal a (k + 1)) =
      quittingRootSuccessorPayoff (reward a)
        (fun who => if who then (0 : ℝ) else xVal a k)
        (quittingRootOfSimplex (chainState a ha0 ha1 (k + 1)).2)
    change _ = quittingRootSuccessorPayoff (reward a) _
      (quittingRootOfSimplex (stepSimplexRoot a ha0 ha1 (k + 1 - 1)))
    simp only [Nat.add_sub_cancel]
    rw [quittingRootOfSimplex_stepSimplexRoot]
    exact (stepRoot_successor_eq a ha0 ha1 k).symm
  · change IsεQuittingRootEndpointNash (reward a)
      (fun who => if who then (0 : ℝ) else xVal a k) 0
      (quittingRootOfSimplex (chainState a ha0 ha1 (k + 1)).2)
    change IsεQuittingRootEndpointNash (reward a) _ 0
      (quittingRootOfSimplex (stepSimplexRoot a ha0 ha1 (k + 1 - 1)))
    simp only [Nat.add_sub_cancel]
    rw [quittingRootOfSimplex_stepSimplexRoot]
    exact stepRoot_isEndpointNash a ha0 ha1 k

/-- The forced chain is an admissible zero-boundary exact Nash--Bellman
chain at every cutoff. -/
theorem chainPath_mem (m : ℕ) :
    chainPath a ha0 ha1 m ∈ quittingFiniteZeroBoundaryNashBellmanChainSet (reward a) m := by
  refine ⟨fun time => chainState_mem_box a ha0 ha1 _, chainPath_last_value a ha0 ha1 m,
    fun time => chainPath_edge a ha0 ha1 m time⟩

/-! ## The chain set is a singleton -/

/-- Every admissible zero-boundary exact Nash--Bellman chain agrees with the
forced chain: its displayed value at reverse distance `remaining` from the
cutoff is the closed-form `x_remaining`, and (for a positive reverse
distance) its operational root there is the forced step root.  This is the
singleton-chain-set uniqueness claim. -/
theorem chainPath_forced (m : ℕ) (path : QuittingFiniteNashBellmanPath Bool m)
    (hpath : path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet (reward a) m)
    (remaining time : ℕ) (hsum : time + remaining = m) :
    quittingFiniteNashBellmanPathValue m path time =
        (fun who => if who then (0 : ℝ) else xVal a remaining) ∧
      (0 < remaining →
        quittingFiniteNashBellmanPathRoots m path time =
          stepRoot a ha0 ha1 (remaining - 1)) := by
  induction remaining generalizing time with
  | zero =>
      refine ⟨?_, fun h => (Nat.lt_irrefl 0 h).elim⟩
      have htime : time = m := by omega
      subst time
      rw [quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff (reward a) m path hpath]
      funext who
      cases who <;> simp [xVal_zero a]
  | succ remaining ih =>
      have htime : time < m := by omega
      set index : Fin m := ⟨time, htime⟩ with hindex
      have hcurrent := ih (time + 1) (by omega)
      have hedge : IsQuittingNashBellmanEdge (reward a)
          (path (Fin.castSucc index)) (path (Fin.succ index)) := hpath.2.2 index
      have hcv : quittingFiniteNashBellmanPathValue m path time =
          (path (Fin.castSucc index)).1 := by
        simp [quittingFiniteNashBellmanPathValue, index, Nat.lt_succ_of_lt htime]
      have hcr : quittingFiniteNashBellmanPathRoots m path time =
          quittingRootOfSimplex (path (Fin.castSucc index)).2 := by
        simp [quittingFiniteNashBellmanPathRoots, index, htime]
      have hsv : quittingFiniteNashBellmanPathValue m path (time + 1) =
          (path (Fin.succ index)).1 := by
        simp [quittingFiniteNashBellmanPathValue, index, Nat.succ_lt_succ htime]
      have hsuccessor : (path (Fin.succ index)).1 =
          (fun who => if who then (0 : ℝ) else xVal a remaining) := by
        rw [← hsv]; exact hcurrent.1
      have hnash : IsεQuittingRootEndpointNash (reward a)
          (fun who => if who then (0 : ℝ) else xVal a remaining) 0
          (quittingRootOfSimplex (path (Fin.castSucc index)).2) := by
        rw [← hsuccessor]; exact hedge.2
      have hforced := root_forced_of_endpointNash a (xVal a remaining)
        (xVal_nonneg a ha0 ha1 remaining) (xVal_lt_a a ha0 ha1 remaining) _ hnash
      have hrooteq : quittingRootOfSimplex (path (Fin.castSucc index)).2 =
          stepRoot a ha0 ha1 remaining := by
        funext who
        cases who
        · exact pmf_bool_eq_coin_of_apply_true_toReal_eq _ _ (by norm_num) (by norm_num)
            hforced.1
        · exact pmf_bool_eq_coin_of_apply_true_toReal_eq _ (p2Val a remaining)
            (p2Val_nonneg a ha0 ha1 remaining) (p2Val_le_one a ha0 ha1 remaining) hforced.2
      refine ⟨?_, fun _ => by rw [hcr, hrooteq]; simp⟩
      rw [hcv]
      have hval := hedge.1
      rw [hsuccessor, hrooteq] at hval
      rw [hval]
      exact stepRoot_successor_eq a ha0 ha1 remaining

/-- Every admissible zero-boundary exact Nash--Bellman chain at cutoff `m`
has the forced initial value. -/
theorem chainPath_forced_initialValue (m : ℕ)
    (path : QuittingFiniteNashBellmanPath Bool m)
    (hpath : path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet (reward a) m) :
    quittingFiniteNashBellmanPathValue m path 0 =
      (fun who => if who then (0 : ℝ) else xVal a m) :=
  (chainPath_forced a ha0 ha1 m path hpath m 0 (by omega)).1

/-! ## Exact optimized dynamic debt -/

/-- The debt-recursion opponent-continue-mass factor, restated with the
successor value. -/
theorem one_sub_p2Val_eq (k : ℕ) : 1 - p2Val a k = xVal a (k + 1) / a := by
  rw [eq_div_iff ha0.ne']
  rw [← xVal_succ_eq a ha0 ha1 k]
  ring

/-- Player two's simplex continue coordinate at reverse distance `j + 1` is
the step-`j` continue mass `1 - p2Val a j`, for any augmented point whose
displayed Nash--Bellman state is the reverse-distance-`(j + 1)` chain
state. -/
theorem quittingDebtOpponentContinueMass_chainState_false
    (point : QuittingDebtPoint Bool) (j : ℕ)
    (hpoint : point.1 = chainState a ha0 ha1 (j + 1)) :
    quittingDebtOpponentContinueMass point false = 1 - p2Val a j := by
  unfold quittingDebtOpponentContinueMass
  have herase : (Finset.univ.erase false : Finset Bool) = {true} := by decide
  rw [herase, Finset.prod_singleton, hpoint]
  change (chainState a ha0 ha1 (j + 1)).2 true false = 1 - p2Val a j
  unfold chainState
  simp only [Nat.add_sub_cancel]
  show (stepSimplexRoot a ha0 ha1 j) true false = 1 - p2Val a j
  rw [← quittingRootOfSimplex_apply_toReal (stepSimplexRoot a ha0 ha1 j) true false,
    quittingRootOfSimplex_stepSimplexRoot]
  simp [stepRoot]

/-- **Exact optimized debt on the forced chain.**  Player one's dynamic
debt at reverse distance `k` from the cutoff is exactly the closed form
`d_k`. -/
theorem chainPath_debtPoint_false (m : ℕ) :
    ∀ k, k ≤ m →
      (quittingFiniteNashBellmanPathDynamicDebtPoint (reward a) m
          (chainPath a ha0 ha1 m) (m - k)).2 false = dVal a k := by
  intro k
  induction k with
  | zero =>
      intro _
      unfold quittingFiniteNashBellmanPathDynamicDebtPoint
      simp only [Nat.sub_zero, dif_pos le_rfl]
      show quittingFiniteNashBellmanPathDynamicDebt (reward a) m
        (chainPath a ha0 ha1 m) false m = dVal a 0
      unfold quittingFiniteNashBellmanPathDynamicDebt
      rw [Nat.sub_self, quittingFiniteDynamicDebt_zero, positiveSingletonDebtCap_false a ha0]
      show a = dVal a 0
      unfold dVal
      have hne : (1 : ℝ) - a ≠ 0 := by linarith
      rw [pow_one]
      field_simp
  | succ k ih =>
      intro hk
      have hklem : k ≤ m := by omega
      have hik := ih hklem
      have htime : m - (k + 1) < m := by omega
      have hedge := quittingFiniteNashBellmanPathDynamicDebtPoint_edge (reward a) m
        (chainPath a ha0 ha1 m) (chainPath_mem a ha0 ha1 m) (m - (k + 1)) htime
      have hnext : m - (k + 1) + 1 = m - k := by omega
      rw [hnext] at hedge
      set current := quittingFiniteNashBellmanPathDynamicDebtPoint (reward a) m
        (chainPath a ha0 ha1 m) (m - (k + 1)) with hcurrent_def
      set successor := quittingFiniteNashBellmanPathDynamicDebtPoint (reward a) m
        (chainPath a ha0 ha1 m) (m - k) with hsuccessor_def
      have hcurrent1 : current.1 = chainState a ha0 ha1 (k + 1) := by
        rw [hcurrent_def]
        unfold quittingFiniteNashBellmanPathDynamicDebtPoint
        rw [dif_pos (by omega : m - (k + 1) ≤ m)]
        change chainPath a ha0 ha1 m ⟨m - (k + 1), Nat.lt_succ_of_le (by omega)⟩ =
          chainState a ha0 ha1 (k + 1)
        change chainState a ha0 ha1 (m - (m - (k + 1))) = chainState a ha0 ha1 (k + 1)
        congr 1
        omega
      have hsuccessor1 : successor.1 = chainState a ha0 ha1 k := by
        rw [hsuccessor_def]
        unfold quittingFiniteNashBellmanPathDynamicDebtPoint
        rw [dif_pos (by omega : m - k ≤ m)]
        change chainPath a ha0 ha1 m ⟨m - k, Nat.lt_succ_of_le (by omega)⟩ =
          chainState a ha0 ha1 k
        change chainState a ha0 ha1 (m - (m - k)) = chainState a ha0 ha1 k
        congr 1
        omega
      have hsuccessorMass : quittingDebtOpponentContinueMass current false = 1 - p2Val a k :=
        quittingDebtOpponentContinueMass_chainState_false a ha0 ha1 current k hcurrent1
      have hmass := hedge.2 false
      change current.2 false = quittingDynamicDebtUpdate (reward a) current successor false
        at hmass
      unfold quittingDynamicDebtUpdate at hmass
      rw [hcurrent1, hsuccessor1, hsuccessorMass, hik] at hmass
      simp only [chainState, Nat.add_sub_cancel] at hmass
      rw [quittingRootOfSimplex_stepSimplexRoot,
        stepRoot_false_quitPayoff_eq, stepRoot_false_continuePayoff_eq] at hmass
      have hxnn : 0 ≤ xVal a (k + 1) := xVal_nonneg a ha0 ha1 (k + 1)
      have hdnn : 0 ≤ dVal a k := by
        have hden := one_sub_pow_pos a ha0 ha1 k
        unfold dVal
        positivity
      have hprodnn : 0 ≤ xVal a (k + 1) / a * dVal a k := by positivity
      simp only [Bool.false_eq_true, if_false] at hmass
      rw [one_sub_p2Val_eq a ha0 ha1 k] at hmass
      rw [max_eq_right (by linarith : xVal a (k + 1) ≤
        xVal a (k + 1) + xVal a (k + 1) / a * dVal a k)] at hmass
      rw [hmass,
        show xVal a (k + 1) + xVal a (k + 1) / a * dVal a k - xVal a (k + 1) =
          dVal a k * (xVal a (k + 1) / a) by ring,
        ← dVal_succ_eq a ha0 ha1 k]

/-- The forced chain's player-one dynamic debt at cutoff `m` is exactly the
closed form `d_m`. -/
theorem chainPath_dynamicDebt_false_eq (m : ℕ) :
    quittingFiniteNashBellmanPathDynamicDebt (reward a) m (chainPath a ha0 ha1 m) false 0 =
      dVal a m := by
  have h := chainPath_debtPoint_false a ha0 ha1 m m le_rfl
  simp only [Nat.sub_self] at h
  unfold quittingFiniteNashBellmanPathDynamicDebtPoint at h
  rw [dif_pos (Nat.zero_le m)] at h
  exact h

/-! ## The forced value and root sequences are shared by every admissible chain -/

/-- Every admissible chain at cutoff `m` has the same displayed value
sequence as the forced chain. -/
theorem quittingFiniteNashBellmanPathValue_eq_chainPath (m : ℕ)
    (path : QuittingFiniteNashBellmanPath Bool m)
    (hpath : path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet (reward a) m) :
    quittingFiniteNashBellmanPathValue m path =
      quittingFiniteNashBellmanPathValue m (chainPath a ha0 ha1 m) := by
  funext time
  by_cases htime : time ≤ m
  · rw [(chainPath_forced a ha0 ha1 m path hpath (m - time) time (by omega)).1,
      (chainPath_forced a ha0 ha1 m (chainPath a ha0 ha1 m) (chainPath_mem a ha0 ha1 m)
        (m - time) time (by omega)).1]
  · have h1 : ¬ time < m + 1 := by omega
    simp [quittingFiniteNashBellmanPathValue, h1]

/-- Every admissible chain at cutoff `m` has the same operational root
sequence as the forced chain. -/
theorem quittingFiniteNashBellmanPathRoots_eq_chainPath (m : ℕ)
    (path : QuittingFiniteNashBellmanPath Bool m)
    (hpath : path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet (reward a) m) :
    quittingFiniteNashBellmanPathRoots m path =
      quittingFiniteNashBellmanPathRoots m (chainPath a ha0 ha1 m) := by
  funext time
  by_cases htime : time < m
  · have hpos : 0 < m - time := by omega
    rw [(chainPath_forced a ha0 ha1 m path hpath (m - time) time (by omega)).2 hpos,
      (chainPath_forced a ha0 ha1 m (chainPath a ha0 ha1 m) (chainPath_mem a ha0 ha1 m)
        (m - time) time (by omega)).2 hpos]
  · simp [quittingFiniteNashBellmanPathRoots, htime]

/-- Consequently every admissible chain's exact dynamic debt agrees with the
forced chain's, at every player and every displayed time. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_eq_chainPath (m : ℕ)
    (path : QuittingFiniteNashBellmanPath Bool m)
    (hpath : path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet (reward a) m)
    (who : Bool) (time : ℕ) :
    quittingFiniteNashBellmanPathDynamicDebt (reward a) m path who time =
      quittingFiniteNashBellmanPathDynamicDebt (reward a) m
        (chainPath a ha0 ha1 m) who time := by
  unfold quittingFiniteNashBellmanPathDynamicDebt
  rw [quittingFiniteNashBellmanPathRoots_eq_chainPath a ha0 ha1 m path hpath,
    quittingFiniteNashBellmanPathValue_eq_chainPath a ha0 ha1 m path hpath]

/-- **Every admissible chain's player-one exact dynamic debt is exactly
`d_m`.**  Not merely a witnessed upper bound: the singleton chain set forces
the same value on every admissible chain. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_false_eq (m : ℕ)
    (path : QuittingFiniteNashBellmanPath Bool m)
    (hpath : path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet (reward a) m) :
    quittingFiniteNashBellmanPathDynamicDebt (reward a) m path false 0 = dVal a m := by
  rw [quittingFiniteNashBellmanPathDynamicDebt_eq_chainPath a ha0 ha1 m path hpath]
  exact chainPath_dynamicDebt_false_eq a ha0 ha1 m

/-- Every admissible chain's playerwise maximum exact dynamic debt is
`d_m`. -/
theorem quittingFiniteNashBellmanPathMaxDynamicDebt_eq (m : ℕ)
    (path : QuittingFiniteNashBellmanPath Bool m)
    (hpath : path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet (reward a) m) :
    quittingFiniteNashBellmanPathMaxDynamicDebt (reward a) m path = dVal a m := by
  have hfalse := quittingFiniteNashBellmanPathDynamicDebt_false_eq a ha0 ha1 m path hpath
  have htrue := quittingFiniteNashBellmanPathDynamicDebt_true_eq_zero a m path hpath
  have hdnn : 0 ≤ dVal a m := by
    have hden := one_sub_pow_pos a ha0 ha1 m
    unfold dVal
    positivity
  unfold quittingFiniteNashBellmanPathMaxDynamicDebt
  apply le_antisymm
  · apply Finset.sup'_le
    intro who _
    cases who
    · rw [hfalse]
    · rw [htrue]; exact hdnn
  · rw [← hfalse]
    exact Finset.le_sup'
      (fun who => quittingFiniteNashBellmanPathDynamicDebt (reward a) m path who 0)
      (Finset.mem_univ false)

/-- **The optimized (min-max) exact dynamic debt at cutoff `m` is exactly
`d_m`.**  Since the chain set is a singleton up to the shared forced value
and root sequences, every admissible chain, in particular the attained
minimizer, has playerwise maximum debt `d_m`. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_eq (m : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt (reward a) m = dVal a m := by
  unfold quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
  exact quittingFiniteNashBellmanPathMaxDynamicDebt_eq a ha0 ha1 m _
    (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem (reward a) m)

/-! ## The positive plateau and the vanishing drop -/

/-- **The positive plateau.**  Optimized exact dynamic debt never falls below
the strictly positive limit `a(1 - a)`. -/
theorem dVal_ge (m : ℕ) : a * (1 - a) ≤ dVal a m := by
  unfold dVal
  have hden := one_sub_pow_pos a ha0 ha1 m
  rw [le_div_iff₀ hden]
  have hnn : 0 ≤ a * (1 - a) * a ^ (m + 1) := by positivity
  nlinarith [hnn]

/-- The optimized debt sequence tends to the strictly positive plateau
`a(1 - a)`. -/
theorem tendsto_dVal :
    Filter.Tendsto (dVal a) Filter.atTop (nhds (a * (1 - a))) := by
  have hpow : Filter.Tendsto (fun k : ℕ => a ^ (k + 1)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).comp (Filter.tendsto_add_atTop_nat 1)
  have hden : Filter.Tendsto (fun k : ℕ => 1 - a ^ (k + 1)) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hpow
  have hdiv : Filter.Tendsto (fun k : ℕ => a * (1 - a) / (1 - a ^ (k + 1))) Filter.atTop
      (nhds (a * (1 - a) / 1)) :=
    Filter.Tendsto.div tendsto_const_nhds hden (by norm_num)
  unfold dVal
  simpa using hdiv

/-- **The vanishing drop.**  For every fixed extra horizon length `L`, the
optimized debt drop `d_m - d_{m + L}` tends to zero as `m → ∞`.  This is the
precise sense in which no bounded-length extension of the zero-pinned chain
family can decrement the optimized debt by a cutoff-independent amount. -/
theorem tendsto_dVal_sub_dVal_add (L : ℕ) :
    Filter.Tendsto (fun m : ℕ => dVal a m - dVal a (m + L)) Filter.atTop (nhds 0) := by
  have hshift : Filter.Tendsto (fun m : ℕ => dVal a (m + L)) Filter.atTop
      (nhds (a * (1 - a))) :=
    (tendsto_dVal a ha0 ha1).comp (Filter.tendsto_add_atTop_nat L)
  simpa using (tendsto_dVal a ha0 ha1).sub hshift

end

/-! ## The plateau is an artifact of pinning the continuation to zero -/

/-- The stationary root at which player one mixes half--half and player two
never quits. -/
def stationaryRoot (_a : ℝ) : Bool → PMF Bool :=
  fun who => if who then PMF.pure false else coin (1 / 2) (by norm_num) (by norm_num)

@[simp] theorem stationaryRoot_false_true (a : ℝ) :
    (stationaryRoot a false true).toReal = 1 / 2 := by simp [stationaryRoot]

@[simp] theorem stationaryRoot_false_false (a : ℝ) :
    (stationaryRoot a false false).toReal = 1 / 2 := by norm_num [stationaryRoot]

@[simp] theorem stationaryRoot_true_true (a : ℝ) :
    (stationaryRoot a true true).toReal = 0 := by simp [stationaryRoot]

/-- The stationary root, run against the constant continuation `(a, 0)`,
reproduces exactly that continuation: it is a genuine stationary root, not
merely an approximate one. -/
theorem stationaryRoot_successor_eq (a : ℝ) :
    quittingRootSuccessorPayoff (reward a)
        (fun who => if who then (0 : ℝ) else a) (stationaryRoot a) =
      (fun who => if who then (0 : ℝ) else a) := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  cases who
  · rw [false_quitPayoff, false_continuePayoff, stationaryRoot_true_true,
      stationaryRoot_false_true, stationaryRoot_false_false]
    simp only [Bool.false_eq_true, if_false]
    ring
  · rw [true_quitPayoff, true_continuePayoff, stationaryRoot_false_true]
    norm_num

/-- The stationary root is exact endpoint Nash against the constant
continuation `(a, 0)`: both players are exactly indifferent, not merely
approximately so. -/
theorem stationaryRoot_isEndpointNash (a : ℝ) :
    IsεQuittingRootEndpointNash (reward a)
        (fun who => if who then (0 : ℝ) else a) 0 (stationaryRoot a) := by
  intro who
  cases who
  · rw [false_endpointDifference, stationaryRoot_true_true]
    norm_num
  · rw [true_endpointDifference, stationaryRoot_false_true]
    norm_num

/-- **The plateau is manufactured by the zero pin, not by the game.**  Run
the exact same dynamic-debt Bellman recursion used above, but against the
game's own stationary continuation `(a, 0)` instead of the zero-boundary
pin, and with the honest terminal debt `0` instead of the positive
singleton cap: the debt is exactly zero at every horizon.  Contrast
`chainPath_dynamicDebt_false_eq`, whose zero-pinned debt is the strictly
positive `d_m`. -/
theorem quittingConstantDynamicDebt_eq_zero (a : ℝ) :
    ∀ fuel start : ℕ,
      quittingFiniteDynamicDebt (reward a) (fun _ => stationaryRoot a) false
        (fun _ => a) 0 start fuel = 0 := by
  intro fuel
  induction fuel with
  | zero => intro start; rfl
  | succ fuel ih =>
      intro start
      rw [quittingFiniteDynamicDebt_succ_eq_endpoints]
      rw [ih (start + 1)]
      rw [false_quitPayoff, false_continuePayoff, stationaryRoot_true_true]
      norm_num

/-! ## Concrete verification at `a = 1 / 2` and small cutoffs -/

/-- The closed-form optimized debt at `a = 1/2` and cutoff `0` is `1/2`. -/
theorem dVal_half_zero : dVal (1 / 2) 0 = 1 / 2 := by unfold dVal; norm_num

/-- The closed-form optimized debt at `a = 1/2` and cutoff `1` is `1/3`. -/
theorem dVal_half_one : dVal (1 / 2) 1 = 1 / 3 := by unfold dVal; norm_num

/-- The closed-form optimized debt at `a = 1/2` and cutoff `2` is `2/7`. -/
theorem dVal_half_two : dVal (1 / 2) 2 = 2 / 7 := by unfold dVal; norm_num

/-- The closed-form optimized debt at `a = 1/2` and cutoff `3` is `4/15`. -/
theorem dVal_half_three : dVal (1 / 2) 3 = 4 / 15 := by unfold dVal; norm_num

/-- At `a = 1/2`, the optimized debts strictly decrease through the first
four cutoffs: `1/2 > 1/3 > 2/7 > 4/15`, all strictly above the plateau
`a(1 - a) = 1/4`. -/
theorem dVal_half_strictAnti_and_above_plateau :
    dVal (1 / 2) 0 > dVal (1 / 2) 1 ∧ dVal (1 / 2) 1 > dVal (1 / 2) 2 ∧
      dVal (1 / 2) 2 > dVal (1 / 2) 3 ∧
      (1 / 2 : ℝ) * (1 - 1 / 2) < dVal (1 / 2) 3 := by
  rw [dVal_half_zero, dVal_half_one, dVal_half_two, dVal_half_three]
  norm_num

/-- The optimized (min-max) exact dynamic debt at `a = 1/2` and cutoff `m`
equals the closed form `d_m`, for every cutoff, not merely a witness. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_half_eq (m : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt (reward (1 / 2)) m =
      dVal (1 / 2) m :=
  quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_eq (1 / 2) (by norm_num) (by norm_num) m

/-- Concretely, at `a = 1/2` the optimized debt at cutoffs `0, 1, 2, 3` is
exactly `1/2, 1/3, 2/7, 4/15`. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_half_zero :
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt (reward (1 / 2)) 0 = 1 / 2 := by
  rw [quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_half_eq, dVal_half_zero]

/-- The optimized debt at `a = 1/2` and cutoff `1` is exactly `1/3`. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_half_one :
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt (reward (1 / 2)) 1 = 1 / 3 := by
  rw [quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_half_eq, dVal_half_one]

/-- The optimized debt at `a = 1/2` and cutoff `2` is exactly `2/7`. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_half_two :
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt (reward (1 / 2)) 2 = 2 / 7 := by
  rw [quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_half_eq, dVal_half_two]

/-- The optimized debt at `a = 1/2` and cutoff `3` is exactly `4/15`. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_half_three :
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt (reward (1 / 2)) 3 = 4 / 15 := by
  rw [quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_half_eq, dVal_half_three]

end QuittingBoundedSurgeryDescentCounterexample

end GameTheory
