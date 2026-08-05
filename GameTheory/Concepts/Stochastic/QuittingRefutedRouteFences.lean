/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Convex.Topology
import GameTheory.Concepts.Stochastic.QuittingRootSuccessorCertificate
import GameTheory.Concepts.Stochastic.QuittingBoundedSurgeryDescentCounterexample

/-!
# Two permanent fences against previously prose-only refuted routes

Two research routes toward the finite-quitting conjecture
(`QuittingConjecture.lean`) carried a "do not reuse" instruction backed only
by a prose witness.  This file turns both witnesses into machine-checked
fences, mirroring the explicit two-coordinate (`ι = Bool`) table idiom of
`QuittingBoundedSurgeryDescentCounterexample.lean`.

## Fence 1: the successor correspondence is not convex-valued

For the table `r({1}) = (-1, 0)`, `r({2}) = (0, -1)`, `r({1,2}) = (1, 1)` and
the continuation `z = (0, 0)`, the set of successor payoffs reachable by a
complementary root — `successorImage` — contains both `(0,0)` and `(1,1)`
but not their midpoint `(1/2, 1/2)`.  Hence `successorImage` is not convex,
which refutes any one-row Kakutani-style argument for the completeness gap
in `QuittingConjecture.lean` (a route that presupposes a convex-valued
correspondence).

## Fence 2: the blocking-digraph closure system can be unsolvable

For the table `r({1}) = (1, 0)`, `r({2}) = (0, 1)`, `r({1,2}) = (1, 1)`, each
coordinate *blocks* the other (`Blocks`), so the blocking digraph is a
directed 2-cycle and the "follow a directed cycle of blockers" construction
has exactly one candidate: the two-phase alternation formalized below.
Propagating the exact Nash--Bellman value recursion once around that cycle
forces both quitting rates to zero, so no admissible closure with both rates
positive exists.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace QuittingRefutedRouteFences

/-! We use `false` for player one and `true` for player two, as in the
mirrored idiom. -/

/-! ## Fence 1: the successor correspondence is not convex-valued -/

namespace SuccessorCorrespondenceNotConvex

/-- Payoffs `r({1}) = (-1, 0)`, `r({2}) = (0, -1)`, and `r({1,2}) = (1, 1)`. -/
def reward1 (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if false ∈ quitters.1 then
      if true ∈ quitters.1 then 1
      else (if who then 0 else -1)
    else (if who then -1 else 0)

/-- The fixed continuation vector `z = (0, 0)`. -/
def zero2 : Payoff Bool := fun _ => 0

/-- The all-quit target vector `(1, 1)`. -/
def one2 : Payoff Bool := fun _ => 1

/-- Player one's pure-Quit endpoint against `z = (0,0)` depends only on
player two's marginal. -/
theorem quitPayoff_false (root : Bool → PMF Bool) :
    quittingRootQuitPayoff reward1 zero2 root false =
      2 * (root true true).toReal - 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  have hc : (root true false).toReal = 1 - (root true true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward1, hc]
  ring

/-- Player one's pure-Continue endpoint against `z = (0,0)` is zero. -/
theorem continuePayoff_false (root : Bool → PMF Bool) :
    quittingRootContinuePayoff reward1 zero2 root false = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward1, zero2]

/-- Player two's pure-Quit endpoint against `z = (0,0)` depends only on
player one's marginal. -/
theorem quitPayoff_true (root : Bool → PMF Bool) :
    quittingRootQuitPayoff reward1 zero2 root true =
      2 * (root false true).toReal - 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hc : (root false false).toReal = 1 - (root false true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward1, hc]
  ring

/-- Player two's pure-Continue endpoint against `z = (0,0)` is zero. -/
theorem continuePayoff_true (root : Bool → PMF Bool) :
    quittingRootContinuePayoff reward1 zero2 root true = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward1, zero2]

/-- The gap for player one, derived from the repository's Quit/Continue
endpoint definitions. -/
theorem endpointDifference_false (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward1 zero2 root false =
      2 * (root true true).toReal - 1 := by
  rw [quittingRootEndpointDifference, quitPayoff_false, continuePayoff_false]
  ring

/-- The gap for player two, derived from the repository's Quit/Continue
endpoint definitions. -/
theorem endpointDifference_true (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward1 zero2 root true =
      2 * (root false true).toReal - 1 := by
  rw [quittingRootEndpointDifference, quitPayoff_true, continuePayoff_true]
  ring

/-- Player one's successor payoff `F_1(y)`, derived from the endpoint
Bernoulli mixture. -/
theorem successorPayoff_false (root : Bool → PMF Bool) :
    quittingRootSuccessorPayoff reward1 zero2 root false =
      (root false true).toReal * (2 * (root true true).toReal - 1) := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quitPayoff_false, continuePayoff_false]
  ring

/-- Player two's successor payoff `F_2(y)`, derived from the endpoint
Bernoulli mixture. -/
theorem successorPayoff_true (root : Bool → PMF Bool) :
    quittingRootSuccessorPayoff reward1 zero2 root true =
      (root true true).toReal * (2 * (root false true).toReal - 1) := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quitPayoff_true, continuePayoff_true]
  ring

/-! ## The deviation-correspondence image at `z = (0,0)` -/

/-- `Φ(z)` for `z = zero2`: the set of successor payoffs `F_y(z)` reachable
by a row `y` that is complementary against `z` — exactly
`IsεQuittingRootEndpointNash reward1 zero2 0 root`, since for a root built
from a row `y` (`(root i true).toReal = y i`), that predicate unfolds to
`y i > 0 → gap i ≥ 0` and `y i < 1 → gap i ≤ 0`. -/
def successorImage : Set (Payoff Bool) :=
  { v | ∃ root : Bool → PMF Bool,
      IsεQuittingRootEndpointNash reward1 zero2 0 root ∧
        quittingRootSuccessorPayoff reward1 zero2 root = v }

/-- The all-continue row `y = (0,0)` is complementary and maps to `(0,0)`. -/
theorem zero2_mem_successorImage : zero2 ∈ successorImage := by
  refine ⟨quittingAllContinueRoot, fun who => ?_, ?_⟩
  · have h0 : (quittingAllContinueRoot who false).toReal = 1 := by
      simp [quittingAllContinueRoot]
    have h1 : (quittingAllContinueRoot who true).toReal = 0 := by
      simp [quittingAllContinueRoot]
    have hdiff : quittingRootEndpointDifference reward1 zero2 quittingAllContinueRoot who = -1 := by
      cases who
      · rw [endpointDifference_false]; norm_num [quittingAllContinueRoot]
      · rw [endpointDifference_true]; norm_num [quittingAllContinueRoot]
    rw [h0, h1, hdiff]
    norm_num
  · funext who
    cases who <;>
      norm_num [successorPayoff_false, successorPayoff_true, quittingAllContinueRoot, zero2]

/-- The all-quit root: both coordinates quit for sure. -/
def allQuitRoot : Bool → PMF Bool := fun _ => PMF.pure true

/-- The all-quit row `y = (1,1)` is complementary and maps to `(1,1)`. -/
theorem one2_mem_successorImage : one2 ∈ successorImage := by
  refine ⟨allQuitRoot, fun who => ?_, ?_⟩
  · have h0 : (allQuitRoot who false).toReal = 0 := by simp [allQuitRoot]
    have h1 : (allQuitRoot who true).toReal = 1 := by simp [allQuitRoot]
    have hdiff : quittingRootEndpointDifference reward1 zero2 allQuitRoot who = 1 := by
      cases who
      · rw [endpointDifference_false]; norm_num [allQuitRoot]
      · rw [endpointDifference_true]; norm_num [allQuitRoot]
    rw [h0, h1, hdiff]
    norm_num
  · funext who
    cases who <;>
      norm_num [successorPayoff_false, successorPayoff_true, allQuitRoot, one2]

/-- **No complementary row maps to the midpoint `(1/2,1/2)` of `(0,0)` and
`(1,1)`.**  This is the arithmetic core of the fence: `p₁ = (root false
true).toReal` and `p₂ = (root true true).toReal` satisfy `p₁(2p₂-1) = 1/2`
and `p₂(2p₁-1) = 1/2`; complementarity at `p₁ > 0` forces `p₁ = 1`, which
forces `p₂ = 1/2`, contradicting `2p₂ - 1 > 0` (itself forced by `p₁ > 0`
and the first equation). -/
theorem successorPayoff_ne_half
    (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootEndpointNash reward1 zero2 0 root) :
    quittingRootSuccessorPayoff reward1 zero2 root ≠ fun _ => (1 / 2 : ℝ) := by
  intro heq
  have hfalse : (root false true).toReal * (2 * (root true true).toReal - 1) = 1 / 2 := by
    have h := congrFun heq false
    rwa [successorPayoff_false] at h
  have htrue : (root true true).toReal * (2 * (root false true).toReal - 1) = 1 / 2 := by
    have h := congrFun heq true
    rwa [successorPayoff_true] at h
  set p1 := (root false true).toReal with hp1_def
  set p2 := (root true true).toReal with hp2_def
  have hp1_nonneg : 0 ≤ p1 := ENNReal.toReal_nonneg
  have hp2_nonneg : 0 ≤ p2 := ENNReal.toReal_nonneg
  have hp1_le1 : p1 ≤ 1 := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root false
    rw [← hp1_def] at hsum
    nlinarith [ENNReal.toReal_nonneg (a := root false false)]
  have hp1_pos : 0 < p1 := by
    rcases eq_or_lt_of_le hp1_nonneg with h | h
    · exfalso; rw [← h] at hfalse; norm_num at hfalse
    · exact h
  have h2p2_pos : 0 < 2 * p2 - 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg hp1_pos.le (neg_nonneg.mpr hcon), hfalse]
  have hnash_false := hnash false
  rw [endpointDifference_false] at hnash_false
  have hcontinue_false : (root false false).toReal = 1 - p1 := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root false
    rw [← hp1_def] at hsum
    linarith
  rw [hcontinue_false, ← hp2_def] at hnash_false
  have hp1_ge1 : 1 ≤ p1 := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < (1 - p1) * (2 * p2 - 1) := mul_pos (by linarith) h2p2_pos
    linarith [hnash_false.1]
  have hp1_eq1 : p1 = 1 := le_antisymm hp1_le1 hp1_ge1
  rw [hp1_eq1] at htrue
  have hp2_eq : p2 = 1 / 2 := by nlinarith [htrue]
  rw [hp2_eq] at h2p2_pos
  norm_num at h2p2_pos

/-- The midpoint of `(0,0)` and `(1,1)` in `Payoff Bool` is the constant
function `1/2`. -/
theorem midpoint_zero2_one2 : midpoint ℝ zero2 one2 = fun _ => (1 / 2 : ℝ) := by
  funext who
  cases who <;> norm_num [zero2, one2, midpoint, AffineMap.lineMap_apply_module]

/-- **HEADLINE** — refutes a one-row Kakutani-style argument for the
completeness gap in `QuittingConjecture.lean`: the deviation-correspondence
image `Φ(z)` at `z = (0,0)` is not convex-valued.  It contains `(0,0)` and
`(1,1)` but not their midpoint `(1/2,1/2)`, so no fixed-point argument that
presupposes a convex-valued successor correspondence can apply to this
table. -/
theorem successorImage_not_convex : ¬ Convex ℝ successorImage := by
  intro hconvex
  have hmidpoint := hconvex.midpoint_mem zero2_mem_successorImage one2_mem_successorImage
  rw [midpoint_zero2_one2] at hmidpoint
  obtain ⟨root, hnash, heq⟩ := hmidpoint
  exact successorPayoff_ne_half root hnash heq

end SuccessorCorrespondenceNotConvex

/-! ## Fence 2: the blocking-digraph closure system can be unsolvable -/

namespace BlockingDigraphUnsolvable

/-- Payoffs `r({1}) = (1, 0)`, `r({2}) = (0, 1)`, and `r({1,2}) = (1, 1)`. -/
def reward2 (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if false ∈ quitters.1 then
      if true ∈ quitters.1 then 1
      else (if who then 0 else 1)
    else (if who then 1 else 0)

/-! ### Part (a): the blocking digraph is a directed 2-cycle -/

/-- Coordinate `j` **blocks** coordinate `i`: no quitting rate `p ∈ (0,1]`
lets `j`'s payoff from switching to sure Quit, against `i`'s rate-`p` hazard,
be at most `j`'s payoff from `i` quitting alone. -/
def Blocks (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (j i : Bool) : Prop :=
  ¬ ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
    (1 - p) * reward (quittingSingletonTerminal j) j +
        p * reward ⟨insert i {j}, Finset.insert_nonempty i {j}⟩ j ≤
      reward (quittingSingletonTerminal i) j

/-- Coordinate `true` blocks coordinate `false`: the comparison collapses to
the constant `1 ≤ 0`, which is false for every `p`. -/
theorem blocks_true_false : Blocks reward2 true false := by
  rintro ⟨p, -, -, hle⟩
  have h1 : reward2 (quittingSingletonTerminal true) true = 1 := by
    simp [reward2, quittingSingletonTerminal]
  have h2 : reward2 (⟨insert false {true}, Finset.insert_nonempty false {true}⟩ :
      {S : Finset Bool // S.Nonempty}) true = 1 := by
    simp [reward2]
  have h3 : reward2 (quittingSingletonTerminal false) true = 0 := by
    simp [reward2, quittingSingletonTerminal]
  rw [h1, h2, h3] at hle
  linarith

/-- Coordinate `false` blocks coordinate `true`: the comparison collapses to
the constant `1 ≤ 0`, which is false for every `p`. -/
theorem blocks_false_true : Blocks reward2 false true := by
  rintro ⟨p, -, -, hle⟩
  have h1 : reward2 (quittingSingletonTerminal false) false = 1 := by
    simp [reward2, quittingSingletonTerminal]
  have h2 : reward2 (⟨insert true {false}, Finset.insert_nonempty true {false}⟩ :
      {S : Finset Bool // S.Nonempty}) false = 1 := by
    simp [reward2]
  have h3 : reward2 (quittingSingletonTerminal true) false = 0 := by
    simp [reward2, quittingSingletonTerminal]
  rw [h1, h2, h3] at hle
  linarith

/-- **HEADLINE** — refutes the "follow a directed cycle of blockers"
construction's freedom of choice: with only two coordinates, each blocks the
other, so the blocking digraph is a directed 2-cycle and the two-phase
alternation of Part (b) is the *only* candidate construction it admits. -/
theorem blockingDigraph_isTwoCycle :
    Blocks reward2 true false ∧ Blocks reward2 false true :=
  ⟨blocks_true_false, blocks_false_true⟩

/-! ### Part (b): the two-phase closure system is unsolvable -/

/-- Player one's pure-Quit endpoint is the constant `1`: it does not depend
on the opponent's marginal, since the solo and full-quit rewards coincide
on this table. -/
theorem quitPayoff_false (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff reward2 tail root false = 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  have hc : (root true false).toReal = 1 - (root true true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward2, hc]

/-- Player one's pure-Continue endpoint. -/
theorem continuePayoff_false (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootContinuePayoff reward2 tail root false =
      (1 - (root true true).toReal) * tail false := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  have hc : (root true false).toReal = 1 - (root true true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward2, hc]

/-- Player two's pure-Quit endpoint is the constant `1`. -/
theorem quitPayoff_true (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff reward2 tail root true = 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hc : (root false false).toReal = 1 - (root false true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward2, hc]

/-- Player two's pure-Continue endpoint. -/
theorem continuePayoff_true (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootContinuePayoff reward2 tail root true =
      (1 - (root false true).toReal) * tail true := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hc : (root false false).toReal = 1 - (root false true).toReal := by linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward2, hc]

/-- Player one's gap, derived from the repository's Quit/Continue endpoint
definitions. -/
theorem endpointDifference_false (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward2 tail root false =
      1 - (1 - (root true true).toReal) * tail false := by
  rw [quittingRootEndpointDifference, quitPayoff_false, continuePayoff_false]

/-- Player two's gap, derived from the repository's Quit/Continue endpoint
definitions. -/
theorem endpointDifference_true (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward2 tail root true =
      1 - (1 - (root false true).toReal) * tail true := by
  rw [quittingRootEndpointDifference, quitPayoff_true, continuePayoff_true]

/-- Player one's successor payoff, from the endpoint Bernoulli mixture. -/
theorem successorPayoff_false (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootSuccessorPayoff reward2 tail root false =
      (root false true).toReal +
        (root false false).toReal * (1 - (root true true).toReal) * tail false := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quitPayoff_false, continuePayoff_false]
  ring

/-- Player two's successor payoff, from the endpoint Bernoulli mixture. -/
theorem successorPayoff_true (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootSuccessorPayoff reward2 tail root true =
      (root true true).toReal +
        (root true false).toReal * (1 - (root false true).toReal) * tail true := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quitPayoff_true, continuePayoff_true]
  ring

/-- The phase root: coordinate `active` quits at rate `p`, the other
coordinate is silent (never quits). -/
def phaseRoot (active : Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Bool → PMF Bool :=
  fun who =>
    if who = active then
      QuittingBoundedSurgeryDescentCounterexample.coin p hp0 hp1
    else PMF.pure false

@[simp] theorem phaseRoot_false_p_false_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (phaseRoot false p hp0 hp1 false true).toReal = p := by
  simp [phaseRoot, QuittingBoundedSurgeryDescentCounterexample.coin_true_toReal]

@[simp] theorem phaseRoot_false_p_false_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (phaseRoot false p hp0 hp1 false false).toReal = 1 - p := by
  simp [phaseRoot, QuittingBoundedSurgeryDescentCounterexample.coin_false_toReal]

@[simp] theorem phaseRoot_false_p_true_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (phaseRoot false p hp0 hp1 true true).toReal = 0 := by
  simp [phaseRoot]

@[simp] theorem phaseRoot_false_p_true_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (phaseRoot false p hp0 hp1 true false).toReal = 1 := by
  simp [phaseRoot]

@[simp] theorem phaseRoot_true_p_true_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (phaseRoot true p hp0 hp1 true true).toReal = p := by
  simp [phaseRoot, QuittingBoundedSurgeryDescentCounterexample.coin_true_toReal]

@[simp] theorem phaseRoot_true_p_true_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (phaseRoot true p hp0 hp1 true false).toReal = 1 - p := by
  simp [phaseRoot, QuittingBoundedSurgeryDescentCounterexample.coin_false_toReal]

@[simp] theorem phaseRoot_true_p_false_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (phaseRoot true p hp0 hp1 false true).toReal = 0 := by
  simp [phaseRoot]

@[simp] theorem phaseRoot_true_p_false_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (phaseRoot true p hp0 hp1 false false).toReal = 1 := by
  simp [phaseRoot]

set_option linter.unusedVariables false in
/-- **HEADLINE** — refutes the two-phase closure construction that the
directed 2-cycle of `blockingDigraph_isTwoCycle` forces: propagating the
exact Nash--Bellman value recursion once around the cycle (phase `false` at
rate `p1` against tail `V2`, phase `true` at rate `p2` against tail `V1`,
closing back to `V1`) drives both phase-`true` values to `1`, which forces
`p1 = 0`, and both phase-`false` values to `1`, which forces `p2 = 0`.  So no
closure with both rates positive exists.

`hp2_pos` is consumed by `nlinarith` when deriving `hineq2` below (needed to
turn `0 ≤ p2 * (1 - V1 true)` into `V1 true ≤ 1`); the unused-variable linter
does not see through that hint-list usage, so it is suppressed locally. -/
theorem quittingTwoPhaseClosure_rates_eq_zero
    (p1 p2 : ℝ) (hp1_0 : 0 ≤ p1) (hp1_1 : p1 ≤ 1) (hp2_0 : 0 ≤ p2) (hp2_1 : p2 ≤ 1)
    (hp1_pos : 0 < p1) (hp2_pos : 0 < p2)
    (V1 V2 : Payoff Bool)
    (hvalue1 : V1 = quittingRootSuccessorPayoff reward2 V2 (phaseRoot false p1 hp1_0 hp1_1))
    (hnash1 : IsεQuittingRootEndpointNash reward2 V2 0 (phaseRoot false p1 hp1_0 hp1_1))
    (hvalue2 : V2 = quittingRootSuccessorPayoff reward2 V1 (phaseRoot true p2 hp2_0 hp2_1))
    (hnash2 : IsεQuittingRootEndpointNash reward2 V1 0 (phaseRoot true p2 hp2_0 hp2_1)) :
    p1 = 0 ∧ p2 = 0 := by
  -- The `true`-coordinate value-recursion equations around the cycle.
  have hval1_true : V1 true = (1 - p1) * V2 true := by
    have h := congrFun hvalue1 true
    rw [successorPayoff_true] at h
    simp only [phaseRoot_false_p_true_true, phaseRoot_false_p_true_false,
      phaseRoot_false_p_false_true] at h
    linarith
  have hval2_true : V2 true = p2 + (1 - p2) * V1 true := by
    have h := congrFun hvalue2 true
    rw [successorPayoff_true] at h
    simp only [phaseRoot_true_p_true_true, phaseRoot_true_p_true_false,
      phaseRoot_true_p_false_true] at h
    linarith
  -- Complementarity forces the phase-`true` values to `1`.
  have hineq1 : 1 ≤ (1 - p1) * V2 true := by
    have h := (hnash1 true).1
    rw [phaseRoot_false_p_true_false, endpointDifference_true,
      phaseRoot_false_p_false_true] at h
    linarith
  have hineq2 : V1 true ≤ 1 := by
    have h := (hnash2 true).2
    rw [phaseRoot_true_p_true_true, endpointDifference_true,
      phaseRoot_true_p_false_true] at h
    nlinarith [hp2_pos]
  have hV1true : V1 true = 1 := by
    have hge : 1 ≤ V1 true := by rw [hval1_true]; exact hineq1
    linarith
  have hV2true : V2 true = 1 := by rw [hval2_true, hV1true]; ring
  have hp1zero : p1 = 0 := by
    have h := hval1_true
    rw [hV1true, hV2true] at h
    linarith
  -- The symmetric `false`-coordinate value-recursion equations around the
  -- cycle.
  have hval2_false : V2 false = (1 - p2) * V1 false := by
    have h := congrFun hvalue2 false
    rw [successorPayoff_false] at h
    simp only [phaseRoot_true_p_false_true, phaseRoot_true_p_false_false,
      phaseRoot_true_p_true_true] at h
    linarith
  have hval1_false : V1 false = p1 + (1 - p1) * V2 false := by
    have h := congrFun hvalue1 false
    rw [successorPayoff_false] at h
    simp only [phaseRoot_false_p_false_true, phaseRoot_false_p_false_false,
      phaseRoot_false_p_true_true] at h
    linarith
  have hineq1' : 1 ≤ (1 - p2) * V1 false := by
    have h := (hnash2 false).1
    rw [phaseRoot_true_p_false_false, endpointDifference_false,
      phaseRoot_true_p_true_true] at h
    linarith
  have hineq2' : V2 false ≤ 1 := by
    have h := (hnash1 false).2
    rw [phaseRoot_false_p_false_true, endpointDifference_false,
      phaseRoot_false_p_true_true] at h
    nlinarith [hp1_pos]
  have hV2false : V2 false = 1 := by
    have hge : 1 ≤ V2 false := by rw [hval2_false]; exact hineq1'
    linarith
  have hV1false : V1 false = 1 := by rw [hval1_false, hV2false]; ring
  have hp2zero : p2 = 0 := by
    have h := hval2_false
    rw [hV2false, hV1false] at h
    linarith
  exact ⟨hp1zero, hp2zero⟩

/-- **HEADLINE** — the "no solution with both rates positive" form of the
fence: a two-phase closure obeying the exact Nash--Bellman value recursion
around the directed 2-cycle cannot have both quitting rates strictly
positive. -/
theorem quittingTwoPhaseClosure_not_both_pos
    (p1 p2 : ℝ) (hp1_0 : 0 ≤ p1) (hp1_1 : p1 ≤ 1) (hp2_0 : 0 ≤ p2) (hp2_1 : p2 ≤ 1)
    (V1 V2 : Payoff Bool)
    (hvalue1 : V1 = quittingRootSuccessorPayoff reward2 V2 (phaseRoot false p1 hp1_0 hp1_1))
    (hnash1 : IsεQuittingRootEndpointNash reward2 V2 0 (phaseRoot false p1 hp1_0 hp1_1))
    (hvalue2 : V2 = quittingRootSuccessorPayoff reward2 V1 (phaseRoot true p2 hp2_0 hp2_1))
    (hnash2 : IsεQuittingRootEndpointNash reward2 V1 0 (phaseRoot true p2 hp2_0 hp2_1)) :
    ¬ (0 < p1 ∧ 0 < p2) := by
  rintro ⟨hp1_pos, hp2_pos⟩
  have := quittingTwoPhaseClosure_rates_eq_zero p1 p2 hp1_0 hp1_1 hp2_0 hp2_1
    hp1_pos hp2_pos V1 V2 hvalue1 hnash1 hvalue2 hnash2
  linarith [this.1]

end BlockingDigraphUnsolvable

end QuittingRefutedRouteFences

end GameTheory
