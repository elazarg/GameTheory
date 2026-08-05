/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteDynamicDebtPositiveLimit
import GameTheory.Concepts.Stochastic.QuittingTerminalUniformization
import GameTheory.Concepts.Stochastic.QuittingExceptionalTailFallback
import GameTheory.Concepts.Stochastic.BigMatch

/-!
# Exact finite dynamic debt need not vanish

This file records a two-player quitting game whose zero-boundary exact
Nash--Bellman chain is strategically forced: the final
predecessor uses the unique half--half root and has value `(3/2, 0)`, while
every earlier predecessor is all-Continue and preserves that value.  The
corresponding exact dynamic debt is `(1/2, 0)` at every preterminal time.

Nevertheless the game has an exact stationary terminal equilibrium at payoff
`(1, 0)`: player one quits with probability one half and player two always
continues.  Thus vanishing exact debt along finite zero-boundary chains is a
sufficient compiler condition, not a necessary condition for uniform
equilibrium existence.

The terminal simplex coordinate of a finite path is intentionally left free
by the chain definition.  Accordingly the uniqueness statements below concern
the operational preterminal roots and values, never literal equality of whole
finite paths.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace QuittingExactDynamicDebtVanishingCounterexample

/-! We use `false` for player one and `true` for player two. -/

/-- The absorbing payoff table

* `QC ↦ (1, 0)`,
* `CQ ↦ (3, -1)`, and
* `QQ ↦ (2, 1)`.
-/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if false ∈ quitters.1 then
      if true ∈ quitters.1 then
        if who then 1 else 2
      else
        if who then 0 else 1
    else
      if who then -1 else 3

/-- The value forced at every nonterminal point of a positive-length
zero-boundary chain. -/
def trapValue : Payoff Bool := fun who => if who then 0 else 3 / 2

/-- The payoff of the stationary equilibrium that lies outside the
zero-boundary exact-D compiler. -/
def equilibriumValue : Payoff Bool := fun who => if who then 0 else 1

/-- Both players independently quit with probability one half. -/
def mixedRoot : Bool → PMF Bool := fun _ => PMF.uniformOfFintype Bool

/-- Player one quits with probability one half and player two always
continues. -/
def stationaryRoot : Bool → PMF Bool := fun who =>
  if who then PMF.pure false else PMF.uniformOfFintype Bool

/-- Fubini expansion of a two-player Boolean product law. -/
theorem expect_pmfPi_bool (selectedRoot : Bool → PMF Bool)
    (f : (Bool → Bool) → ℝ) :
    expect (pmfPi selectedRoot) f =
      expect (selectedRoot false) (fun first ↦
        expect (selectedRoot true) (fun second ↦
          f (fun who ↦ if who then second else first))) :=
  StochasticGame.BigMatch.expect_pmfPi_bool selectedRoot f

@[simp] theorem expect_uniform_bool (f : Bool → ℝ) :
    expect (PMF.uniformOfFintype Bool) f = (f false + f true) / 2 := by
  rw [expect_eq_sum, Fintype.sum_bool]
  norm_num [PMF.uniformOfFintype_apply]
  ring

/-- Explicit quitter set for a two-coordinate Boolean action. -/
@[simp] theorem quittingQuitters_boolAction (first second : Bool) :
    quittingQuitters (fun who : Bool ↦ if who then second else first) =
      (if first = true then {false} else ∅) ∪
        (if second = true then {true} else ∅) := by
  ext who
  cases who <;> cases first <;> cases second <;>
    simp [quittingQuitters]

@[simp] theorem quittingQuitters_const_true :
    quittingQuitters (fun _ : Bool ↦ true) = {false, true} := by
  ext who
  cases who <;> simp [quittingQuitters]

@[simp] theorem quittingQuitters_id :
    quittingQuitters (fun who : Bool ↦ who) = {true} := by
  ext who
  cases who <;> simp [quittingQuitters]

@[simp] theorem quittingQuitters_not :
    quittingQuitters (fun who : Bool ↦ !who) = {false} := by
  ext who
  cases who <;> simp [quittingQuitters]

@[simp] theorem trapValue_false : trapValue false = 3 / 2 := by
  simp [trapValue]

@[simp] theorem trapValue_true : trapValue true = 0 := by
  simp [trapValue]

@[simp] theorem equilibriumValue_false : equilibriumValue false = 1 := by
  simp [equilibriumValue]

@[simp] theorem equilibriumValue_true : equilibriumValue true = 0 := by
  simp [equilibriumValue]

@[simp] theorem mixedRoot_apply (who : Bool) :
    mixedRoot who = PMF.uniformOfFintype Bool := by
  rfl

@[simp] theorem mixedRoot_quitProbability (who : Bool) :
    (mixedRoot who true).toReal = 1 / 2 := by
  simp [mixedRoot, PMF.uniformOfFintype_apply]

@[simp] theorem stationaryRoot_false :
    stationaryRoot false = PMF.uniformOfFintype Bool := by
  simp [stationaryRoot]

@[simp] theorem stationaryRoot_true :
    stationaryRoot true = PMF.pure false := by
  simp [stationaryRoot]

/-! ## Endpoint formulas -/

/-- Player one's pure-Quit endpoint is `1 + y`, where `y` is player two's
Quit probability. -/
theorem false_quitPayoff (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff reward tail root false =
      1 + (root true true).toReal := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward]
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  ring_nf at hsum ⊢
  linarith

/-- Player one's pure-Continue endpoint is
`3*y + (1-y)*tail₁`. -/
theorem false_continuePayoff (tail : Payoff Bool)
    (root : Bool → PMF Bool) :
    quittingRootContinuePayoff reward tail root false =
      3 * (root true true).toReal +
        (root true false).toReal * tail false := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward]
  ring

/-- Player two's pure-Quit endpoint is `2*p - 1`, where `p` is player one's
Quit probability. -/
theorem true_quitPayoff (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff reward tail root true =
      2 * (root false true).toReal - 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  ring_nf at hsum ⊢
  linarith

/-- Player two's pure-Continue endpoint is its continuation value times
player one's Continue probability. -/
theorem true_continuePayoff (tail : Payoff Bool)
    (root : Bool → PMF Bool) :
    quittingRootContinuePayoff reward tail root true =
      (root false false).toReal * tail true := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward]

@[simp] theorem false_endpointDifference_zero (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward (0 : Payoff Bool) root false =
      1 - 2 * (root true true).toReal := by
  rw [quittingRootEndpointDifference, false_quitPayoff,
    false_continuePayoff]
  simp
  ring

@[simp] theorem true_endpointDifference_zero (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward (0 : Payoff Bool) root true =
      2 * (root false true).toReal - 1 := by
  rw [quittingRootEndpointDifference, true_quitPayoff,
    true_continuePayoff]
  simp

@[simp] theorem false_endpointDifference_trapValue
    (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward trapValue root false =
      -(1 + (root true true).toReal) / 2 := by
  rw [quittingRootEndpointDifference, false_quitPayoff,
    false_continuePayoff, trapValue_false]
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  nlinarith

@[simp] theorem true_endpointDifference_trapValue
    (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward trapValue root true =
      2 * (root false true).toReal - 1 := by
  rw [quittingRootEndpointDifference, true_quitPayoff,
    true_continuePayoff, trapValue_true]
  ring

/-! ## The two unique backward roots -/

/-- A Boolean law whose Quit mass is one half is the uniform law. -/
theorem pmf_bool_eq_uniform_of_apply_true_toReal_eq_half
    (marginal : PMF Bool)
    (htrue : (marginal true).toReal = 1 / 2) :
    marginal = PMF.uniformOfFintype Bool := by
  ext action
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top marginal action)
    (PMF.apply_ne_top (PMF.uniformOfFintype Bool) action)).mp
  cases action
  · have hsum :
        (marginal false).toReal + (marginal true).toReal = 1 := by
      simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one marginal
    rw [htrue] at hsum
    norm_num [PMF.uniformOfFintype_apply]
    linarith
  · simpa [PMF.uniformOfFintype_apply] using htrue

/-- Against the zero tail, exact endpoint Nash forces both players to mix
half--half. -/
theorem root_eq_mixedRoot_of_endpointNash_zero
    (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootEndpointNash reward (0 : Payoff Bool) 0 root) :
    root = mixedRoot := by
  let p : ℝ := (root false true).toReal
  let y : ℝ := (root true true).toReal
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hy0 : 0 ≤ y := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root false
    dsimp only [p]
    nlinarith [ENNReal.toReal_nonneg (a := root false false)]
  have hy1 : y ≤ 1 := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root true
    dsimp only [y]
    nlinarith [ENNReal.toReal_nonneg (a := root true false)]
  have hfalse := hnash false
  have htrue := hnash true
  simp only [false_endpointDifference_zero, true_endpointDifference_zero,
    neg_zero] at hfalse htrue
  change (root false false).toReal * (1 - 2 * y) ≤ 0 ∧
      0 ≤ p * (1 - 2 * y) at hfalse
  change (root true false).toReal * (2 * p - 1) ≤ 0 ∧
      0 ≤ y * (2 * p - 1) at htrue
  have hp : p = 1 / 2 := by
    rcases lt_trichotomy p (1 / 2) with hlt | heq | hgt
    · have hdiff : 2 * p - 1 < 0 := by linarith
      have hy : y = 0 := by
        apply le_antisymm
        · by_contra hnot
          have hypos : 0 < y := lt_of_not_ge hnot
          exact (not_lt_of_ge htrue.2
            (mul_neg_of_pos_of_neg hypos hdiff))
        · exact hy0
      have hpContinue : (root false false).toReal = 1 - p := by
        have hsum :=
          quittingRoot_continueProbability_add_quitProbability root false
        dsimp only [p]
        linarith
      rw [hy, hpContinue] at hfalse
      norm_num at hfalse
      linarith
    · exact heq
    · have hdiff : 0 < 2 * p - 1 := by linarith
      have hy : y = 1 := by
        have hyContinue : (root true false).toReal = 1 - y := by
          have hsum :=
            quittingRoot_continueProbability_add_quitProbability root true
          dsimp only [y]
          linarith
        rw [hyContinue] at htrue
        by_contra hne
        have hltOne : y < 1 := lt_of_le_of_ne hy1 hne
        have hpos : 0 < (1 - y) * (2 * p - 1) :=
          mul_pos (by linarith) hdiff
        exact (not_lt_of_ge (show (1 - y) * (2 * p - 1) ≤ 0 from htrue.1)
          hpos)
      rw [hy] at hfalse
      norm_num at hfalse
      have hppos : 0 < p := lt_trans (by norm_num) hgt
      nlinarith
  have hy : y = 1 / 2 := by
    have hpContinue : (root false false).toReal = 1 - p := by
      have hsum :=
        quittingRoot_continueProbability_add_quitProbability root false
      dsimp only [p]
      linarith
    rw [hpContinue] at hfalse
    change (1 - p) * (1 - 2 * y) ≤ 0 ∧
      0 ≤ p * (1 - 2 * y) at hfalse
    rw [hp] at hfalse
    norm_num at hfalse
    linarith
  funext who
  cases who
  · simpa [mixedRoot] using
      pmf_bool_eq_uniform_of_apply_true_toReal_eq_half (root false) hp
  · simpa [mixedRoot] using
      pmf_bool_eq_uniform_of_apply_true_toReal_eq_half (root true) hy

/-- Equivalent root-Nash formulation of the zero-tail uniqueness result. -/
theorem root_eq_mixedRoot_of_nash_zero
    (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootNash reward (0 : Payoff Bool) 0 root) :
    root = mixedRoot :=
  root_eq_mixedRoot_of_endpointNash_zero root
    ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (0 : Payoff Bool) root).mpr hnash)

/-- The half--half root is exact Nash against the zero tail. -/
theorem mixedRoot_isEndpointNash_zero :
    IsεQuittingRootEndpointNash reward (0 : Payoff Bool) 0 mixedRoot := by
  intro who
  cases who <;>
    norm_num [mixedRoot]

/-- The half--half root sends the zero tail to the trap value. -/
theorem mixedRoot_successor_zero :
    quittingRootSuccessorPayoff reward (0 : Payoff Bool) mixedRoot =
      trapValue := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  cases who
  · rw [false_quitPayoff, false_continuePayoff]
    norm_num [mixedRoot, trapValue, PMF.uniformOfFintype_apply]
  · rw [true_quitPayoff, true_continuePayoff]
    norm_num [mixedRoot, trapValue, PMF.uniformOfFintype_apply]

/-- Against the trap tail, exact endpoint Nash forces all-Continue. -/
theorem root_eq_allContinue_of_endpointNash_trapValue
    (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootEndpointNash reward trapValue 0 root) :
    root = quittingAllContinueRoot := by
  have hfalse := (hnash false).2
  rw [false_endpointDifference_trapValue] at hfalse
  have hy0 : 0 ≤ (root true true).toReal := ENNReal.toReal_nonneg
  have hfactor : 0 < (1 + (root true true).toReal) / 2 := by
    positivity
  have hp : (root false true).toReal = 0 := by
    apply le_antisymm
    · by_contra hnot
      have hppos : 0 < (root false true).toReal :=
        lt_of_not_ge hnot
      have hneg :
          (root false true).toReal *
              (-(1 + (root true true).toReal) / 2) < 0 := by
        exact mul_neg_of_pos_of_neg hppos (by linarith)
      exact (not_lt_of_ge hfalse (by simpa using hneg))
    · exact ENNReal.toReal_nonneg
  have htrue := (hnash true).2
  rw [true_endpointDifference_trapValue, hp] at htrue
  norm_num at htrue
  have hy : (root true true).toReal = 0 := by
    nlinarith [ENNReal.toReal_nonneg (a := root true true)]
  funext who
  cases who
  · simpa [quittingAllContinueRoot] using
      pmf_eq_pure_false_of_apply_true_toReal_eq_zero (root false) hp
  · simpa [quittingAllContinueRoot] using
      pmf_eq_pure_false_of_apply_true_toReal_eq_zero (root true) hy

/-- Equivalent root-Nash formulation of trap-tail uniqueness. -/
theorem root_eq_allContinue_of_nash_trapValue
    (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootNash reward trapValue 0 root) :
    root = quittingAllContinueRoot :=
  root_eq_allContinue_of_endpointNash_trapValue root
    ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward trapValue root).mpr hnash)

/-- All-Continue is exact Nash against the trap tail. -/
theorem allContinueRoot_isEndpointNash_trapValue :
    IsεQuittingRootEndpointNash reward trapValue 0
      (quittingAllContinueRoot : Bool → PMF Bool) := by
  intro who
  cases who
  · rw [false_endpointDifference_trapValue]
    norm_num [quittingAllContinueRoot]
  · rw [true_endpointDifference_trapValue]
    norm_num [quittingAllContinueRoot]

/-- All-Continue preserves the trap value. -/
theorem allContinueRoot_successor_trapValue :
    quittingRootSuccessorPayoff reward trapValue
        (quittingAllContinueRoot : Bool → PMF Bool) = trapValue :=
  quittingRootSuccessorPayoff_allContinueRoot_eq reward trapValue

/-! ## Forced finite zero-boundary chains -/

/-- The last predecessor of a zero terminal value has the unique operational
root `mixedRoot` and value `trapValue`. -/
theorem edge_to_zero_forced
    (current successor : QuittingNashBellmanPoint Bool)
    (hedge : IsQuittingNashBellmanEdge reward current successor)
    (hsuccessor : successor.1 = 0) :
    quittingRootOfSimplex current.2 = mixedRoot ∧
      current.1 = trapValue := by
  have hnash : IsεQuittingRootEndpointNash reward (0 : Payoff Bool) 0
      (quittingRootOfSimplex current.2) := by
    simpa [hsuccessor] using hedge.2
  have hroot := root_eq_mixedRoot_of_endpointNash_zero _ hnash
  refine ⟨hroot, ?_⟩
  rw [hedge.1, hsuccessor, hroot, mixedRoot_successor_zero]

/-- Every exact Nash--Bellman predecessor of the trap has the unique
operational all-Continue root and preserves the trap value. -/
theorem edge_to_trapValue_forced
    (current successor : QuittingNashBellmanPoint Bool)
    (hedge : IsQuittingNashBellmanEdge reward current successor)
    (hsuccessor : successor.1 = trapValue) :
    quittingRootOfSimplex current.2 = quittingAllContinueRoot ∧
      current.1 = trapValue := by
  have hnash : IsεQuittingRootEndpointNash reward trapValue 0
      (quittingRootOfSimplex current.2) := by
    simpa [hsuccessor] using hedge.2
  have hroot := root_eq_allContinue_of_endpointNash_trapValue _ hnash
  refine ⟨hroot, ?_⟩
  rw [hedge.1, hsuccessor, hroot,
    allContinueRoot_successor_trapValue]

/-- At a positive reverse distance from the zero boundary, every admissible
path has the trap value.  Its operational root is half--half at reverse
distance one and all-Continue at every larger reverse distance. -/
theorem finitePath_forced_at_positive_distance
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath Bool cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (remaining time : ℕ) (hpositive : 0 < remaining)
    (hsum : time + remaining = cutoff) :
    quittingFiniteNashBellmanPathValue cutoff path time = trapValue ∧
      quittingFiniteNashBellmanPathRoots cutoff path time =
        if remaining = 1 then mixedRoot else quittingAllContinueRoot := by
  induction remaining generalizing time with
  | zero => omega
  | succ remaining ih =>
      have htime : time < cutoff := by omega
      let index : Fin cutoff := ⟨time, htime⟩
      let current := path (Fin.castSucc index)
      let successor := path (Fin.succ index)
      have hedge : IsQuittingNashBellmanEdge reward current successor :=
        hpath.2.2 index
      have hcurrentValue :
          quittingFiniteNashBellmanPathValue cutoff path time =
            current.1 := by
        simp [quittingFiniteNashBellmanPathValue, current, index,
          Nat.lt_succ_of_lt htime]
      have hcurrentRoot :
          quittingFiniteNashBellmanPathRoots cutoff path time =
            quittingRootOfSimplex current.2 := by
        simp [quittingFiniteNashBellmanPathRoots, current, index, htime]
      by_cases hremaining : remaining = 0
      · subst remaining
        have hsuccessor : successor.1 = 0 := by
          have hindex : Fin.succ index = Fin.last cutoff := by
            ext
            simp [index]
            omega
          change (path (Fin.succ index)).1 = 0
          rw [hindex]
          exact hpath.2.1
        have hforced := edge_to_zero_forced current successor hedge hsuccessor
        constructor
        · rw [hcurrentValue, hforced.2]
        · rw [hcurrentRoot, hforced.1]
          simp
      · have hremainingPositive : 0 < remaining :=
          Nat.pos_of_ne_zero hremaining
        have htail := ih (time + 1) hremainingPositive (by omega)
        have hsuccessorValue :
            quittingFiniteNashBellmanPathValue cutoff path (time + 1) =
              successor.1 := by
          simp [quittingFiniteNashBellmanPathValue, successor, index,
            Nat.succ_lt_succ htime]
        have hsuccessor : successor.1 = trapValue := by
          rw [← hsuccessorValue]
          exact htail.1
        have hforced :=
          edge_to_trapValue_forced current successor hedge hsuccessor
        constructor
        · rw [hcurrentValue, hforced.2]
        · rw [hcurrentRoot, hforced.1]
          simp [hremaining]

/-- In particular, every positive-length admissible path begins at the trap
value. -/
theorem finitePath_initialValue_forced
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (path : QuittingFiniteNashBellmanPath Bool cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteNashBellmanPathValue cutoff path 0 = trapValue := by
  exact (finitePath_forced_at_positive_distance cutoff path hpath
    cutoff 0 hcutoff (by simp)).1

/-! ## The nonvanishing exact debt -/

@[simp] theorem positiveSingletonDebtCap_false :
    quittingPositiveSingletonDebtCap reward false = 1 := by
  simp [quittingPositiveSingletonDebtCap, reward,
    quittingSingletonTerminal]

@[simp] theorem positiveSingletonDebtCap_true :
    quittingPositiveSingletonDebtCap reward true = 0 := by
  simp [quittingPositiveSingletonDebtCap, reward,
    quittingSingletonTerminal]

/-- With two players, player one's fixed-opponent Continue mass is exactly
player two's Continue probability. -/
theorem fixedOpponentsContinueMass_false
    (roots : ℕ → Bool → PMF Bool) (time : ℕ) :
    quittingFixedOpponentsContinueMass roots false time =
      (roots time true false).toReal := by
  unfold quittingFixedOpponentsContinueMass
    quittingStationaryContinueMass
  simp [pmfPi_apply, quittingAllContinueAction]

/-- Symmetrically, player two's fixed-opponent Continue mass is player one's
Continue probability. -/
theorem fixedOpponentsContinueMass_true
    (roots : ℕ → Bool → PMF Bool) (time : ℕ) :
    quittingFixedOpponentsContinueMass roots true time =
      (roots time false false).toReal := by
  unfold quittingFixedOpponentsContinueMass
    quittingStationaryContinueMass
  simp [pmfPi_apply, quittingAllContinueAction]

/-- Every preterminal point of every admissible path carries exact dynamic
debt `(1/2, 0)`. -/
theorem finitePath_dynamicDebt_forced_at_positive_distance
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath Bool cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (remaining time : ℕ) (hpositive : 0 < remaining)
    (hsum : time + remaining = cutoff) :
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path false time =
        1 / 2 ∧
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff path true time =
        0 := by
  induction remaining generalizing time with
  | zero => omega
  | succ remaining ih =>
      let roots := quittingFiniteNashBellmanPathRoots cutoff path
      let value := quittingFiniteNashBellmanPathValue cutoff path
      have hcurrent := finitePath_forced_at_positive_distance
        cutoff path hpath (remaining + 1) time (by omega) hsum
      have hcurrentFalse : value time false = 3 / 2 := by
        dsimp only [value]
        rw [hcurrent.1]
        simp
      have hcurrentTrue : value time true = 0 := by
        dsimp only [value]
        rw [hcurrent.1]
        simp
      have hfuel : cutoff - time = remaining + 1 := by omega
      by_cases hremaining : remaining = 0
      · subst remaining
        have hnext : value (time + 1) = 0 := by
          dsimp only [value]
          have htime : time + 1 = cutoff := by omega
          rw [htime]
          exact quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
            reward cutoff path hpath
        have hroot : roots time = mixedRoot := by
          dsimp only [roots]
          simpa using hcurrent.2
        constructor
        · unfold quittingFiniteNashBellmanPathDynamicDebt
          rw [hfuel, quittingFiniteDynamicDebt_succ_eq_endpoints]
          change
            max
                (quittingRootQuitPayoff reward
                  (fun _ ↦ value (time + 1) false) (roots time) false)
                (quittingRootContinuePayoff reward
                    (fun _ ↦ value (time + 1) false) (roots time) false +
                  quittingFixedOpponentsContinueMass roots false time *
                    quittingFiniteDynamicDebt reward roots false
                      (fun liveTime ↦ value liveTime false)
                      (quittingPositiveSingletonDebtCap reward false)
                      (time + 1) 0) -
              value time false = 1 / 2
          rw [hroot, false_quitPayoff, false_continuePayoff,
            fixedOpponentsContinueMass_false, hroot, hnext,
            hcurrentFalse]
          norm_num [mixedRoot, PMF.uniformOfFintype_apply]
        · unfold quittingFiniteNashBellmanPathDynamicDebt
          rw [hfuel, quittingFiniteDynamicDebt_succ_eq_endpoints]
          change
            max
                (quittingRootQuitPayoff reward
                  (fun _ ↦ value (time + 1) true) (roots time) true)
                (quittingRootContinuePayoff reward
                    (fun _ ↦ value (time + 1) true) (roots time) true +
                  quittingFixedOpponentsContinueMass roots true time *
                    quittingFiniteDynamicDebt reward roots true
                      (fun liveTime ↦ value liveTime true)
                      (quittingPositiveSingletonDebtCap reward true)
                      (time + 1) 0) -
              value time true = 0
          rw [hroot, true_quitPayoff, true_continuePayoff,
            fixedOpponentsContinueMass_true, hroot, hnext,
            hcurrentTrue]
          norm_num [mixedRoot, PMF.uniformOfFintype_apply]
      · have hremainingPositive : 0 < remaining :=
          Nat.pos_of_ne_zero hremaining
        have htail := ih (time + 1) hremainingPositive (by omega)
        have hnextForced := finitePath_forced_at_positive_distance
          cutoff path hpath remaining (time + 1) hremainingPositive (by omega)
        have hnext : value (time + 1) = trapValue := by
          exact hnextForced.1
        have hroot : roots time = quittingAllContinueRoot := by
          dsimp only [roots]
          simpa [hremaining] using hcurrent.2
        have htailFuel : cutoff - (time + 1) = remaining := by omega
        have htailFalse :
            quittingFiniteDynamicDebt reward roots false
                (fun liveTime ↦ value liveTime false)
                (quittingPositiveSingletonDebtCap reward false)
                (time + 1) remaining = 1 / 2 := by
          rw [← htailFuel]
          exact htail.1
        have htailTrue :
            quittingFiniteDynamicDebt reward roots true
                (fun liveTime ↦ value liveTime true)
                (quittingPositiveSingletonDebtCap reward true)
                (time + 1) remaining = 0 := by
          rw [← htailFuel]
          exact htail.2
        constructor
        · unfold quittingFiniteNashBellmanPathDynamicDebt
          rw [hfuel, quittingFiniteDynamicDebt_succ_eq_endpoints]
          change
            max
                (quittingRootQuitPayoff reward
                  (fun _ ↦ value (time + 1) false) (roots time) false)
                (quittingRootContinuePayoff reward
                    (fun _ ↦ value (time + 1) false) (roots time) false +
                  quittingFixedOpponentsContinueMass roots false time *
                    quittingFiniteDynamicDebt reward roots false
                      (fun liveTime ↦ value liveTime false)
                      (quittingPositiveSingletonDebtCap reward false)
                      (time + 1) remaining) -
              value time false = 1 / 2
          rw [hroot, false_quitPayoff, false_continuePayoff,
            fixedOpponentsContinueMass_false, hroot, hnext,
            htailFalse, hcurrentFalse]
          norm_num [quittingAllContinueRoot]
        · unfold quittingFiniteNashBellmanPathDynamicDebt
          rw [hfuel, quittingFiniteDynamicDebt_succ_eq_endpoints]
          change
            max
                (quittingRootQuitPayoff reward
                  (fun _ ↦ value (time + 1) true) (roots time) true)
                (quittingRootContinuePayoff reward
                    (fun _ ↦ value (time + 1) true) (roots time) true +
                  quittingFixedOpponentsContinueMass roots true time *
                    quittingFiniteDynamicDebt reward roots true
                      (fun liveTime ↦ value liveTime true)
                      (quittingPositiveSingletonDebtCap reward true)
                      (time + 1) remaining) -
              value time true = 0
          rw [hroot, true_quitPayoff, true_continuePayoff,
            fixedOpponentsContinueMass_true, hroot, hnext,
            htailTrue, hcurrentTrue]
          norm_num [quittingAllContinueRoot]

/-- Initial exact debt of every positive-length admissible path. -/
theorem finitePath_initialDynamicDebt_forced
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (path : QuittingFiniteNashBellmanPath Bool cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path false 0 =
        1 / 2 ∧
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff path true 0 =
        0 := by
  exact finitePath_dynamicDebt_forced_at_positive_distance
    cutoff path hpath cutoff 0 hcutoff (by simp)

/-- Every positive-length admissible path has aggregate exact debt one half. -/
theorem finitePath_aggregateDynamicDebt_eq_half
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (path : QuittingFiniteNashBellmanPath Bool cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteNashBellmanPathAggregateDynamicDebt reward cutoff path =
      1 / 2 := by
  have hdebt := finitePath_initialDynamicDebt_forced
    cutoff hcutoff path hpath
  unfold quittingFiniteNashBellmanPathAggregateDynamicDebt
  rw [Fintype.sum_bool, hdebt.1, hdebt.2]
  ring

/-- Every positive-length admissible path has literal maximum exact debt one
half. -/
theorem finitePath_maxDynamicDebt_eq_half
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    (path : QuittingFiniteNashBellmanPath Bool cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff path =
      1 / 2 := by
  have hdebt := finitePath_initialDynamicDebt_forced
    cutoff hcutoff path hpath
  apply le_antisymm
  · unfold quittingFiniteNashBellmanPathMaxDynamicDebt
    apply Finset.sup'_le
    intro who _
    cases who
    · exact hdebt.1.le
    · rw [hdebt.2]
      norm_num
  · rw [← hdebt.1]
    exact quittingFiniteNashBellmanPathDynamicDebt_le_max
      reward cutoff path false

/-- The cutoff-zero aggregate objective is one on every admissible path. -/
theorem finitePath_aggregateDynamicDebt_zeroCutoff
    (path : QuittingFiniteNashBellmanPath Bool 0) :
    quittingFiniteNashBellmanPathAggregateDynamicDebt reward 0 path = 1 := by
  unfold quittingFiniteNashBellmanPathAggregateDynamicDebt
    quittingFiniteNashBellmanPathDynamicDebt
  rw [Fintype.sum_bool]
  norm_num

/-- The cutoff-zero maximum objective is one on every admissible path. -/
theorem finitePath_maxDynamicDebt_zeroCutoff
    (path : QuittingFiniteNashBellmanPath Bool 0) :
    quittingFiniteNashBellmanPathMaxDynamicDebt reward 0 path = 1 := by
  apply le_antisymm
  · unfold quittingFiniteNashBellmanPathMaxDynamicDebt
    apply Finset.sup'_le
    intro who _
    cases who <;>
      simp [quittingFiniteNashBellmanPathDynamicDebt]
  · have hfalse := quittingFiniteNashBellmanPathDynamicDebt_le_max
      reward 0 path false
    simpa [quittingFiniteNashBellmanPathDynamicDebt] using hfalse

/-- The attained aggregate optimum is exactly one half at every positive
cutoff. -/
theorem minDynamicDebt_eq_half
    (cutoff : ℕ) (hcutoff : 0 < cutoff) :
    quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff =
      1 / 2 := by
  unfold quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
  exact finitePath_aggregateDynamicDebt_eq_half cutoff hcutoff _
    (quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer_mem
      reward cutoff)

/-- The attained literal min-max optimum is exactly one half at every
positive cutoff. -/
theorem minMaxDynamicDebt_eq_half
    (cutoff : ℕ) (hcutoff : 0 < cutoff) :
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff =
      1 / 2 := by
  unfold quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
  exact finitePath_maxDynamicDebt_eq_half cutoff hcutoff _
    (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff)

@[simp] theorem minDynamicDebt_zero :
    quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward 0 = 1 := by
  unfold quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
  exact finitePath_aggregateDynamicDebt_zeroCutoff _

@[simp] theorem minMaxDynamicDebt_zero :
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward 0 = 1 := by
  unfold quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
  exact finitePath_maxDynamicDebt_zeroCutoff _

/-- The optimized aggregate exact debt has positive infimum one half. -/
theorem iInf_minDynamicDebt_eq_half :
    (⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff) =
        1 / 2 := by
  have hbdd : BddBelow (Set.range fun cutoff : ℕ ↦
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff) := by
    refine ⟨0, ?_⟩
    rintro value ⟨cutoff, rfl⟩
    exact quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt_nonneg
      reward cutoff
  apply le_antisymm
  · calc
      (⨅ cutoff : ℕ,
          quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff) ≤
          quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward 1 :=
        ciInf_le hbdd 1
      _ = 1 / 2 := minDynamicDebt_eq_half 1 (by omega)
  · apply le_ciInf
    intro cutoff
    cases cutoff with
    | zero => norm_num
    | succ cutoff =>
        rw [minDynamicDebt_eq_half (cutoff + 1) (by omega)]

/-- **Failure of exact-D vanishing.**  The optimized playerwise maximum
exact debt also has positive infimum one half. -/
theorem iInf_minMaxDynamicDebt_eq_half :
    (⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff) =
        1 / 2 := by
  have hbdd : BddBelow (Set.range fun cutoff : ℕ ↦
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff) := by
    refine ⟨0, ?_⟩
    rintro value ⟨cutoff, rfl⟩
    exact quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_nonneg
      reward cutoff
  apply le_antisymm
  · calc
      (⨅ cutoff : ℕ,
          quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff) ≤
          quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward 1 :=
        ciInf_le hbdd 1
      _ = 1 / 2 := minMaxDynamicDebt_eq_half 1 (by omega)
  · apply le_ciInf
    intro cutoff
    cases cutoff with
    | zero => norm_num
    | succ cutoff =>
        rw [minMaxDynamicDebt_eq_half (cutoff + 1) (by omega)]

/-! ## The exact stationary equilibrium outside the compiler -/

/-- The displayed stationary root is exact endpoint Nash at its own payoff
vector. -/
theorem stationaryRoot_isEndpointNash :
    IsεQuittingRootEndpointNash reward equilibriumValue 0 stationaryRoot := by
  intro who
  cases who
  · rw [quittingRootEndpointDifference, false_quitPayoff,
      false_continuePayoff]
    norm_num [stationaryRoot, equilibriumValue,
      PMF.uniformOfFintype_apply]
  · rw [quittingRootEndpointDifference, true_quitPayoff,
      true_continuePayoff]
    norm_num [stationaryRoot, equilibriumValue,
      PMF.uniformOfFintype_apply]

/-- The stationary root's Bellman successor is exactly `(1,0)`. -/
theorem stationaryRoot_successor :
    quittingRootSuccessorPayoff reward equilibriumValue stationaryRoot =
      equilibriumValue := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  cases who
  · rw [false_quitPayoff, false_continuePayoff]
    norm_num [stationaryRoot, equilibriumValue,
      PMF.uniformOfFintype_apply]
  · rw [true_quitPayoff, true_continuePayoff]
    norm_num [stationaryRoot, equilibriumValue,
      PMF.uniformOfFintype_apply]

/-- The stationary root is the standard solo stationary root owned by player
one. -/
theorem stationaryRoot_eq_solo :
    stationaryRoot = quittingSoloStationaryRoot false
      (PMF.uniformOfFintype Bool) := by
  funext who
  cases who <;>
    simp [stationaryRoot, quittingSoloStationaryRoot]

/-- The stationary profile's terminal payoff is exactly `(1,0)`. -/
theorem terminalPayoff_stationaryRoot (who : Bool) :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward stationaryRoot) who =
      equilibriumValue who := by
  rw [stationaryRoot_eq_solo,
    quittingTerminalPayoff_soloStationary reward false who
      (PMF.uniformOfFintype Bool) (by
        norm_num [PMF.uniformOfFintype_apply])]
  cases who <;>
    simp [quittingSoloReward, reward, equilibriumValue]

/-- Player two's stationary fixed-opponent Quit value is zero. -/
theorem stationaryFixedOpponentsQuitValue_true :
    quittingStationaryFixedOpponentsQuitValue reward stationaryRoot true =
      0 := by
  unfold quittingStationaryFixedOpponentsQuitValue
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    reward (fun _ ↦ stationaryRoot) true (0 : Payoff Bool) 0,
    true_quitPayoff]
  norm_num [stationaryRoot, PMF.uniformOfFintype_apply]

/-- Player one's stationary hazard makes player two's opponent-only process
contract by one half each stage. -/
theorem stationaryFixedOpponentsContinueMass_true_lt_one :
    quittingStationaryFixedOpponentsContinueMass stationaryRoot true < 1 := by
  unfold quittingStationaryFixedOpponentsContinueMass
  rw [fixedOpponentsContinueMass_true]
  norm_num [stationaryRoot, PMF.uniformOfFintype_apply]

/-- Player two's full stationary unilateral cap is zero. -/
theorem stationaryUnilateralCap_true :
    quittingStationaryUnilateralCap reward stationaryRoot true = 0 := by
  have hpositive :
      0 < ((PMF.uniformOfFintype Bool) true).toReal := by
    norm_num [PMF.uniformOfFintype_apply]
  have hquit := stationaryFixedOpponentsQuitValue_true
  rw [stationaryRoot_eq_solo] at hquit ⊢
  rw [quittingStationaryUnilateralCap_solo_other reward
    (show true ≠ false by decide) (PMF.uniformOfFintype Bool) hpositive,
    hquit]
  simp [quittingSoloReward, reward]

/-- The stationary profile is an exact equilibrium for the terminal payoff
functional, including arbitrary history-dependent deviations. -/
theorem stationaryProfile_isTerminalNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward stationaryRoot) := by
  intro who deviation
  cases who
  · have howner := quittingTerminalPayoff_update_solo_owner_le
      reward false (PMF.uniformOfFintype Bool) deviation
    rw [← stationaryRoot_eq_solo] at howner
    calc
      quittingTerminalPayoff reward
          (Function.update
            (quittingStationaryProfile reward stationaryRoot) false
            deviation) false ≤ 1 := by
        simpa [quittingSoloReward, reward] using howner
      _ = quittingTerminalPayoff reward
          (quittingStationaryProfile reward stationaryRoot) false + 0 := by
        rw [terminalPayoff_stationaryRoot]
        simp
  · have hcap :=
      quittingTerminalPayoff_update_stationary_le_unilateralCap
        reward stationaryRoot true deviation
          stationaryFixedOpponentsContinueMass_true_lt_one
    calc
      quittingTerminalPayoff reward
          (Function.update
            (quittingStationaryProfile reward stationaryRoot) true
            deviation) true ≤
        quittingStationaryUnilateralCap reward stationaryRoot true := hcap
      _ = quittingTerminalPayoff reward
          (quittingStationaryProfile reward stationaryRoot) true + 0 := by
        rw [stationaryUnilateralCap_true,
          terminalPayoff_stationaryRoot]
        simp

/-- The same stationary profile is a uniform epsilon-equilibrium for every
positive error. -/
theorem stationaryProfile_isUniformεEquilibrium
    {ε : ℝ} (hε : 0 < ε) :
    (quittingGame reward).IsUniformεEquilibrium none ε
      (quittingStationaryProfile reward stationaryRoot) :=
  quittingGame_isUniformεEquilibrium_of_terminalNash_finite
    reward (quittingStationaryProfile reward stationaryRoot)
      hε stationaryProfile_isTerminalNash

/-- Despite the positive optimized exact-D infimum, `(1,0)` is a concrete
uniform-equilibrium payoff of the game. -/
theorem equilibriumValue_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none equilibriumValue := by
  intro ε hε
  obtain ⟨nashThreshold, hnashThreshold⟩ :=
    stationaryProfile_isUniformεEquilibrium hε
  have heventuallyDelivery : ∀ᶠ horizon : ℕ in Filter.atTop, ∀ who,
      |(quittingGame reward).finiteAveragePayoff none horizon
          (quittingStationaryProfile reward stationaryRoot) who -
        equilibriumValue who| ≤ ε := by
    apply Filter.eventually_all.mpr
    intro who
    have hball :=
      (tendsto_finiteAveragePayoff_quittingGame reward
        (quittingStationaryProfile reward stationaryRoot) who).eventually
        (Metric.ball_mem_nhds
          (quittingTerminalPayoff reward
            (quittingStationaryProfile reward stationaryRoot) who) hε)
    filter_upwards [hball] with horizon hhorizon
    rw [terminalPayoff_stationaryRoot] at hhorizon
    simpa [Metric.mem_ball, Real.dist_eq] using hhorizon.le
  obtain ⟨deliveryThreshold, hdeliveryThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨quittingStationaryProfile reward stationaryRoot,
    max nashThreshold deliveryThreshold, fun horizon hhorizon ↦ ?_⟩
  constructor
  · exact hnashThreshold horizon
      (le_trans (Nat.le_max_left _ _) hhorizon)
  · exact hdeliveryThreshold horizon
      (le_trans (Nat.le_max_right _ _) hhorizon)

end QuittingExactDynamicDebtVanishingCounterexample

end GameTheory
