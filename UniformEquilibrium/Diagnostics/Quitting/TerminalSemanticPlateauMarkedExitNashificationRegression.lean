/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMarkedVariational
import UniformEquilibrium.Quitting.Debt.Dynamic.ExactDynamicDebtVanishingCounterexample

/-!
# A regression for Nashifying a marked sure-exit row

The marked variational argument can produce a product row at which one
player quits surely, has zero local defect, and meets a positive collision
atom.  It is tempting to hold that player fixed and Nashify the other
coordinates while retaining either the collision or the marked player's
Quit inequality.  This file gives a two-player quantitative counterexample.

Player `false` is marked.  The all-Quit row gives the marked player payoff
`1` from Quit and `0` from Continue, so its local defect is zero and the
collision has probability one.  Player `true`, however, receives `1` from
Continue and `0` from Quit against every marginal of the marked player.
Thus every exact Nashification of the unmarked coordinate removes its Quit
mass.  Once that mass is removed, the marked player's endpoint difference
is `-1`.

More quantitatively, an `ε`-Nash unmarked coordinate has Quit probability at
most `ε`, and hence the marked endpoint difference is at most `2 * ε - 1`.
It is therefore strictly negative whenever `ε < 1/2`.  Positive collision
support plus one marked first-order condition is not a closed constraint
under even approximate Nashification of the other coordinates.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The exact finite premise that does survive -/

/-- On one fixed, co-realized row, a marked sure-Quit inequality plus the
endpoint `ε`-Nash inequalities for every other coordinate gives full root
endpoint `ε`-Nash.  A minimum-tail assumption is useful here only if it
actually supplies these missing same-row inequalities; minimum provenance
alone does not enter this finite statement. -/
theorem isεQuittingRootEndpointNash_of_marked_sureQuit_of_others
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (marked : ι) (ε : ℝ)
    (hε : 0 ≤ ε) (hsure : root marked = PMF.pure true)
    (hmarked : -ε ≤
      quittingRootEndpointDifference reward tail root marked)
    (hothers : ∀ other, other ≠ marked →
      (root other false).toReal *
            quittingRootEndpointDifference reward tail root other ≤ ε ∧
        -ε ≤ (root other true).toReal *
            quittingRootEndpointDifference reward tail root other) :
    IsεQuittingRootEndpointNash reward tail ε root := by
  intro who
  by_cases hwho : who = marked
  · subst who
    rw [hsure]
    simpa using And.intro hε hmarked
  · exact hothers who hwho

/-- Exact same-row control of every unmarked coordinate turns the marked
sure-exit row into a full exact Nash root. -/
theorem isZeroQuittingRootNash_of_marked_sureQuit_of_others
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (marked : ι)
    (hsure : root marked = PMF.pure true)
    (hmarked : 0 ≤
      quittingRootEndpointDifference reward tail root marked)
    (hothers : ∀ other, other ≠ marked →
      (root other false).toReal *
            quittingRootEndpointDifference reward tail root other ≤ 0 ∧
        0 ≤ (root other true).toReal *
            quittingRootEndpointDifference reward tail root other) :
    IsεQuittingRootNash reward tail 0 root := by
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward tail root).mp
  exact isεQuittingRootEndpointNash_of_marked_sureQuit_of_others
    reward tail root marked 0 (by norm_num) hsure (by simpa using hmarked)
    (by simpa using hothers)

namespace QuittingMarkedExitNashificationRegression

/-- The marked player is `false`.  Its solo reward is `-1`, but its reward
in the collision is `1`.  Player `true` receives `1` exactly when it
continues while the marked player quits. -/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if false ∈ quitters.1 then
      if true ∈ quitters.1 then
        if who then 0 else 1
      else
        if who then 1 else -1
    else
      0

/-- The all-Continue tail pays `0` to the marked player and `1` to the
unmarked player. -/
def tail : Payoff Bool := fun who => if who then 1 else 0

/-- The marked collision row: both players Quit surely. -/
def markedCollisionRoot : Bool → PMF Bool := fun _ => PMF.pure true

/-- The unmarked coordinate has the constant pure-Quit endpoint `0`. -/
theorem quitPayoff_true (root : Bool → PMF Bool) :
    quittingRootQuitPayoff reward tail root true = 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, tail]

/-- The unmarked coordinate has the constant pure-Continue endpoint `1`. -/
theorem continuePayoff_true (root : Bool → PMF Bool) :
    quittingRootContinuePayoff reward tail root true = 1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hc : (root false false).toReal = 1 - (root false true).toReal := by
    linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, tail, hc]

/-- Player `true` strictly prefers Continue at every root. -/
theorem endpointDifference_true (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward tail root true = -1 := by
  rw [quittingRootEndpointDifference, quitPayoff_true, continuePayoff_true]
  norm_num

/-- The marked player's pure-Quit endpoint is `2q-1`, where `q` is the
unmarked player's Quit probability. -/
theorem quitPayoff_false (root : Bool → PMF Bool) :
    quittingRootQuitPayoff reward tail root false =
      2 * (root true true).toReal - 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  have hc : (root true false).toReal = 1 - (root true true).toReal := by
    linarith
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, tail, hc]
  ring

/-- The marked player's pure-Continue endpoint is identically zero. -/
theorem continuePayoff_false (root : Bool → PMF Bool) :
    quittingRootContinuePayoff reward tail root false = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, tail]

/-- The marked endpoint difference is supplied entirely by the unmarked
player's collision probability. -/
theorem endpointDifference_false (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward tail root false =
      2 * (root true true).toReal - 1 := by
  rw [quittingRootEndpointDifference, quitPayoff_false, continuePayoff_false]
  ring

/-- The displayed row has sure marked Quit and sure opponent Quit. -/
theorem markedCollisionRoot_probabilities :
    (markedCollisionRoot false true).toReal = 1 ∧
      (markedCollisionRoot true true).toReal = 1 := by
  simp [markedCollisionRoot]

/-- The exact two-player collision has probability one at the displayed
row, not merely positive marginal support. -/
theorem markedCollisionRoot_collisionMass :
    quittingRootCoalitionMass markedCollisionRoot (Finset.univ : Finset Bool) = 1 := by
  unfold quittingRootCoalitionMass
  have hcomp : (Finset.univ : Finset Bool)ᶜ = ∅ := by
    ext who
    simp
  rw [coalitionMass, hcomp]
  simp [quittingRootQuitRates, markedCollisionRoot]

/-- At the displayed positive-collision row the marked player's Quit
endpoint beats its Continue endpoint by exactly one. -/
theorem markedCollisionRoot_marked_endpointDifference :
    quittingRootEndpointDifference reward tail markedCollisionRoot false = 1 := by
  rw [endpointDifference_false]
  norm_num [markedCollisionRoot]

/-- Consequently the marked coordinate itself satisfies exact endpoint
Nash at the displayed pure-Quit row.  This is the pointwise first-order
information furnished by the marked variational bridge. -/
theorem markedCollisionRoot_marked_endpointNash :
    (markedCollisionRoot false false).toReal *
          quittingRootEndpointDifference reward tail markedCollisionRoot false ≤ 0 ∧
      0 ≤ (markedCollisionRoot false true).toReal *
          quittingRootEndpointDifference reward tail markedCollisionRoot false := by
  rw [markedCollisionRoot_marked_endpointDifference]
  norm_num [markedCollisionRoot]

/-- The marked coordinate's local Nash defect is exactly zero at the
positive-collision row. -/
theorem markedCollisionRoot_marked_coordinateNashDefect :
    quittingRootCoordinateNashDefect reward tail markedCollisionRoot false = 0 := by
  rw [quittingRootCoordinateNashDefect,
    quittingRootSuccessorPayoff_eq_endpointMix,
    quitPayoff_false, continuePayoff_false]
  norm_num [markedCollisionRoot]

/-- Approximate Nashification of the unmarked coordinate forces its Quit
probability below the Nash error.  Only that coordinate's lower endpoint
inequality is used. -/
theorem unmarked_quitProbability_le_error
    (root : Bool → PMF Bool) (ε : ℝ)
    (hunmarked :
      (root true false).toReal *
            quittingRootEndpointDifference reward tail root true ≤ ε ∧
        -ε ≤ (root true true).toReal *
            quittingRootEndpointDifference reward tail root true) :
    (root true true).toReal ≤ ε := by
  rw [endpointDifference_true] at hunmarked
  linarith

/-- After `ε`-Nashifying the unmarked coordinate, the marked Quit advantage
is at most `2ε-1`. -/
theorem marked_endpointDifference_le_two_mul_error_sub_one
    (root : Bool → PMF Bool) (ε : ℝ)
    (hunmarked :
      (root true false).toReal *
            quittingRootEndpointDifference reward tail root true ≤ ε ∧
        -ε ≤ (root true true).toReal *
            quittingRootEndpointDifference reward tail root true) :
    quittingRootEndpointDifference reward tail root false ≤ 2 * ε - 1 := by
  rw [endpointDifference_false]
  linarith [unmarked_quitProbability_le_error root ε hunmarked]

/-- For error below `1/2`, Nashifying the unmarked coordinate strictly
reverses the marked player's exit inequality. -/
theorem marked_endpointDifference_neg_of_unmarked_approximateNash
    (root : Bool → PMF Bool) (ε : ℝ) (hε : ε < 1 / 2)
    (hunmarked :
      (root true false).toReal *
            quittingRootEndpointDifference reward tail root true ≤ ε ∧
        -ε ≤ (root true true).toReal *
            quittingRootEndpointDifference reward tail root true) :
    quittingRootEndpointDifference reward tail root false < 0 := by
  have hle :=
    marked_endpointDifference_le_two_mul_error_sub_one root ε hunmarked
  linarith

/-- Exact Nashification of the unmarked coordinate kills its Quit mass. -/
theorem unmarked_quitProbability_eq_zero_of_exactNash
    (root : Bool → PMF Bool)
    (hunmarked :
      (root true false).toReal *
            quittingRootEndpointDifference reward tail root true ≤ 0 ∧
        0 ≤ (root true true).toReal *
            quittingRootEndpointDifference reward tail root true) :
    (root true true).toReal = 0 := by
  have hle := unmarked_quitProbability_le_error root 0 (by simpa using hunmarked)
  exact le_antisymm hle ENNReal.toReal_nonneg

/-- Exact Nashification of the other coordinate changes the marked endpoint
difference from `1` at the collision row to `-1`. -/
theorem marked_endpointDifference_eq_neg_one_of_unmarked_exactNash
    (root : Bool → PMF Bool)
    (hunmarked :
      (root true false).toReal *
            quittingRootEndpointDifference reward tail root true ≤ 0 ∧
        0 ≤ (root true true).toReal *
            quittingRootEndpointDifference reward tail root true) :
    quittingRootEndpointDifference reward tail root false = -1 := by
  rw [endpointDifference_false,
    unmarked_quitProbability_eq_zero_of_exactNash root hunmarked]
  norm_num

/-- **Regression headline.**  There is no product row that exact-Nashifies
the unmarked coordinate and retains the marked player's weak Quit
inequality.  This remains true even if the marked marginal is held at sure
Quit; the proof does not need that extra restriction. -/
theorem no_exact_unmarked_nashification_retains_marked_exit :
    ¬ ∃ root : Bool → PMF Bool,
      ((root true false).toReal *
              quittingRootEndpointDifference reward tail root true ≤ 0 ∧
          0 ≤ (root true true).toReal *
              quittingRootEndpointDifference reward tail root true) ∧
        0 ≤ quittingRootEndpointDifference reward tail root false := by
  rintro ⟨root, hunmarked, hmarked⟩
  rw [marked_endpointDifference_eq_neg_one_of_unmarked_exactNash root hunmarked]
    at hmarked
  linarith

/-- Every exact endpoint-Nash root has zero Quit probability in both
coordinates.  Thus the only exact Nash outcome is the nonabsorbing
all-Continue outcome, despite the marked collision row above. -/
theorem exact_endpointNash_forces_zero_quit_probabilities
    (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) :
    (root false true).toReal = 0 ∧ (root true true).toReal = 0 := by
  have htrue : (root true true).toReal = 0 :=
    unmarked_quitProbability_eq_zero_of_exactNash root (by simpa using hnash true)
  have hfalseDiff :
      quittingRootEndpointDifference reward tail root false = -1 := by
    rw [endpointDifference_false, htrue]
    norm_num
  have hfalseLe : (root false true).toReal ≤ 0 := by
    have h := (hnash false).2
    rw [hfalseDiff] at h
    linarith
  exact ⟨le_antisymm hfalseLe ENNReal.toReal_nonneg, htrue⟩

end QuittingMarkedExitNashificationRegression

end GameTheory
