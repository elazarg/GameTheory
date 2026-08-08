/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.DisjunctionCounterexample
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot
import UniformEquilibrium.Quitting.Stationary.BestResponse
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# The isolated-negative branch is not vacuous: a repair for the counterexample weight

`QuittingDisjunctionCounterexample.lean` and `QuittingThreeBranchDisjunction.lean` place
`QuittingDisjunctionCounterexample.reward` in the third (isolated-negative) branch of the
repaired trichotomy, a branch with **no sufficiency theorem**.  This file shows the branch
is not vacuous as a producer for this specific weight: for every `ε > 0` there is an actual
behavior profile whose every unilateral deviation gains at most `ε`, so the weight *does*
have a uniform equilibrium payoff, even though neither the zero-solo nor the admissible-cycle
route can certify it.

## The repair profile

Both coordinates play the constant hazard `p` at every stage (`repairRoot`), for `p` small.
Unlike the exact `witnessRoot` of `QuittingDisjunctionCounterexample.lean` (`q = 1`, `p = 0`),
this keeps **both** opponents' continuation mass strictly below one, so the stationary
best-response theory of `QuittingStationaryBestResponse.lean` applies directly: the
best-response cap of each coordinate is the explicit `max` of quitting immediately and never
quitting (`quittingStationaryUnilateralCap`), with no `ε = 0` degeneracy.

Exact computation gives cap `1` for coordinate `false` against honest payoff `≥ 1 - p`, and cap
`2p - 1` for coordinate `true` against honest payoff `≥ -1`.  Both deviation gains are therefore
at most `2p`, so `p = ε / 2` (clipped to `1`) makes the stationary profile an `ε`-asymptotic-Nash
equilibrium.  Feeding this into the base bridge
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors` produces an honest
uniform equilibrium payoff for the counterexample weight.

## What this does not say

This does not certify the isolated-negative branch in general: the construction is specific to
this weight's two-coordinate table (in particular, to `r_2({2}) = -1` being reachable from a
symmetric contracting perturbation of the isolated configuration).  No general sufficiency
theorem for `HasIsolatedNegativeAbsorbingQuittingCycle` is produced here.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

namespace QuittingDisjunctionCounterexample

/-! ## The repair root: a symmetric constant hazard -/

/-- Both coordinates quit with the same constant probability `p` at every stage. -/
def repairRoot (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Bool → PMF Bool :=
  fun _ => quittingHazardCoin p hp0 hp1

@[simp] theorem repairRoot_true_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (who : Bool) :
    (repairRoot p hp0 hp1 who true).toReal = p := by
  simp [repairRoot]

@[simp] theorem repairRoot_false_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (who : Bool) :
    (repairRoot p hp0 hp1 who false).toReal = 1 - p := by
  simp [repairRoot]

section Repair

variable (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)

/-! ### The stationary quit/continue data -/

/-- The stationary fixed-opponents quit value is the one-root quit payoff of
the repair root against any tail, since quitting depends only on the current
root. -/
theorem repairQuitValue_eq (who : Bool) :
    quittingStationaryFixedOpponentsQuitValue reward (repairRoot p hp0 hp1) who =
      quittingRootQuitPayoff reward (0 : Payoff Bool) (repairRoot p hp0 hp1) who :=
  (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
    (fun _ : ℕ => repairRoot p hp0 hp1) who 0 0).symm

/-- Reads off the stationary continuation reward and continuation mass at
`who` from two evaluations of the one-root continue payoff (an affine
function of `tail who`), at `tail who = 0` and `tail who = 1`. -/
theorem repairContinueReward_mass_eq (who : Bool)
    (continueReward continueMass : ℝ)
    (h0 : quittingRootContinuePayoff reward (fun _ => (0 : ℝ)) (repairRoot p hp0 hp1) who =
      continueReward)
    (h1 : quittingRootContinuePayoff reward (fun _ => (1 : ℝ)) (repairRoot p hp0 hp1) who =
      continueReward + continueMass) :
    quittingFixedOpponentsContinueReward reward
        (fun _ : ℕ => repairRoot p hp0 hp1) who 0 = continueReward ∧
      quittingFixedOpponentsContinueMass
        (fun _ : ℕ => repairRoot p hp0 hp1) who 0 = continueMass := by
  have e0 := quittingRootContinuePayoff_eq_fixedOpponents reward
    (fun _ : ℕ => repairRoot p hp0 hp1) who (fun _ => (0 : ℝ)) 0
  have e1 := quittingRootContinuePayoff_eq_fixedOpponents reward
    (fun _ : ℕ => repairRoot p hp0 hp1) who (fun _ => (1 : ℝ)) 0
  rw [h0] at e0
  rw [h1] at e1
  simp only [mul_zero, add_zero, mul_one] at e0 e1
  exact ⟨e0.symm, by linarith⟩

/-- Coordinate `false`'s stationary quit value against the repair root. -/
theorem repairQuitValue_false : quittingStationaryFixedOpponentsQuitValue
    reward (repairRoot p hp0 hp1) false = 1 - p := by
  rw [repairQuitValue_eq, false_quitPayoff]; simp

/-- Coordinate `true`'s stationary quit value against the repair root. -/
theorem repairQuitValue_true : quittingStationaryFixedOpponentsQuitValue
    reward (repairRoot p hp0 hp1) true = 2 * p - 1 := by
  rw [repairQuitValue_eq, true_quitPayoff]; simp

/-- Coordinate `false`'s stationary continuation reward and continuation mass
against the repair root. -/
theorem repairContinue_false :
    quittingFixedOpponentsContinueReward reward
        (fun _ : ℕ => repairRoot p hp0 hp1) false 0 = p ∧
      quittingFixedOpponentsContinueMass
        (fun _ : ℕ => repairRoot p hp0 hp1) false 0 = 1 - p := by
  apply repairContinueReward_mass_eq p hp0 hp1 false p (1 - p)
  · rw [false_continuePayoff]; simp
  · rw [false_continuePayoff]; simp

/-- Coordinate `true`'s stationary continuation reward and continuation mass
against the repair root. -/
theorem repairContinue_true :
    quittingFixedOpponentsContinueReward reward
        (fun _ : ℕ => repairRoot p hp0 hp1) true 0 = -p ∧
      quittingFixedOpponentsContinueMass
        (fun _ : ℕ => repairRoot p hp0 hp1) true 0 = 1 - p := by
  apply repairContinueReward_mass_eq p hp0 hp1 true (-p) (1 - p)
  · rw [true_continuePayoff]; simp
  · rw [true_continuePayoff]; simp

/-- Coordinate `false`'s stationary continuation mass: the opponent's
continue probability `1 - p`. -/
theorem repairContinueMass_false :
    quittingStationaryFixedOpponentsContinueMass (repairRoot p hp0 hp1) false = 1 - p :=
  (repairContinue_false p hp0 hp1).2

/-- Coordinate `true`'s stationary continuation mass: the opponent's
continue probability `1 - p`. -/
theorem repairContinueMass_true :
    quittingStationaryFixedOpponentsContinueMass (repairRoot p hp0 hp1) true = 1 - p :=
  (repairContinue_true p hp0 hp1).2

/-- Coordinate `false`'s stationary continuation reward. -/
theorem repairContinueReward_false :
    quittingStationaryFixedOpponentsContinueReward reward (repairRoot p hp0 hp1) false = p :=
  (repairContinue_false p hp0 hp1).1

/-- Coordinate `true`'s stationary continuation reward. -/
theorem repairContinueReward_true :
    quittingStationaryFixedOpponentsContinueReward reward (repairRoot p hp0 hp1) true = -p :=
  (repairContinue_true p hp0 hp1).1

/-! ### `hcontracts`: neither coordinate is isolated -/

/-- Both coordinates' opponents genuinely contract, since the shared hazard `p`
is strictly positive. -/
theorem repairContracts (hppos : 0 < p) (who : Bool) :
    quittingStationaryFixedOpponentsContinueMass (repairRoot p hp0 hp1) who < 1 := by
  cases who
  · rw [repairContinueMass_false]; linarith
  · rw [repairContinueMass_true]; linarith

/-! ### The best-response caps -/

/-- The best-response cap at coordinate `false`: quitting is dominated by never
quitting, which nets exactly `1`, the maximal table entry. -/
theorem repairCap_false (hppos : 0 < p) :
    quittingStationaryUnilateralCap reward (repairRoot p hp0 hp1) false = 1 := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [repairQuitValue_false, repairContinueReward_false, repairContinueMass_false]
  rw [show (1 : ℝ) - (1 - p) = p by ring, div_self hppos.ne']
  exact max_eq_right (by linarith)

/-- The best-response cap at coordinate `true`: quitting immediately, which
nets `2p - 1`, dominates never quitting, which nets exactly `-1`. -/
theorem repairCap_true (hppos : 0 < p) :
    quittingStationaryUnilateralCap reward (repairRoot p hp0 hp1) true = 2 * p - 1 := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [repairQuitValue_true, repairContinueReward_true, repairContinueMass_true]
  rw [show (1 : ℝ) - (1 - p) = p by ring, show (-p : ℝ) / p = -1 by
    rw [div_eq_iff hppos.ne']; ring]
  exact max_eq_left (by linarith)

/-! ### The honest (on-path) payoffs -/

/-- The honest payoff is a fixed point of the one-stage root recursion. -/
theorem repairHonest_fixedPoint (who : Bool) :
    quittingTerminalPayoff reward (quittingStationaryProfile reward (repairRoot p hp0 hp1)) who =
      quittingRootSuccessorPayoff reward
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward (repairRoot p hp0 hp1)) player)
        (repairRoot p hp0 hp1) who := by
  exact quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward
    (repairRoot p hp0 hp1) who

/-- The honest payoff at coordinate `false` satisfies the explicit affine
self-consistency equation of the shared-hazard stationary profile. -/
theorem repairHonest_eq_false :
    quittingTerminalPayoff reward (quittingStationaryProfile reward (repairRoot p hp0 hp1)) false =
      2 * p * (1 - p) + (1 - p) ^ 2 *
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward (repairRoot p hp0 hp1)) false := by
  conv_lhs => rw [repairHonest_fixedPoint p hp0 hp1 false,
    quittingRootSuccessorPayoff_eq_endpointMix, false_quitPayoff, false_continuePayoff]
  simp only [repairRoot_true_toReal, repairRoot_false_toReal]
  ring

/-- The honest payoff at coordinate `true` satisfies the explicit affine
self-consistency equation of the shared-hazard stationary profile. -/
theorem repairHonest_eq_true :
    quittingTerminalPayoff reward (quittingStationaryProfile reward (repairRoot p hp0 hp1)) true =
      p * (3 * p - 2) + (1 - p) ^ 2 *
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward (repairRoot p hp0 hp1)) true := by
  conv_lhs => rw [repairHonest_fixedPoint p hp0 hp1 true,
    quittingRootSuccessorPayoff_eq_endpointMix, true_quitPayoff, true_continuePayoff]
  simp only [repairRoot_true_toReal, repairRoot_false_toReal]
  ring

/-- The honest payoff at coordinate `false` is within `p` of the ceiling `1`. -/
theorem repairHonest_false_ge (hppos : 0 < p) :
    1 - p ≤ quittingTerminalPayoff reward
      (quittingStationaryProfile reward (repairRoot p hp0 hp1)) false := by
  have heq := repairHonest_eq_false p hp0 hp1
  nlinarith [heq, mul_nonneg (mul_nonneg hp0 hp0) (by linarith : (0:ℝ) ≤ 1 - p),
    mul_pos hppos (show (0:ℝ) < 2 - p by linarith)]

/-- The honest payoff at coordinate `true` is at least `-1`, the floor of the
reward table. -/
theorem repairHonest_true_ge (hppos : 0 < p) :
    (-1 : ℝ) ≤ quittingTerminalPayoff reward
      (quittingStationaryProfile reward (repairRoot p hp0 hp1)) true := by
  have heq := repairHonest_eq_true p hp0 hp1
  nlinarith [heq, sq_nonneg p, mul_pos hppos (show (0:ℝ) < 2 - p by linarith)]

end Repair

/-! ## The repair: an ε-equilibrium for every positive `ε` -/

/-- **The repair.**  For every `ε > 0` the shared-hazard stationary profile at
`p = min (ε / 2) 1` is an `ε`-asymptotic-Nash equilibrium of the counterexample
weight: both deviation gains (`p` at coordinate `false`, at most `2p` at
coordinate `true`) are within `ε`. -/
theorem repair_isεAsymptoticNash :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε profile := by
  intro ε hε
  set p : ℝ := min (ε / 2) 1 with hp_def
  have hp0 : 0 ≤ p := le_min (by linarith) (by norm_num)
  have hp1 : p ≤ 1 := min_le_right _ _
  have hppos : 0 < p := lt_min (by linarith) (by norm_num)
  have hpε : p ≤ ε / 2 := min_le_left _ _
  refine ⟨quittingStationaryProfile reward (repairRoot p hp0 hp1), ?_⟩
  apply isεAsymptoticNash_stationary_of_unilateralCap_le
  · exact repairContracts p hp0 hp1 hppos
  · intro who
    cases who
    · rw [repairCap_false p hp0 hp1 hppos]
      have h := repairHonest_false_ge p hp0 hp1 hppos
      linarith
    · rw [repairCap_true p hp0 hp1 hppos]
      have h := repairHonest_true_ge p hp0 hp1 hppos
      linarith

/-- **HEADLINE.**  The counterexample weight has a uniform equilibrium payoff,
despite lying in the isolated-negative branch, which carries no general
sufficiency theorem.  The branch is not vacuous as a producer on this weight:
the shared-hazard stationary profiles of `repair_isεAsymptoticNash`, as
`p → 0`, certify it directly. -/
theorem exists_uniformEquilibriumPayoff_reward :
    ∃ payoff : Payoff Bool, (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors reward
    repair_isεAsymptoticNash

end QuittingDisjunctionCounterexample

end GameTheory
