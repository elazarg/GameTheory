/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.SorinOccupationPlayerOneSecurity

/-!
# Survival accounting for Sorin's occupation-separation argument

This module formalizes the finite-probability backbone of Sorin's stopping
proof.  The live-state probability is antitone, converges to its infimum, and
the sum of the two expected stage payoffs is at most `2` minus the next
live-state probability.  These facts avoid constructing an infinite-play
measure: the later stopping estimate can work entirely with finite public
history laws and the real limit of the survival sequence.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Topology

namespace GameTheory
namespace StochasticGame
namespace SorinAbsorbingGame

open Filter Math.Probability

/-! ## Live-state mass -/

/-- Indicator of the unique nonabsorbing state. -/
def liveIndicator : State → ℝ
  | .live => 1
  | .absTL | .absTR => 0

@[simp] theorem liveIndicator_live : liveIndicator .live = 1 := rfl
@[simp] theorem liveIndicator_absTL : liveIndicator .absTL = 0 := rfl
@[simp] theorem liveIndicator_absTR : liveIndicator .absTR = 0 := rfl

theorem liveIndicator_nonneg (state : State) :
    0 ≤ liveIndicator state := by
  cases state <;> norm_num

theorem liveIndicator_le_one (state : State) :
    liveIndicator state ≤ 1 := by
  cases state <;> norm_num

/-- Probability of still being live after `time` completed stages, written as
an expectation under the finite public-history law. -/
def liveProbability (profile : game.BehaviorProfile) (time : ℕ) : ℝ :=
  game.expectedStateValue profile .live time liveIndicator

@[simp] theorem liveProbability_zero (profile : game.BehaviorProfile) :
    liveProbability profile 0 = 1 := by
  simp [liveProbability]

theorem liveProbability_nonneg (profile : game.BehaviorProfile)
    (time : ℕ) :
    0 ≤ liveProbability profile time := by
  unfold liveProbability StochasticGame.expectedStateValue
  exact expect_nonneg _ _ fun history => liveIndicator_nonneg history.2

theorem liveProbability_le_one (profile : game.BehaviorProfile)
    (time : ℕ) :
    liveProbability profile time ≤ 1 := by
  unfold liveProbability StochasticGame.expectedStateValue
  calc
    expect (game.histDist profile .live time)
        (fun history => liveIndicator history.2) ≤
      expect (game.histDist profile .live time) (fun _history => 1) := by
        apply expect_mono
        intro history
        exact liveIndicator_le_one history.2
    _ = 1 := expect_const _ _

/-- The live indicator cannot increase along any one-step transition. -/
theorem expect_transition_liveIndicator_le
    (state : State) (action : game.JointAct) :
    expect (game.transition state action) liveIndicator ≤
      liveIndicator state := by
  cases state <;> cases hrow : action false <;>
    cases hcol : action true <;>
    norm_num [transition, nextState, liveIndicator, hrow, hcol]

/-- Averaging the preceding cellwise fact over a mixed action preserves it. -/
theorem expect_stageAction_transition_liveIndicator_le
    (profile : game.BehaviorProfile) {time : ℕ}
    (history : game.Hist time) :
    expect (game.stageActionDist profile history)
        (fun action =>
          expect (game.transition history.2 action) liveIndicator) ≤
      liveIndicator history.2 := by
  calc
    expect (game.stageActionDist profile history)
        (fun action =>
          expect (game.transition history.2 action) liveIndicator) ≤
      expect (game.stageActionDist profile history)
        (fun _action => liveIndicator history.2) := by
          apply expect_mono
          intro action
          exact expect_transition_liveIndicator_le history.2 action
    _ = liveIndicator history.2 := expect_const _ _

theorem liveProbability_succ_le (profile : game.BehaviorProfile)
    (time : ℕ) :
    liveProbability profile (time + 1) ≤ liveProbability profile time := by
  rw [liveProbability, game.expectedStateValue_succ]
  unfold liveProbability StochasticGame.expectedStateValue
  exact expect_mono _ _ _ fun history =>
    expect_stageAction_transition_liveIndicator_le profile history

/-- Survival is antitone in calendar time. -/
theorem liveProbability_antitone (profile : game.BehaviorProfile) :
    Antitone (liveProbability profile) :=
  antitone_nat_of_succ_le (liveProbability_succ_le profile)

/-- The finite-law replacement for `Pr(M = ∞)`: the infimum of all finite
survival probabilities. -/
def survivalLimit (profile : game.BehaviorProfile) : ℝ :=
  ⨅ time : ℕ, liveProbability profile time

theorem liveProbability_bddBelow (profile : game.BehaviorProfile) :
    BddBelow (Set.range (liveProbability profile)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨time, rfl⟩
  exact liveProbability_nonneg profile time

theorem survivalLimit_nonneg (profile : game.BehaviorProfile) :
    0 ≤ survivalLimit profile := by
  exact le_ciInf fun time => liveProbability_nonneg profile time

theorem survivalLimit_le_liveProbability
    (profile : game.BehaviorProfile) (time : ℕ) :
    survivalLimit profile ≤ liveProbability profile time := by
  exact ciInf_le (liveProbability_bddBelow profile) time

/-- The antitone survival sequence converges to `survivalLimit`. -/
theorem tendsto_liveProbability_survivalLimit
    (profile : game.BehaviorProfile) :
    Tendsto (liveProbability profile) atTop
      (nhds (survivalLimit profile)) := by
  apply tendsto_atTop_ciInf (liveProbability_antitone profile)
  exact liveProbability_bddBelow profile

/-! ## Exact payoff/survival identity -/

/-- Cellwise, the sum of the two current payoffs is at most `2` minus the
expected live indicator of the successor state.  The inequality is strict at
the `Top, Right`/`absTR` outcome, whose total payoff is `1`. -/
theorem stagePayoff_sum_le_two_sub_nextLive
    (state : State) (action : game.JointAct) :
    game.stagePayoff state action false +
        game.stagePayoff state action true ≤
      2 - expect (game.transition state action) liveIndicator := by
  cases state <;> cases hrow : action false <;>
    cases hcol : action true <;>
    norm_num [payoff, pair, transition, nextState, liveIndicator, hrow, hcol]

/-- Historywise mixed-action form of the cellwise bound. -/
theorem stageEUAt_sum_le_two_sub_nextLive
    (profile : game.BehaviorProfile) {time : ℕ}
    (history : game.Hist time) :
    game.stageEUAt profile history false +
        game.stageEUAt profile history true ≤
      2 - expect (game.stageActionDist profile history)
        (fun action =>
          expect (game.transition history.2 action) liveIndicator) := by
  unfold StochasticGame.stageEUAt
  rw [← expect_add]
  calc
    expect (game.stageActionDist profile history)
        (fun action =>
          game.stagePayoff history.2 action false +
            game.stagePayoff history.2 action true) ≤
      expect (game.stageActionDist profile history)
        (fun action =>
          2 - expect (game.transition history.2 action) liveIndicator) := by
            apply expect_mono
            intro action
            exact stagePayoff_sum_le_two_sub_nextLive history.2 action
    _ = 2 - expect (game.stageActionDist profile history)
        (fun action =>
          expect (game.transition history.2 action) liveIndicator) := by
            rw [expect_sub, expect_const]

/-- **Expected stage survival bound.**  At stage `time`, the two expected
payoffs sum to at most `2 - r_(time+1)`. -/
theorem expectedStagePayoff_sum_le_two_sub_liveProbability_succ
    (profile : game.BehaviorProfile) (time : ℕ) :
    game.expectedStagePayoff profile .live time false +
        game.expectedStagePayoff profile .live time true ≤
      2 - liveProbability profile (time + 1) := by
  unfold StochasticGame.expectedStagePayoff
  rw [← expect_add]
  calc
    expect (game.histDist profile .live time)
        (fun history =>
          game.stageEUAt profile history false +
            game.stageEUAt profile history true) ≤
      expect (game.histDist profile .live time)
        (fun history =>
          2 - expect (game.stageActionDist profile history)
            (fun action =>
              expect (game.transition history.2 action) liveIndicator)) := by
                apply expect_mono
                intro history
                exact stageEUAt_sum_le_two_sub_nextLive profile history
    _ = 2 - expect (game.histDist profile .live time)
        (fun history =>
          expect (game.stageActionDist profile history)
            (fun action =>
              expect (game.transition history.2 action) liveIndicator)) := by
                rw [expect_sub, expect_const]
    _ = 2 - liveProbability profile (time + 1) := by
      rw [liveProbability, game.expectedStateValue_succ]

end SorinAbsorbingGame
end StochasticGame
end GameTheory
