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

/-- If the survival limit is positive, then for every relative tolerance
`eta ∈ (0,1)` some deterministic prefix has conditional survival mass larger
than `1 - eta`: `(1-eta) * r_N < p`.  This is the division-free form used by
the stopping proof. -/
theorem exists_one_sub_mul_liveProbability_lt_survivalLimit
    (profile : game.BehaviorProfile) {eta : ℝ}
    (heta0 : 0 < eta)
    (hlimit : 0 < survivalLimit profile) :
    ∃ prefixLength : ℕ,
      (1 - eta) * liveProbability profile prefixLength <
        survivalLimit profile := by
  have htendsto := tendsto_liveProbability_survivalLimit profile
  obtain ⟨prefixLength, hprefixLength⟩ :=
    (Metric.tendsto_atTop.mp htendsto)
      (eta * survivalLimit profile) (mul_pos heta0 hlimit)
  refine ⟨prefixLength, ?_⟩
  have hdist := hprefixLength prefixLength (le_refl prefixLength)
  rw [Real.dist_eq] at hdist
  have hupper := (abs_lt.mp hdist).2
  have hsurvival0 := liveProbability_nonneg profile prefixLength
  nlinarith [sq_pos_of_pos heta0]

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

/-! ## Prefix-conditioned live tails -/

/-- Arbitrary-initial-state version of the expected stage survival bound. -/
theorem expectedStagePayoff_sum_le_two_sub_expectedStateValue_succ
    (profile : game.BehaviorProfile) (initial : State) (time : ℕ) :
    game.expectedStagePayoff profile initial time false +
        game.expectedStagePayoff profile initial time true ≤
      2 - game.expectedStateValue profile initial (time + 1)
        liveIndicator := by
  unfold StochasticGame.expectedStagePayoff
  rw [← expect_add]
  calc
    expect (game.histDist profile initial time)
        (fun history =>
          game.stageEUAt profile history false +
            game.stageEUAt profile history true) ≤
      expect (game.histDist profile initial time)
        (fun history =>
          2 - expect (game.stageActionDist profile history)
            (fun action =>
              expect (game.transition history.2 action) liveIndicator)) := by
                apply expect_mono
                intro history
                exact stageEUAt_sum_le_two_sub_nextLive profile history
    _ = 2 - expect (game.histDist profile initial time)
        (fun history =>
          expect (game.stageActionDist profile history)
            (fun action =>
              expect (game.transition history.2 action) liveIndicator)) := by
                rw [expect_sub, expect_const]
    _ = 2 - game.expectedStateValue profile initial (time + 1)
        liveIndicator := by
      rw [game.expectedStateValue_succ]

/-- Expected state values disintegrate at a deterministic public prefix. -/
theorem expectedStateValue_add_eq_expect_afterHistory
    (profile : game.BehaviorProfile) (initial : State)
    (prefixLength suffixLength : ℕ) (stateValue : State → ℝ) :
    game.expectedStateValue profile initial (prefixLength + suffixLength)
        stateValue =
      expect (game.histDist profile initial prefixLength) fun base =>
        game.expectedStateValue (game.afterHistoryProfile profile base)
          base.2 suffixLength stateValue := by
  unfold StochasticGame.expectedStateValue
  rw [game.histDist_add_eq_bind_histDistAfter, expect_bind]
  apply congrArg (expect (game.histDist profile initial prefixLength))
  funext base
  unfold StochasticGame.histDistAfter
  rw [expect_map]
  rfl

/-- Starting from either absorbing state, the expected live indicator remains
zero under every behavior profile. -/
theorem expectedStateValue_liveIndicator_eq_zero_of_not_live
    (profile : game.BehaviorProfile) (initial : State)
    (hinitial : initial ≠ State.live) (time : ℕ) :
    game.expectedStateValue profile initial time liveIndicator = 0 := by
  cases initial with
  | live => exact (hinitial rfl).elim
  | absTL =>
      unfold StochasticGame.expectedStateValue
      calc
        expect (game.histDist profile .absTL time)
            (fun history => liveIndicator history.2) =
          expect (game.histDist profile .absTL time) (fun _history => 0) := by
            apply Math.ProbabilityMassFunction.expect_congr_on_support
            intro history hhistory
            have hsnd := game.snd_eq_of_mem_support_histDist_of_isAbsorbingState
              absTL_isAbsorbingState profile time history hhistory
            simp [hsnd, liveIndicator]
        _ = 0 := expect_const _ _
  | absTR =>
      unfold StochasticGame.expectedStateValue
      calc
        expect (game.histDist profile .absTR time)
            (fun history => liveIndicator history.2) =
          expect (game.histDist profile .absTR time) (fun _history => 0) := by
            apply Math.ProbabilityMassFunction.expect_congr_on_support
            intro history hhistory
            have hsnd := game.snd_eq_of_mem_support_histDist_of_isAbsorbingState
              absTR_isAbsorbingState profile time history hhistory
            simp [hsnd, liveIndicator]
        _ = 0 := expect_const _ _

/-- The probability mass of live prefixes is `r_N`. -/
theorem expect_livePrefixIndicator_eq_liveProbability
    (profile : game.BehaviorProfile) (prefixLength : ℕ) :
    expect (game.histDist profile .live prefixLength)
        (fun base => if base.2 = State.live then (1 : ℝ) else 0) =
      liveProbability profile prefixLength := by
  unfold liveProbability StochasticGame.expectedStateValue
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro base _
  cases base.2 <;> simp [liveIndicator]

/-- Averaging suffix live-state mass over precisely the live prefixes recovers
the global later survival probability. -/
theorem expect_livePrefix_expectedStateValue_eq_liveProbability_add
    (profile : game.BehaviorProfile) (prefixLength suffixLength : ℕ) :
    expect (game.histDist profile .live prefixLength)
        (fun base =>
          if base.2 = State.live then
            game.expectedStateValue (game.afterHistoryProfile profile base)
              base.2 suffixLength liveIndicator
          else
            0) =
      liveProbability profile (prefixLength + suffixLength) := by
  rw [liveProbability,
    expectedStateValue_add_eq_expect_afterHistory]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro base _
  by_cases hbase : base.2 = State.live
  · simp [hbase]
  · rw [expectedStateValue_liveIndicator_eq_zero_of_not_live
      (game.afterHistoryProfile profile base) base.2 hbase suffixLength]
    simp [hbase]

/-- Prefix-mass-weighted expected payoff of one tail stage, restricted to
prefixes which are live at the splice time. -/
def liveWeightedStagePayoff (profile : game.BehaviorProfile)
    (prefixLength suffixTime : ℕ) (who : Player) : ℝ :=
  expect (game.histDist profile .live prefixLength) fun base =>
    if base.2 = State.live then
      game.expectedStagePayoff (game.afterHistoryProfile profile base)
        base.2 suffixTime who
    else
      0

/-- The two live-weighted tail-stage payoffs are bounded by twice the prefix
survival mass minus the later survival mass. -/
theorem liveWeightedStagePayoff_sum_le
    (profile : game.BehaviorProfile) (prefixLength suffixTime : ℕ) :
    liveWeightedStagePayoff profile prefixLength suffixTime false +
        liveWeightedStagePayoff profile prefixLength suffixTime true ≤
      2 * liveProbability profile prefixLength -
        liveProbability profile (prefixLength + (suffixTime + 1)) := by
  unfold liveWeightedStagePayoff
  rw [← expect_add]
  calc
    expect (game.histDist profile .live prefixLength)
        (fun base =>
          (if base.2 = State.live then
            game.expectedStagePayoff (game.afterHistoryProfile profile base)
              base.2 suffixTime false
          else 0) +
          if base.2 = State.live then
            game.expectedStagePayoff (game.afterHistoryProfile profile base)
              base.2 suffixTime true
          else 0) ≤
      expect (game.histDist profile .live prefixLength)
        (fun base =>
          if base.2 = State.live then
            2 - game.expectedStateValue
              (game.afterHistoryProfile profile base) base.2
              (suffixTime + 1) liveIndicator
          else 0) := by
            apply expect_mono
            intro base
            by_cases hbase : base.2 = State.live
            · simp only [hbase, ↓reduceIte]
              simpa only [hbase] using
                expectedStagePayoff_sum_le_two_sub_expectedStateValue_succ
                  (game.afterHistoryProfile profile base) base.2 suffixTime
            · simp [hbase]
    _ = 2 * liveProbability profile prefixLength -
        liveProbability profile (prefixLength + (suffixTime + 1)) := by
      have hpoint :
          (fun base : game.Hist prefixLength =>
            if base.2 = State.live then
              2 - game.expectedStateValue
                (game.afterHistoryProfile profile base) base.2
                (suffixTime + 1) liveIndicator
            else 0) =
          (fun base =>
            2 * (if base.2 = State.live then (1 : ℝ) else 0) -
              (if base.2 = State.live then
                game.expectedStateValue
                  (game.afterHistoryProfile profile base) base.2
                  (suffixTime + 1) liveIndicator
              else 0)) := by
        funext base
        by_cases hbase : base.2 = State.live <;> simp [hbase]
      rw [hpoint, expect_sub, expect_const_mul,
        expect_livePrefixIndicator_eq_liveProbability,
        expect_livePrefix_expectedStateValue_eq_liveProbability_add]

/-- Prefix-mass-weighted finite tail average of one player's prescribed
continuation, restricted to prefixes live at the splice time. -/
def liveWeightedTailAverage (profile : game.BehaviorProfile)
    (prefixLength suffixLength : ℕ) (who : Player) : ℝ :=
  (suffixLength : ℝ)⁻¹ *
    ∑ suffixTime ∈ Finset.range suffixLength,
      liveWeightedStagePayoff profile prefixLength suffixTime who

/-- Equivalent conditional-history form of `liveWeightedTailAverage`. -/
theorem liveWeightedTailAverage_eq_expect
    (profile : game.BehaviorProfile) (prefixLength suffixLength : ℕ)
    (who : Player) :
    liveWeightedTailAverage profile prefixLength suffixLength who =
      expect (game.histDist profile .live prefixLength) fun base =>
        if base.2 = State.live then
          game.finiteAveragePayoff base.2 suffixLength
            (game.afterHistoryProfile profile base) who
        else
          0 := by
  unfold liveWeightedTailAverage liveWeightedStagePayoff
  rw [← Fin.sum_univ_eq_sum_range,
    Math.Probability.expect_sum_comm, ← expect_const_mul]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro base _
  by_cases hbase : base.2 = State.live
  · simp only [hbase, ↓reduceIte]
    rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    congr 1
    exact Fin.sum_univ_eq_sum_range
      (fun time : ℕ =>
        game.expectedStagePayoff (game.afterHistoryProfile profile base)
          State.live time who)
      suffixLength
  · simp [hbase]

/-- The sum of the two live-weighted prescribed tail averages is at most
`2 r_N - p`.  This is the unnormalized form of Sorin's conditional-tail
bound `u₁ + u₂ ≤ 2 - p/r_N`. -/
theorem liveWeightedTailAverage_sum_le_two_mul_sub_survivalLimit
    (profile : game.BehaviorProfile) (prefixLength suffixLength : ℕ)
    (hsuffix : 0 < suffixLength) :
    liveWeightedTailAverage profile prefixLength suffixLength false +
        liveWeightedTailAverage profile prefixLength suffixLength true ≤
      2 * liveProbability profile prefixLength - survivalLimit profile := by
  have hterm : ∀ suffixTime ∈ Finset.range suffixLength,
      liveWeightedStagePayoff profile prefixLength suffixTime false +
          liveWeightedStagePayoff profile prefixLength suffixTime true ≤
        2 * liveProbability profile prefixLength - survivalLimit profile := by
    intro suffixTime _
    exact (liveWeightedStagePayoff_sum_le profile prefixLength suffixTime).trans
      (sub_le_sub_left
        (survivalLimit_le_liveProbability profile
          (prefixLength + (suffixTime + 1)))
        (2 * liveProbability profile prefixLength))
  have hsum := Finset.sum_le_sum hterm
  have hsuffixReal : (0 : ℝ) < suffixLength := by exact_mod_cast hsuffix
  unfold liveWeightedTailAverage
  rw [← mul_add, ← Finset.sum_add_distrib] at *
  have hnormalize := mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr hsuffixReal.le)
  calc
    (suffixLength : ℝ)⁻¹ *
        ∑ suffixTime ∈ Finset.range suffixLength,
          (liveWeightedStagePayoff profile prefixLength suffixTime false +
            liveWeightedStagePayoff profile prefixLength suffixTime true) ≤
      (suffixLength : ℝ)⁻¹ *
        ∑ _suffixTime ∈ Finset.range suffixLength,
          (2 * liveProbability profile prefixLength - survivalLimit profile) :=
        hnormalize
    _ = 2 * liveProbability profile prefixLength - survivalLimit profile := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-! ## Security-tail averages and exact root gain -/

/-- Player 1's live-prefix-weighted tail stage payoff after locally resetting
the Blackwell--Ferguson strategy. -/
def playerOneSecurityWeightedStagePayoff (parameter : ℕ)
    (profile : game.BehaviorProfile) (prefixLength suffixTime : ℕ) : ℝ :=
  expect (game.histDist profile .live prefixLength) fun base =>
    if base.2 = State.live then
      game.expectedStagePayoff
        (Function.update (game.afterHistoryProfile profile base) false
          (playerOneSecurityStrategy parameter))
        base.2 suffixTime false
    else
      0

/-- Corresponding live-prefix-weighted finite tail average. -/
def playerOneSecurityWeightedTailAverage (parameter : ℕ)
    (profile : game.BehaviorProfile) (prefixLength suffixLength : ℕ) : ℝ :=
  (suffixLength : ℝ)⁻¹ *
    ∑ suffixTime ∈ Finset.range suffixLength,
      playerOneSecurityWeightedStagePayoff parameter profile prefixLength
        suffixTime

theorem playerOneSecurityWeightedTailAverage_eq_expect
    (parameter : ℕ) (profile : game.BehaviorProfile)
    (prefixLength suffixLength : ℕ) :
    playerOneSecurityWeightedTailAverage parameter profile prefixLength
        suffixLength =
      expect (game.histDist profile .live prefixLength) fun base =>
        if base.2 = State.live then
          game.finiteAveragePayoff base.2 suffixLength
            (Function.update (game.afterHistoryProfile profile base) false
              (playerOneSecurityStrategy parameter))
            false
        else
          0 := by
  unfold playerOneSecurityWeightedTailAverage
    playerOneSecurityWeightedStagePayoff
  rw [← Fin.sum_univ_eq_sum_range,
    Math.Probability.expect_sum_comm, ← expect_const_mul]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro base _
  by_cases hbase : base.2 = State.live
  · simp only [hbase, ↓reduceIte]
    rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    congr 1
    exact Fin.sum_univ_eq_sum_range
      (fun time : ℕ =>
        game.expectedStagePayoff
          (Function.update (game.afterHistoryProfile profile base) false
            (playerOneSecurityStrategy parameter))
          State.live time false)
      suffixLength
  · simp [hbase]

/-- The uniform Blackwell--Ferguson floor survives averaging over all live
prefixes. -/
theorem playerOneSecurityWeightedTailAverage_ge
    (parameter threshold : ℕ) (zeta : ℝ)
    (hsecurity : ∀ (opponent : game.BehaviorProfile) (horizon : ℕ),
      threshold ≤ horizon →
        1 / 2 - zeta ≤
          game.finiteAveragePayoff .live horizon
            (Function.update opponent false
              (playerOneSecurityStrategy parameter)) false)
    (profile : game.BehaviorProfile) (prefixLength suffixLength : ℕ)
    (hsuffix : threshold ≤ suffixLength) :
    (1 / 2 - zeta) * liveProbability profile prefixLength ≤
      playerOneSecurityWeightedTailAverage parameter profile prefixLength
        suffixLength := by
  rw [playerOneSecurityWeightedTailAverage_eq_expect]
  calc
    (1 / 2 - zeta) * liveProbability profile prefixLength =
      expect (game.histDist profile .live prefixLength)
        (fun base =>
          if base.2 = State.live then 1 / 2 - zeta else 0) := by
            rw [show
              (fun base : game.Hist prefixLength =>
                if base.2 = State.live then 1 / 2 - zeta else 0) =
              (fun base =>
                (1 / 2 - zeta) *
                  (if base.2 = State.live then (1 : ℝ) else 0)) by
                    funext base
                    by_cases hbase : base.2 = State.live <;> simp [hbase]]
            rw [expect_const_mul,
              expect_livePrefixIndicator_eq_liveProbability]
    _ ≤ expect (game.histDist profile .live prefixLength)
        (fun base =>
          if base.2 = State.live then
            game.finiteAveragePayoff base.2 suffixLength
              (Function.update (game.afterHistoryProfile profile base) false
                (playerOneSecurityStrategy parameter)) false
          else 0) := by
            apply expect_mono
            intro base
            by_cases hbase : base.2 = State.live
            · simp only [hbase, ↓reduceIte]
              simpa only [hbase] using
                hsecurity (game.afterHistoryProfile profile base)
                  suffixLength hsuffix
            · simp [hbase]

theorem playerOneSecurityWeightedStagePayoff_sub_liveWeightedStagePayoff
    (parameter : ℕ) (profile : game.BehaviorProfile)
    (prefixLength suffixTime : ℕ) :
    expect (game.histDist profile .live prefixLength)
        (fun base =>
          if base.2 = State.live then
            game.expectedStagePayoff
                (Function.update (game.afterHistoryProfile profile base) false
                  (playerOneSecurityStrategy parameter))
                base.2 suffixTime false -
              game.expectedStagePayoff
                (game.afterHistoryProfile profile base)
                base.2 suffixTime false
          else 0) =
      playerOneSecurityWeightedStagePayoff parameter profile prefixLength
          suffixTime -
        liveWeightedStagePayoff profile prefixLength suffixTime false := by
  unfold playerOneSecurityWeightedStagePayoff liveWeightedStagePayoff
  rw [← expect_sub]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro base _
  by_cases hbase : base.2 = State.live <;> simp [hbase]

/-- Exact root payoff gain from the deterministic player-1 live reset,
expressed as tail weight times the live-weighted conditional tail gain. -/
theorem finiteAveragePayoff_playerOneSecurityAfterLive_sub_eq_tailWeight
    (parameter : ℕ) (profile : game.BehaviorProfile)
    (prefixLength suffixLength : ℕ) (hsuffix : 0 < suffixLength) :
    game.finiteAveragePayoff .live (prefixLength + suffixLength)
        (Function.update profile false
          (playerOneSecurityAfterLiveDeviation parameter profile prefixLength))
        false -
      game.finiteAveragePayoff .live (prefixLength + suffixLength)
        profile false =
      ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ * suffixLength *
        (playerOneSecurityWeightedTailAverage parameter profile prefixLength
            suffixLength -
          liveWeightedTailAverage profile prefixLength suffixLength false) := by
  rw [finiteAveragePayoff_playerOneSecurityAfterLive_sub]
  simp_rw [playerOneSecurityWeightedStagePayoff_sub_liveWeightedStagePayoff]
  rw [Finset.sum_sub_distrib]
  unfold playerOneSecurityWeightedTailAverage liveWeightedTailAverage
  have hsuffixNe : (suffixLength : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hsuffix.ne'
  field_simp

theorem playerTwoSecurityStageGain_eq
    (profile : game.BehaviorProfile) (prefixLength suffixTime : ℕ) :
    expect (game.histDist profile .live prefixLength)
        (fun base =>
          if base.2 = State.live then
            2 / 3 -
              game.expectedStagePayoff
                (game.afterHistoryProfile profile base)
                base.2 suffixTime true
          else 0) =
      (2 / 3) * liveProbability profile prefixLength -
        liveWeightedStagePayoff profile prefixLength suffixTime true := by
  unfold liveWeightedStagePayoff
  calc
    expect (game.histDist profile .live prefixLength)
        (fun base =>
          if base.2 = State.live then
            2 / 3 -
              game.expectedStagePayoff
                (game.afterHistoryProfile profile base)
                base.2 suffixTime true
          else 0) =
      expect (game.histDist profile .live prefixLength)
        (fun base =>
          (if base.2 = State.live then 2 / 3 else 0) -
            (if base.2 = State.live then
              game.expectedStagePayoff
                (game.afterHistoryProfile profile base)
                base.2 suffixTime true
            else 0)) := by
            apply Math.ProbabilityMassFunction.expect_congr_on_support
            intro base _
            by_cases hbase : base.2 = State.live <;> simp [hbase]
    _ = expect (game.histDist profile .live prefixLength)
          (fun base => if base.2 = State.live then 2 / 3 else 0) -
        expect (game.histDist profile .live prefixLength)
          (fun base => if base.2 = State.live then
            game.expectedStagePayoff
              (game.afterHistoryProfile profile base)
              base.2 suffixTime true
          else 0) := by
            rw [expect_sub]
    _ = _ := by
      rw [show
        (fun base : game.Hist prefixLength =>
          if base.2 = State.live then (2 / 3 : ℝ) else 0) =
        (fun base =>
          (2 / 3 : ℝ) *
            (if base.2 = State.live then (1 : ℝ) else 0)) by
              funext base
              by_cases hbase : base.2 = State.live <;> simp [hbase],
        expect_const_mul,
        expect_livePrefixIndicator_eq_liveProbability]

/-- Exact root payoff gain from player 2's deterministic live reset. -/
theorem finiteAveragePayoff_playerTwoSecurityAfterLive_sub_eq_tailWeight
    (profile : game.BehaviorProfile)
    (prefixLength suffixLength : ℕ) (hsuffix : 0 < suffixLength) :
    game.finiteAveragePayoff .live (prefixLength + suffixLength)
        (Function.update profile true
          (playerTwoSecurityAfterLiveDeviation profile prefixLength)) true -
      game.finiteAveragePayoff .live (prefixLength + suffixLength)
        profile true =
      ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ * suffixLength *
        ((2 / 3) * liveProbability profile prefixLength -
          liveWeightedTailAverage profile prefixLength suffixLength true) := by
  rw [finiteAveragePayoff_playerTwoSecurityAfterLive_sub]
  simp_rw [playerTwoSecurityStageGain_eq]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  unfold liveWeightedTailAverage
  have hsuffixNe : (suffixLength : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hsuffix.ne'
  field_simp

end SorinAbsorbingGame
end StochasticGame
end GameTheory
