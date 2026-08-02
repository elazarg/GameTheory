/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.SorinAbsorbingGame

/-!
# Security strategies for Sorin's absorbing game

This file isolates the two unilateral-security ingredients used by Sorin's
stopping argument.  The first one, proved below, is elementary but strategically
important: player 2 can secure `2 / 3` at every positive finite horizon by
playing `Left` with probability `1 / 3` at every history.  The proof is against
an arbitrary history-dependent behavioral strategy of player 1.

The exact finite-horizon identity is stronger than the asymptotic guarantee
needed by the occupation-separation argument.  It is stated separately so that
the later deterministic live-history splice can consume it without importing
any target-payoff or equilibrium hypotheses.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace StochasticGame
namespace SorinAbsorbingGame

open Math.Probability Math.PMFProduct

/-! ## Player 2's exact stationary security strategy -/

/-- Player 2's security action: play `Left` with probability `1 / 3`. -/
def playerTwoSecurityCoin : PMF Bool :=
  BigMatch.coinPMF (1 / 3) (by norm_num) (by norm_num)

@[simp] theorem playerTwoSecurityCoin_true_toReal :
    (playerTwoSecurityCoin true).toReal = 1 / 3 :=
  BigMatch.coinPMF_apply_true_toReal _ _ _

@[simp] theorem playerTwoSecurityCoin_false_toReal :
    (playerTwoSecurityCoin false).toReal = 2 / 3 := by
  rw [playerTwoSecurityCoin, BigMatch.coinPMF_apply_false_toReal]
  norm_num

/-- The stationary behavioral strategy induced by `playerTwoSecurityCoin`. -/
def playerTwoSecurityStrategy : game.BehaviorStrategy true :=
  fun _ _ => playerTwoSecurityCoin

/-- An arbitrary player-1 strategy paired with player 2's security strategy. -/
def profilePlayerTwoSecurity
    (dev : game.BehaviorStrategy false) : game.BehaviorProfile :=
  fun who t h => if who then playerTwoSecurityStrategy t h else dev t h

@[simp] theorem profilePlayerTwoSecurity_false
    (dev : game.BehaviorStrategy false) :
    profilePlayerTwoSecurity dev false = dev := rfl

@[simp] theorem profilePlayerTwoSecurity_true
    (dev : game.BehaviorStrategy false) :
    profilePlayerTwoSecurity dev true = playerTwoSecurityStrategy := rfl

/-- Player 2's harmonic security value on the three states. -/
def playerTwoSecurityValue : State → ℝ
  | .live => 2 / 3
  | .absTL => 2
  | .absTR => 0

@[simp] theorem playerTwoSecurityValue_live :
    playerTwoSecurityValue .live = 2 / 3 := rfl

@[simp] theorem playerTwoSecurityValue_absTL :
    playerTwoSecurityValue .absTL = 2 := rfl

@[simp] theorem playerTwoSecurityValue_absTR :
    playerTwoSecurityValue .absTR = 0 := rfl

/-- Cellwise calculation: once player 2 mixes `Left` with probability `1 / 3`,
their expected current payoff is the security value of the current state,
independently of player 1's mixed action. -/
theorem expect_stagePayoff_playerTwoSecurity
    (s : State) (mu : PMF Bool) :
    expect (pmfPi (fun who => if who then playerTwoSecurityCoin else mu))
        (fun a => game.stagePayoff s a true) =
      playerTwoSecurityValue s := by
  rw [BigMatch.expect_pmfPi_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [expect_eq_sum, Fintype.sum_bool, BigMatch.pmfBool_false_toReal]
  cases s <;>
    simp [BigMatch.expect_coinPMF, playerTwoSecurityCoin, payoff,
      playerTwoSecurityValue, pair] <;>
    ring

/-- The same mix makes the security-value process harmonic. -/
theorem expect_next_playerTwoSecurityValue
    (s : State) (mu : PMF Bool) :
    expect (pmfPi (fun who => if who then playerTwoSecurityCoin else mu))
        (fun a => expect (game.transition s a) playerTwoSecurityValue) =
      playerTwoSecurityValue s := by
  rw [BigMatch.expect_pmfPi_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [expect_eq_sum, Fintype.sum_bool, BigMatch.pmfBool_false_toReal]
  cases s <;>
    simp [BigMatch.expect_coinPMF, playerTwoSecurityCoin, nextState,
      playerTwoSecurityValue] <;>
    ring

/-- At every finite history, player 2's security strategy gives exactly the
harmonic security value as the next-stage expected payoff. -/
theorem stageEUAt_playerTwoSecurity
    (dev : game.BehaviorStrategy false) {t : ℕ} (h : game.Hist t) :
    game.stageEUAt (profilePlayerTwoSecurity dev) h true =
      playerTwoSecurityValue h.2 := by
  unfold StochasticGame.stageEUAt
  change expect
      (pmfPi (fun who => if who then playerTwoSecurityCoin else dev t h))
      (fun a => game.stagePayoff h.2 a true) = playerTwoSecurityValue h.2
  exact expect_stagePayoff_playerTwoSecurity h.2 (dev t h)

/-- At every finite history, the expected successor security value equals the
current security value. -/
theorem oneStep_playerTwoSecurityValue
    (dev : game.BehaviorStrategy false) {t : ℕ} (h : game.Hist t) :
    expect (game.stageActionDist (profilePlayerTwoSecurity dev) h)
        (fun a => expect (game.transition h.2 a) playerTwoSecurityValue) =
      playerTwoSecurityValue h.2 := by
  change expect
      (pmfPi (fun who => if who then playerTwoSecurityCoin else dev t h))
      (fun a => expect (game.transition h.2 a) playerTwoSecurityValue) =
    playerTwoSecurityValue h.2
  exact expect_next_playerTwoSecurityValue h.2 (dev t h)

/-- Starting live, player 2's expected security value remains exactly `2 / 3`
at every time, against every behavioral player-1 strategy. -/
theorem expectedStateValue_playerTwoSecurity
    (dev : game.BehaviorStrategy false) (t : ℕ) :
    game.expectedStateValue (profilePlayerTwoSecurity dev) .live t
        playerTwoSecurityValue = 2 / 3 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [game.expectedStateValue_succ]
      rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ _
        (fun h _ => oneStep_playerTwoSecurityValue dev h)]
      exact ih

/-- Every stage payoff of player 2 is exactly `2 / 3` in expectation under the
security strategy. -/
theorem expectedStagePayoff_playerTwoSecurity
    (dev : game.BehaviorStrategy false) (t : ℕ) :
    game.expectedStagePayoff (profilePlayerTwoSecurity dev) .live t true =
      2 / 3 := by
  unfold StochasticGame.expectedStagePayoff
  rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ _
    (fun h _ => stageEUAt_playerTwoSecurity dev h)]
  exact expectedStateValue_playerTwoSecurity dev t

/-- Player 2 secures exactly `2 / 3` at every positive finite horizon. -/
theorem finiteAveragePayoff_playerTwoSecurity
    (dev : game.BehaviorStrategy false) {T : ℕ} (hT : 0 < T) :
    game.finiteAveragePayoff .live T (profilePlayerTwoSecurity dev) true =
      2 / 3 := by
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  rw [Finset.sum_congr rfl
      (fun t _ => expectedStagePayoff_playerTwoSecurity dev t),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  field_simp

/-- Overriding player 2's component of any profile by the stationary security
strategy recovers `profilePlayerTwoSecurity` applied to that profile's player-1
component. -/
theorem update_true_playerTwoSecurityStrategy (opp : game.BehaviorProfile) :
    Function.update opp true playerTwoSecurityStrategy =
      profilePlayerTwoSecurity (opp false) := by
  funext who t h
  cases who
  · simp [profilePlayerTwoSecurity]
  · simp [profilePlayerTwoSecurity]

/-- Player 2's exact finite-horizon security identity, repackaged in the
generic one-sided-certificate language. -/
theorem isOneSidedGuaranteeCertificate_playerTwo :
    game.IsOneSidedGuaranteeCertificate .live true (2 / 3) := by
  intro delta hdelta
  refine ⟨playerTwoSecurityStrategy, 2, le_refl 2, fun opp T hT => ?_⟩
  have hTpos : 0 < T := by omega
  rw [update_true_playerTwoSecurityStrategy,
    finiteAveragePayoff_playerTwoSecurity (opp false) hTpos]
  linarith

end SorinAbsorbingGame
end StochasticGame
end GameTheory
