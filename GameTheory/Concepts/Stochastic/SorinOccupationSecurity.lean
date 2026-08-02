/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.SorinAbsorbingGame
import GameTheory.Concepts.Stochastic.FiniteHorizonProfileLawTransfer
import GameTheory.Concepts.Stochastic.PublicFixedPrefixAccounting
import GameTheory.Concepts.Stochastic.PublicTerminalChildLawTransfer

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

/-! ## Deterministic live-history splice -/

/-- Follow the prescribed player-2 strategy before time `prefixLength`.  From
that time onward, switch to `playerTwoSecurityStrategy` exactly on the public
history cones whose length-`prefixLength` base is still live.  On cones already
absorbed at the splice time, keep following the prescribed strategy.

The test is made on the recovered fixed prefix, not on the current state.  This
is what makes the deviation a single behavioral strategy and ensures that a
live base selects the security strategy forever on its entire suffix cone. -/
def playerTwoSecurityAfterLiveDeviation
    (prescribed : game.BehaviorProfile) (prefixLength : ℕ) :
    game.BehaviorStrategy true :=
  fun time history =>
    if htime : prefixLength ≤ time then
      if (game.terminalPrefixLE htime history).2 = State.live then
        playerTwoSecurityCoin
      else
        prescribed true time history
    else
      prescribed true time history

theorem playerTwoSecurityAfterLiveDeviation_before
    (prescribed : game.BehaviorProfile) (prefixLength : ℕ)
    {time : ℕ} (htime : time < prefixLength) (history : game.Hist time) :
    playerTwoSecurityAfterLiveDeviation prescribed prefixLength time history =
      prescribed true time history := by
  simp [playerTwoSecurityAfterLiveDeviation, Nat.not_le_of_lt htime]

theorem playerTwoSecurityAfterLiveDeviation_appendHist_of_live
    (prescribed : game.BehaviorProfile) (prefixLength : ℕ)
    (base : game.Hist prefixLength) (hbase : base.2 = State.live)
    {suffixLength : ℕ} (suffix : game.Hist suffixLength)
    (hstart : suffix.StartsAt base.2) :
    playerTwoSecurityAfterLiveDeviation prescribed prefixLength
        (prefixLength + suffixLength) (game.appendHist base suffix) =
      playerTwoSecurityCoin := by
  unfold playerTwoSecurityAfterLiveDeviation
  simp only [dif_pos (Nat.le_add_right prefixLength suffixLength)]
  rw [game.terminalPrefixLE_appendHist base suffix hstart]
  simp [hbase]

theorem playerTwoSecurityAfterLiveDeviation_appendHist_of_not_live
    (prescribed : game.BehaviorProfile) (prefixLength : ℕ)
    (base : game.Hist prefixLength) (hbase : base.2 ≠ State.live)
    {suffixLength : ℕ} (suffix : game.Hist suffixLength)
    (hstart : suffix.StartsAt base.2) :
    playerTwoSecurityAfterLiveDeviation prescribed prefixLength
        (prefixLength + suffixLength) (game.appendHist base suffix) =
      prescribed true (prefixLength + suffixLength)
        (game.appendHist base suffix) := by
  unfold playerTwoSecurityAfterLiveDeviation
  simp only [dif_pos (Nat.le_add_right prefixLength suffixLength)]
  rw [game.terminalPrefixLE_appendHist base suffix hstart]
  simp [hbase]

/-- The unilateral spliced profile and the prescribed profile agree at every
history strictly before the splice time. -/
theorem profilesAgreeBefore_playerTwoSecurityAfterLive
    (prescribed : game.BehaviorProfile) (prefixLength : ℕ) :
    game.ProfilesAgreeBefore
      (Function.update prescribed true
        (playerTwoSecurityAfterLiveDeviation prescribed prefixLength))
      prescribed prefixLength := by
  intro who time history htime
  cases who
  · simp
  · simp [playerTwoSecurityAfterLiveDeviation_before prescribed
      prefixLength htime history]

/-- In particular, switching at deterministic time `prefixLength` leaves the
law of the public prefix through that time exactly unchanged. -/
theorem histDist_playerTwoSecurityAfterLive_at_prefix
    (prescribed : game.BehaviorProfile) (initial : State)
    (prefixLength : ℕ) :
    game.histDist
        (Function.update prescribed true
          (playerTwoSecurityAfterLiveDeviation prescribed prefixLength))
        initial prefixLength =
      game.histDist prescribed initial prefixLength :=
  game.histDist_eq_of_profilesAgreeBefore
    (profilesAgreeBefore_playerTwoSecurityAfterLive prescribed prefixLength)
    prefixLength (le_refl prefixLength)

/-- After a live terminal prefix, the rebased unilateral splice agrees on all
genuine suffix histories with player 2's stationary security profile against
the prescribed rebased player-1 continuation. -/
theorem profilesAgreeOnStartsAt_playerTwoSecurityAfterLive_of_live
    (prescribed : game.BehaviorProfile) (prefixLength : ℕ)
    (base : game.Hist prefixLength) (hbase : base.2 = State.live) :
    game.ProfilesAgreeOnStartsAt
      (game.afterHistoryProfile
        (Function.update prescribed true
          (playerTwoSecurityAfterLiveDeviation prescribed prefixLength))
        base)
      (profilePlayerTwoSecurity
        ((game.afterHistoryProfile prescribed base) false))
      base.2 := by
  intro who suffixLength suffix hstart
  cases who
  · simp [profilePlayerTwoSecurity]
  · change
      playerTwoSecurityAfterLiveDeviation prescribed prefixLength
          (prefixLength + suffixLength) (game.appendHist base suffix) =
        playerTwoSecurityCoin
    exact playerTwoSecurityAfterLiveDeviation_appendHist_of_live
      prescribed prefixLength base hbase suffix hstart

/-- After a terminal prefix which is already absorbed, the splice agrees on
all genuine suffix histories with the prescribed rebased profile. -/
theorem profilesAgreeOnStartsAt_playerTwoSecurityAfterLive_of_not_live
    (prescribed : game.BehaviorProfile) (prefixLength : ℕ)
    (base : game.Hist prefixLength) (hbase : base.2 ≠ State.live) :
    game.ProfilesAgreeOnStartsAt
      (game.afterHistoryProfile
        (Function.update prescribed true
          (playerTwoSecurityAfterLiveDeviation prescribed prefixLength))
        base)
      (game.afterHistoryProfile prescribed base)
      base.2 := by
  intro who suffixLength suffix hstart
  cases who
  · simp
  · change
      playerTwoSecurityAfterLiveDeviation prescribed prefixLength
          (prefixLength + suffixLength) (game.appendHist base suffix) =
        prescribed true (prefixLength + suffixLength)
          (game.appendHist base suffix)
    exact playerTwoSecurityAfterLiveDeviation_appendHist_of_not_live
      prescribed prefixLength base hbase suffix hstart

/-- Conditional on a live prefix, every suffix-stage payoff of the spliced
player 2 is exactly `2 / 3`. -/
theorem expectedStagePayoff_after_playerTwoSecurityAfterLive_of_live
    (prescribed : game.BehaviorProfile) (prefixLength : ℕ)
    (base : game.Hist prefixLength) (hbase : base.2 = State.live)
    (suffixLength : ℕ) :
    game.expectedStagePayoff
        (game.afterHistoryProfile
          (Function.update prescribed true
            (playerTwoSecurityAfterLiveDeviation prescribed prefixLength))
          base)
        base.2 suffixLength true = 2 / 3 := by
  rw [game.expectedStagePayoff_eq_of_profilesAgreeOnStartsAt
    (profilesAgreeOnStartsAt_playerTwoSecurityAfterLive_of_live
      prescribed prefixLength base hbase)]
  simpa [hbase] using expectedStagePayoff_playerTwoSecurity
    ((game.afterHistoryProfile prescribed base) false) suffixLength

/-- Conditional on an already absorbed prefix, every suffix-stage payoff is
unchanged by the splice. -/
theorem expectedStagePayoff_after_playerTwoSecurityAfterLive_of_not_live
    (prescribed : game.BehaviorProfile) (prefixLength : ℕ)
    (base : game.Hist prefixLength) (hbase : base.2 ≠ State.live)
    (suffixLength : ℕ) :
    game.expectedStagePayoff
        (game.afterHistoryProfile
          (Function.update prescribed true
            (playerTwoSecurityAfterLiveDeviation prescribed prefixLength))
          base)
        base.2 suffixLength true =
      game.expectedStagePayoff (game.afterHistoryProfile prescribed base)
        base.2 suffixLength true :=
  game.expectedStagePayoff_eq_of_profilesAgreeOnStartsAt
    (profilesAgreeOnStartsAt_playerTwoSecurityAfterLive_of_not_live
      prescribed prefixLength base hbase)
    suffixLength true

/-- Stage-payoff disintegration at a deterministic prefix, specialized here
to the Sorin game to avoid making the occupation worker depend on the larger
fixed-depth adaptive-splice API. -/
theorem expectedStagePayoff_add_eq_expect_afterHistory_for_sorinSplice
    (profile : game.BehaviorProfile) (initial : State)
    (prefixLength suffixLength : ℕ) (who : Player) :
    game.expectedStagePayoff profile initial
        (prefixLength + suffixLength) who =
      expect (game.histDist profile initial prefixLength) fun base =>
        game.expectedStagePayoff (game.afterHistoryProfile profile base)
          base.2 suffixLength who := by
  unfold StochasticGame.expectedStagePayoff
  rw [game.histDist_add_eq_bind_histDistAfter, expect_bind]
  apply congrArg (expect (game.histDist profile initial prefixLength))
  funext base
  unfold StochasticGame.histDistAfter
  rw [expect_map]
  rfl

/-- Exact one-stage gain formula after the splice.  Only live prefixes
contribute: there the spliced continuation pays `2 / 3`, while absorbed
prefixes are left unchanged. -/
theorem expectedStagePayoff_playerTwoSecurityAfterLive_sub
    (prescribed : game.BehaviorProfile) (initial : State)
    (prefixLength suffixLength : ℕ) :
    game.expectedStagePayoff
        (Function.update prescribed true
          (playerTwoSecurityAfterLiveDeviation prescribed prefixLength))
        initial (prefixLength + suffixLength) true -
      game.expectedStagePayoff prescribed initial
        (prefixLength + suffixLength) true =
      expect (game.histDist prescribed initial prefixLength) fun base =>
        if base.2 = State.live then
          2 / 3 -
            game.expectedStagePayoff
              (game.afterHistoryProfile prescribed base)
              base.2 suffixLength true
        else
          0 := by
  rw [expectedStagePayoff_add_eq_expect_afterHistory_for_sorinSplice,
    expectedStagePayoff_add_eq_expect_afterHistory_for_sorinSplice,
    histDist_playerTwoSecurityAfterLive_at_prefix]
  rw [← expect_sub]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro base _
  by_cases hbase : base.2 = State.live
  · rw [expectedStagePayoff_after_playerTwoSecurityAfterLive_of_live
      prescribed prefixLength base hbase]
    simp [hbase]
  · rw [expectedStagePayoff_after_playerTwoSecurityAfterLive_of_not_live
      prescribed prefixLength base hbase]
    simp [hbase]

/-- Profiles agreeing before a deterministic time have equal expected stage
payoffs at every strictly earlier time. -/
theorem expectedStagePayoff_eq_of_profilesAgreeBefore_for_sorinSplice
    {left right : game.BehaviorProfile} {initial : State}
    {prefixLength time : ℕ}
    (hagree : game.ProfilesAgreeBefore left right prefixLength)
    (htime : time < prefixLength) (who : Player) :
    game.expectedStagePayoff left initial time who =
      game.expectedStagePayoff right initial time who := by
  unfold StochasticGame.expectedStagePayoff
  rw [game.histDist_eq_of_profilesAgreeBefore hagree time htime.le]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro history _
  unfold StochasticGame.stageEUAt
  rw [game.stageActionDist_eq_of_profilesAgreeBefore hagree history htime]

/-- **Exact deterministic live-history splice identity.**  At horizon
`prefixLength + suffixLength`, the splice changes no prefix payoff.  Its whole
finite-average gain is the normalized sum of the conditional live-prefix
security gains over the suffix.  No equilibrium, payoff-delivery, or
reachability hypothesis is used. -/
theorem finiteAveragePayoff_playerTwoSecurityAfterLive_sub
    (prescribed : game.BehaviorProfile) (initial : State)
    (prefixLength suffixLength : ℕ) :
    game.finiteAveragePayoff initial (prefixLength + suffixLength)
        (Function.update prescribed true
          (playerTwoSecurityAfterLiveDeviation prescribed prefixLength))
        true -
      game.finiteAveragePayoff initial (prefixLength + suffixLength)
        prescribed true =
      ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
        ∑ time ∈ Finset.range suffixLength,
          expect (game.histDist prescribed initial prefixLength) fun base =>
            if base.2 = State.live then
              2 / 3 -
                game.expectedStagePayoff
                  (game.afterHistoryProfile prescribed base)
                  base.2 time true
            else
              0 := by
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff,
    game.finiteAveragePayoff_eq_sum_expectedStagePayoff,
    Finset.sum_range_add, Finset.sum_range_add]
  have hprefix :
      (∑ time ∈ Finset.range prefixLength,
          game.expectedStagePayoff
            (Function.update prescribed true
              (playerTwoSecurityAfterLiveDeviation prescribed prefixLength))
            initial time true) =
        ∑ time ∈ Finset.range prefixLength,
          game.expectedStagePayoff prescribed initial time true := by
    apply Finset.sum_congr rfl
    intro time htime
    exact expectedStagePayoff_eq_of_profilesAgreeBefore_for_sorinSplice
      (profilesAgreeBefore_playerTwoSecurityAfterLive prescribed prefixLength)
      (Finset.mem_range.mp htime) true
  rw [hprefix]
  calc
    ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
          ((∑ time ∈ Finset.range prefixLength,
              game.expectedStagePayoff prescribed initial time true) +
            ∑ time ∈ Finset.range suffixLength,
              game.expectedStagePayoff
                (Function.update prescribed true
                  (playerTwoSecurityAfterLiveDeviation prescribed prefixLength))
                initial (prefixLength + time) true) -
        ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
          ((∑ time ∈ Finset.range prefixLength,
              game.expectedStagePayoff prescribed initial time true) +
            ∑ time ∈ Finset.range suffixLength,
              game.expectedStagePayoff prescribed initial
                (prefixLength + time) true) =
      ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
        ((∑ time ∈ Finset.range suffixLength,
            game.expectedStagePayoff
              (Function.update prescribed true
                (playerTwoSecurityAfterLiveDeviation prescribed prefixLength))
              initial (prefixLength + time) true) -
          ∑ time ∈ Finset.range suffixLength,
            game.expectedStagePayoff prescribed initial
              (prefixLength + time) true) := by ring
    _ = ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
        ∑ time ∈ Finset.range suffixLength,
          (game.expectedStagePayoff
              (Function.update prescribed true
                (playerTwoSecurityAfterLiveDeviation prescribed prefixLength))
              initial (prefixLength + time) true -
            game.expectedStagePayoff prescribed initial
              (prefixLength + time) true) := by
          rw [Finset.sum_sub_distrib]
    _ = ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
        ∑ time ∈ Finset.range suffixLength,
          expect (game.histDist prescribed initial prefixLength) fun base =>
            if base.2 = State.live then
              2 / 3 -
                game.expectedStagePayoff
                  (game.afterHistoryProfile prescribed base)
                  base.2 time true
            else
              0 := by
          congr 1
          apply Finset.sum_congr rfl
          intro time _
          exact expectedStagePayoff_playerTwoSecurityAfterLive_sub
            prescribed initial prefixLength time

end SorinAbsorbingGame
end StochasticGame
end GameTheory
