/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.SorinOccupationSecurity

/-!
# Transporting player 1's Big-Match security strategy to Sorin's game

For player 1, Sorin's absorbing game is exactly the Big Match after renaming
the absorbing states

```text
BigMatch.live ↔ live,   BigMatch.zero ↔ absTL,   BigMatch.one ↔ absTR.
```

The actions, transition graph, and player-1 payoff are otherwise identical.
This file makes that assertion literal at the finite-history-law level and
transports the already formalized Blackwell--Ferguson uniform `1 / 2`
guarantee.  Nothing here uses a target payoff or an equilibrium hypothesis.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace StochasticGame
namespace SorinAbsorbingGame

open Math.Probability Math.PMFProduct

/-! ## State and history renaming -/

def toBigMatchState : State → BigMatch.State
  | .live => .live
  | .absTL => .zero
  | .absTR => .one

def fromBigMatchState : BigMatch.State → State
  | .live => .live
  | .zero => .absTL
  | .one => .absTR

@[simp] theorem fromBigMatchState_toBigMatchState (state : State) :
    fromBigMatchState (toBigMatchState state) = state := by
  cases state <;> rfl

@[simp] theorem toBigMatchState_fromBigMatchState (state : BigMatch.State) :
    toBigMatchState (fromBigMatchState state) = state := by
  cases state <;> rfl

def toBigMatchHist {length : ℕ}
    (history : game.Hist length) : BigMatch.game.Hist length :=
  (fun index =>
    (toBigMatchState (history.1 index).1, (history.1 index).2),
    toBigMatchState history.2)

def fromBigMatchHist {length : ℕ}
    (history : BigMatch.game.Hist length) : game.Hist length :=
  (fun index =>
    (fromBigMatchState (history.1 index).1, (history.1 index).2),
    fromBigMatchState history.2)

@[simp] theorem fromBigMatchHist_toBigMatchHist {length : ℕ}
    (history : game.Hist length) :
    fromBigMatchHist (toBigMatchHist history) = history := by
  apply Prod.ext
  · funext index
    apply Prod.ext
    · exact fromBigMatchState_toBigMatchState _
    · rfl
  · exact fromBigMatchState_toBigMatchState _

@[simp] theorem toBigMatchHist_fromBigMatchHist {length : ℕ}
    (history : BigMatch.game.Hist length) :
    toBigMatchHist (fromBigMatchHist history) = history := by
  apply Prod.ext
  · funext index
    apply Prod.ext
    · exact toBigMatchState_fromBigMatchState _
    · rfl
  · exact toBigMatchState_fromBigMatchState _

@[simp] theorem toBigMatchHist_empty (state : State) :
    toBigMatchHist (game.emptyHist state) =
      BigMatch.game.emptyHist (toBigMatchState state) := by
  apply Prod.ext
  · funext index
    exact Fin.elim0 index
  · rfl

@[simp] theorem toBigMatchHist_snoc {length : ℕ}
    (history : game.Hist length) (action : game.JointAct) (next : State) :
    toBigMatchHist
        ((Fin.snoc history.1 (history.2, action), next) :
          game.Hist (length + 1)) =
      (Fin.snoc (toBigMatchHist history).1
          (toBigMatchState history.2, action),
        toBigMatchState next) := by
  apply Prod.ext
  · funext index
    refine Fin.lastCases ?_ (fun previous => ?_) index
    · simp [toBigMatchHist]
    · simp [toBigMatchHist]
  · rfl

@[simp] theorem toBigMatchState_nextState
    (state : State) (action : game.JointAct) :
    toBigMatchState (nextState state action) =
      BigMatch.nextState (toBigMatchState state) action := by
  cases state <;> cases hrow : action false <;>
    cases hcol : action true <;>
    simp [nextState, BigMatch.nextState, toBigMatchState, hrow, hcol]

@[simp] theorem map_transition_toBigMatchState
    (state : State) (action : game.JointAct) :
    (game.transition state action).map toBigMatchState =
      BigMatch.game.transition (toBigMatchState state) action := by
  rw [transition_eq, BigMatch.transition_eq_pure, PMF.pure_map]
  simp

@[simp] theorem playerOne_stagePayoff_toBigMatch
    (state : State) (action : game.JointAct) :
    game.stagePayoff state action false =
      BigMatch.game.stagePayoff (toBigMatchState state) action false := by
  cases state <;> cases hrow : action false <;>
    cases hcol : action true <;>
    norm_num [payoff, pair, BigMatch.payoff, BigMatch.reward,
      toBigMatchState, hrow, hcol]

/-! ## Strategy/profile transport -/

def toBigMatchStrategy {who : Player}
    (strategy : game.BehaviorStrategy who) :
    BigMatch.game.BehaviorStrategy who :=
  fun length history => strategy length (fromBigMatchHist history)

def fromBigMatchStrategy {who : Player}
    (strategy : BigMatch.game.BehaviorStrategy who) :
    game.BehaviorStrategy who :=
  fun length history => strategy length (toBigMatchHist history)

def toBigMatchProfile (profile : game.BehaviorProfile) :
    BigMatch.game.BehaviorProfile :=
  fun who length history =>
    profile who length (fromBigMatchHist history)

@[simp] theorem toBigMatchStrategy_toBigMatchHist {who : Player}
    (strategy : game.BehaviorStrategy who) {length : ℕ}
    (history : game.Hist length) :
    toBigMatchStrategy strategy length (toBigMatchHist history) =
      strategy length history := by
  simp [toBigMatchStrategy]

@[simp] theorem fromBigMatchStrategy_fromBigMatchHist {who : Player}
    (strategy : BigMatch.game.BehaviorStrategy who) {length : ℕ}
    (history : BigMatch.game.Hist length) :
    fromBigMatchStrategy strategy length (fromBigMatchHist history) =
      strategy length history := by
  simp [fromBigMatchStrategy]

@[simp] theorem toBigMatchProfile_toBigMatchHist
    (profile : game.BehaviorProfile) (who : Player) {length : ℕ}
    (history : game.Hist length) :
    toBigMatchProfile profile who length (toBigMatchHist history) =
      profile who length history := by
  simp [toBigMatchProfile]

theorem stageActionDist_toBigMatchProfile
    (profile : game.BehaviorProfile) {length : ℕ}
    (history : game.Hist length) :
    BigMatch.game.stageActionDist (toBigMatchProfile profile)
        (toBigMatchHist history) =
      game.stageActionDist profile history := by
  unfold StochasticGame.stageActionDist
  congr 1
  funext who
  exact toBigMatchProfile_toBigMatchHist profile who history

/-- Transporting every finite Sorin history through the state renaming gives
exactly the Big-Match history law of the transported profile. -/
theorem histDist_map_toBigMatchHist
    (profile : game.BehaviorProfile) (initial : State) :
    ∀ length : ℕ,
      (game.histDist profile initial length).map toBigMatchHist =
        BigMatch.game.histDist (toBigMatchProfile profile)
          (toBigMatchState initial) length := by
  intro length
  induction length with
  | zero =>
      simp only [game.histDist_zero, BigMatch.game.histDist_zero,
        PMF.pure_map, toBigMatchHist_empty]
  | succ length ih =>
      rw [game.histDist_succ, PMF.map_bind,
        BigMatch.game.histDist_succ, ← ih, PMF.bind_map]
      apply congrArg (PMF.bind (game.histDist profile initial length))
      funext history
      simp only [Function.comp_apply]
      rw [PMF.map_bind, stageActionDist_toBigMatchProfile]
      apply congrArg (PMF.bind (game.stageActionDist profile history))
      funext action
      rw [show (toBigMatchHist history).2 =
        toBigMatchState history.2 by rfl]
      simp only [transition, BigMatch.transition, PMF.pure_bind]
      rw [PMF.pure_map, toBigMatchHist_snoc,
        toBigMatchState_nextState]

/-- Player 1's accumulated payoff is invariant under the history renaming. -/
theorem totalPayoff_toBigMatchHist {length : ℕ}
    (history : game.Hist length) :
    BigMatch.game.totalPayoff false (toBigMatchHist history) =
      game.totalPayoff false history := by
  unfold StochasticGame.totalPayoff
  apply Finset.sum_congr rfl
  intro index _
  simpa [toBigMatchHist] using
    (playerOne_stagePayoff_toBigMatch
      (history.1 index).1 (history.1 index).2).symm

/-- The entire finite-average payoff of player 1 is preserved by transporting
a Sorin profile to the Big Match. -/
theorem finiteAveragePayoff_toBigMatchProfile
    (profile : game.BehaviorProfile) (initial : State) (horizon : ℕ) :
    game.finiteAveragePayoff initial horizon profile false =
      BigMatch.game.finiteAveragePayoff (toBigMatchState initial) horizon
        (toBigMatchProfile profile) false := by
  unfold StochasticGame.finiteAveragePayoff
  rw [← histDist_map_toBigMatchHist profile initial horizon, expect_map]
  apply congrArg
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro history _
  exact (totalPayoff_toBigMatchHist history).symm

/-! ## The transported Blackwell--Ferguson guarantee -/

/-- The Blackwell--Ferguson strategy read on the state-renamed public
history. -/
def playerOneSecurityStrategy (parameter : ℕ) :
    game.BehaviorStrategy false :=
  fromBigMatchStrategy (BigMatch.blackwellFergusonStrategy parameter)

/-- Transporting an arbitrary Sorin opponent completion paired with the
player-1 security strategy gives exactly the Big Match's `bfDevProfile`. -/
theorem toBigMatchProfile_update_false_playerOneSecurityStrategy
    (parameter : ℕ) (opponent : game.BehaviorProfile) :
    toBigMatchProfile
        (Function.update opponent false
          (playerOneSecurityStrategy parameter)) =
      BigMatch.bfDevProfile parameter
        (toBigMatchStrategy (opponent true)) := by
  funext who length history
  cases who
  · simp [toBigMatchProfile, playerOneSecurityStrategy,
      fromBigMatchStrategy]
  · simp [toBigMatchProfile, toBigMatchStrategy]

/-- Exact payoff transport for a Blackwell--Ferguson player-1 completion. -/
theorem finiteAveragePayoff_update_playerOneSecurityStrategy_eq_bigMatch
    (parameter : ℕ) (opponent : game.BehaviorProfile) (horizon : ℕ) :
    game.finiteAveragePayoff .live horizon
        (Function.update opponent false
          (playerOneSecurityStrategy parameter)) false =
      BigMatch.game.finiteAveragePayoff .live horizon
        (BigMatch.bfDevProfile parameter
          (toBigMatchStrategy (opponent true))) false := by
  rw [finiteAveragePayoff_toBigMatchProfile,
    toBigMatchProfile_update_false_playerOneSecurityStrategy]
  rfl

/-- Quantitative player-1 security, transported from the existing
Blackwell--Ferguson theorem with its full arbitrary-behavior quantifiers. -/
theorem playerOneSecurity_eventually_ge_half
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ parameter threshold : ℕ,
      ∀ (opponent : game.BehaviorProfile) (horizon : ℕ),
        threshold ≤ horizon →
          1 / 2 - epsilon ≤
            game.finiteAveragePayoff .live horizon
              (Function.update opponent false
                (playerOneSecurityStrategy parameter)) false := by
  obtain ⟨parameter, threshold, hsecurity⟩ :=
    BigMatch.bf_dev_eventually_ge_half_via_certificate epsilon hepsilon
  refine ⟨parameter, threshold, fun opponent horizon hhorizon => ?_⟩
  rw [finiteAveragePayoff_update_playerOneSecurityStrategy_eq_bigMatch]
  exact hsecurity (toBigMatchStrategy (opponent true)) horizon hhorizon

/-- Player 1's `1 / 2` security floor in the generic one-sided-certificate
language.  This is the second security input to Sorin's stopping argument. -/
theorem isOneSidedGuaranteeCertificate_playerOne :
    game.IsOneSidedGuaranteeCertificate .live false (1 / 2) := by
  intro delta hdelta
  obtain ⟨parameter, threshold, hsecurity⟩ :=
    playerOneSecurity_eventually_ge_half delta hdelta
  refine ⟨playerOneSecurityStrategy parameter, max threshold 2,
    le_max_right _ _, fun opponent horizon hhorizon => ?_⟩
  exact hsecurity opponent horizon
    (le_trans (le_max_left threshold 2) hhorizon)

/-! ## Deterministic live-history reset of player 1's security strategy -/

/-- Follow the prescribed player-1 strategy before `prefixLength`.  On a
length-`prefixLength` cone which is still live, reset the
Blackwell--Ferguson strategy and feed it only the rebased suffix history.  On
cones already absorbed by the splice time, keep the prescribed strategy. -/
def playerOneSecurityAfterLiveDeviation
    (parameter : ℕ) (prescribed : game.BehaviorProfile)
    (prefixLength : ℕ) : game.BehaviorStrategy false :=
  fun time history =>
    if htime : prefixLength ≤ time then
      let base := game.terminalPrefixLE htime history
      if base.2 = State.live then
        playerOneSecurityStrategy parameter (time - prefixLength)
          (game.terminalSuffixLE htime history)
      else
        prescribed false time history
    else
      prescribed false time history

/-- A packaged-history evaluator used to move the reset strategy across the
dependent equality between a recovered suffix and its displayed suffix. -/
def playerOneSecurityAtPackagedHistory (parameter : ℕ) :
    (Σ length, game.Hist length) → PMF Bool :=
  fun packaged =>
    playerOneSecurityStrategy parameter packaged.1 packaged.2

theorem playerOneSecurityAfterLiveDeviation_before
    (parameter : ℕ) (prescribed : game.BehaviorProfile)
    (prefixLength : ℕ) {time : ℕ} (htime : time < prefixLength)
    (history : game.Hist time) :
    playerOneSecurityAfterLiveDeviation parameter prescribed prefixLength
        time history =
      prescribed false time history := by
  simp [playerOneSecurityAfterLiveDeviation, Nat.not_le_of_lt htime]

theorem playerOneSecurityAfterLiveDeviation_appendHist_of_live
    (parameter : ℕ) (prescribed : game.BehaviorProfile)
    (prefixLength : ℕ) (base : game.Hist prefixLength)
    (hbase : base.2 = State.live) {suffixLength : ℕ}
    (suffix : game.Hist suffixLength) (hstart : suffix.StartsAt base.2) :
    playerOneSecurityAfterLiveDeviation parameter prescribed prefixLength
        (prefixLength + suffixLength) (game.appendHist base suffix) =
      playerOneSecurityStrategy parameter suffixLength suffix := by
  unfold playerOneSecurityAfterLiveDeviation
  simp only [dif_pos (Nat.le_add_right prefixLength suffixLength)]
  rw [game.terminalPrefixLE_appendHist base suffix hstart]
  simp only [hbase, ↓reduceIte]
  let packagedSuffix : Σ length, game.Hist length :=
    ⟨prefixLength + suffixLength - prefixLength,
      game.terminalSuffixLE
        (Nat.le_add_right prefixLength suffixLength)
        (game.appendHist base suffix)⟩
  have packagedSuffix_eq :
      packagedSuffix = ⟨suffixLength, suffix⟩ := by
    apply Sigma.ext (Nat.add_sub_cancel_left prefixLength suffixLength)
    exact game.terminalSuffixLE_appendHist_heq base suffix
  change
    playerOneSecurityAtPackagedHistory parameter packagedSuffix =
      playerOneSecurityAtPackagedHistory parameter ⟨suffixLength, suffix⟩
  exact congrArg (playerOneSecurityAtPackagedHistory parameter)
    packagedSuffix_eq

theorem playerOneSecurityAfterLiveDeviation_appendHist_of_not_live
    (parameter : ℕ) (prescribed : game.BehaviorProfile)
    (prefixLength : ℕ) (base : game.Hist prefixLength)
    (hbase : base.2 ≠ State.live) {suffixLength : ℕ}
    (suffix : game.Hist suffixLength) (hstart : suffix.StartsAt base.2) :
    playerOneSecurityAfterLiveDeviation parameter prescribed prefixLength
        (prefixLength + suffixLength) (game.appendHist base suffix) =
      prescribed false (prefixLength + suffixLength)
        (game.appendHist base suffix) := by
  unfold playerOneSecurityAfterLiveDeviation
  simp only [dif_pos (Nat.le_add_right prefixLength suffixLength)]
  rw [game.terminalPrefixLE_appendHist base suffix hstart]
  simp [hbase]

/-- The reset deviation leaves the complete prefix law unchanged. -/
theorem profilesAgreeBefore_playerOneSecurityAfterLive
    (parameter : ℕ) (prescribed : game.BehaviorProfile)
    (prefixLength : ℕ) :
    game.ProfilesAgreeBefore
      (Function.update prescribed false
        (playerOneSecurityAfterLiveDeviation parameter prescribed
          prefixLength))
      prescribed prefixLength := by
  intro who time history htime
  cases who
  · simp [playerOneSecurityAfterLiveDeviation_before parameter prescribed
      prefixLength htime history]
  · simp

theorem histDist_playerOneSecurityAfterLive_at_prefix
    (parameter : ℕ) (prescribed : game.BehaviorProfile)
    (initial : State) (prefixLength : ℕ) :
    game.histDist
        (Function.update prescribed false
          (playerOneSecurityAfterLiveDeviation parameter prescribed
            prefixLength))
        initial prefixLength =
      game.histDist prescribed initial prefixLength :=
  game.histDist_eq_of_profilesAgreeBefore
    (profilesAgreeBefore_playerOneSecurityAfterLive parameter prescribed
      prefixLength)
    prefixLength (le_refl prefixLength)

/-- On every genuine suffix of a live prefix, the global reset is exactly the
local security completion against the prescribed rebased player-2 strategy. -/
theorem profilesAgreeOnStartsAt_playerOneSecurityAfterLive_of_live
    (parameter : ℕ) (prescribed : game.BehaviorProfile)
    (prefixLength : ℕ) (base : game.Hist prefixLength)
    (hbase : base.2 = State.live) :
    game.ProfilesAgreeOnStartsAt
      (game.afterHistoryProfile
        (Function.update prescribed false
          (playerOneSecurityAfterLiveDeviation parameter prescribed
            prefixLength))
        base)
      (Function.update (game.afterHistoryProfile prescribed base) false
        (playerOneSecurityStrategy parameter))
      base.2 := by
  intro who suffixLength suffix hstart
  cases who
  · change
      playerOneSecurityAfterLiveDeviation parameter prescribed prefixLength
          (prefixLength + suffixLength) (game.appendHist base suffix) =
        playerOneSecurityStrategy parameter suffixLength suffix
    exact playerOneSecurityAfterLiveDeviation_appendHist_of_live
      parameter prescribed prefixLength base hbase suffix hstart
  · simp

/-- On every genuine suffix of an absorbed prefix, the global reset is
identical to the prescribed rebased profile. -/
theorem profilesAgreeOnStartsAt_playerOneSecurityAfterLive_of_not_live
    (parameter : ℕ) (prescribed : game.BehaviorProfile)
    (prefixLength : ℕ) (base : game.Hist prefixLength)
    (hbase : base.2 ≠ State.live) :
    game.ProfilesAgreeOnStartsAt
      (game.afterHistoryProfile
        (Function.update prescribed false
          (playerOneSecurityAfterLiveDeviation parameter prescribed
            prefixLength))
        base)
      (game.afterHistoryProfile prescribed base)
      base.2 := by
  intro who suffixLength suffix hstart
  cases who
  · change
      playerOneSecurityAfterLiveDeviation parameter prescribed prefixLength
          (prefixLength + suffixLength) (game.appendHist base suffix) =
        prescribed false (prefixLength + suffixLength)
          (game.appendHist base suffix)
    exact playerOneSecurityAfterLiveDeviation_appendHist_of_not_live
      parameter prescribed prefixLength base hbase suffix hstart
  · simp

/-- Finite-average payoffs depend only on play at histories genuinely rooted
at the supplied initial state. -/
theorem finiteAveragePayoff_eq_of_profilesAgreeOnStartsAt_for_sorinSecurity
    {left right : game.BehaviorProfile} {initial : State}
    (hagree : game.ProfilesAgreeOnStartsAt left right initial)
    (horizon : ℕ) (who : Player) :
    game.finiteAveragePayoff initial horizon left who =
      game.finiteAveragePayoff initial horizon right who := by
  unfold StochasticGame.finiteAveragePayoff
  rw [game.histDist_eq_of_profilesAgreeOnStartsAt hagree horizon]

/-- On a live prefix, the conditional finite-average payoff of the global
reset is exactly that of the locally reset security completion. -/
theorem finiteAveragePayoff_after_playerOneSecurityAfterLive_of_live
    (parameter : ℕ) (prescribed : game.BehaviorProfile)
    (prefixLength : ℕ) (base : game.Hist prefixLength)
    (hbase : base.2 = State.live) (horizon : ℕ) :
    game.finiteAveragePayoff base.2 horizon
        (game.afterHistoryProfile
          (Function.update prescribed false
            (playerOneSecurityAfterLiveDeviation parameter prescribed
              prefixLength))
          base)
        false =
      game.finiteAveragePayoff base.2 horizon
        (Function.update (game.afterHistoryProfile prescribed base) false
          (playerOneSecurityStrategy parameter))
        false :=
  finiteAveragePayoff_eq_of_profilesAgreeOnStartsAt_for_sorinSecurity
    (profilesAgreeOnStartsAt_playerOneSecurityAfterLive_of_live
      parameter prescribed prefixLength base hbase)
    horizon false

/-- On an absorbed prefix, the conditional finite-average payoff is unchanged
by the global reset. -/
theorem finiteAveragePayoff_after_playerOneSecurityAfterLive_of_not_live
    (parameter : ℕ) (prescribed : game.BehaviorProfile)
    (prefixLength : ℕ) (base : game.Hist prefixLength)
    (hbase : base.2 ≠ State.live) (horizon : ℕ) :
    game.finiteAveragePayoff base.2 horizon
        (game.afterHistoryProfile
          (Function.update prescribed false
            (playerOneSecurityAfterLiveDeviation parameter prescribed
              prefixLength))
          base)
        false =
      game.finiteAveragePayoff base.2 horizon
        (game.afterHistoryProfile prescribed base) false :=
  finiteAveragePayoff_eq_of_profilesAgreeOnStartsAt_for_sorinSecurity
    (profilesAgreeOnStartsAt_playerOneSecurityAfterLive_of_not_live
      parameter prescribed prefixLength base hbase)
    horizon false

/-- A quantitative Blackwell--Ferguson guarantee applies uniformly after
every live prefix because its opponent quantifier ranges over arbitrary
rebased behavior profiles. -/
theorem finiteAveragePayoff_after_playerOneSecurityAfterLive_ge_half
    (parameter threshold : ℕ) (epsilon : ℝ)
    (hsecurity : ∀ (opponent : game.BehaviorProfile) (horizon : ℕ),
      threshold ≤ horizon →
        1 / 2 - epsilon ≤
          game.finiteAveragePayoff .live horizon
            (Function.update opponent false
              (playerOneSecurityStrategy parameter)) false)
    (prescribed : game.BehaviorProfile) (prefixLength : ℕ)
    (base : game.Hist prefixLength) (hbase : base.2 = State.live)
    (horizon : ℕ) (hhorizon : threshold ≤ horizon) :
    1 / 2 - epsilon ≤
      game.finiteAveragePayoff base.2 horizon
        (game.afterHistoryProfile
          (Function.update prescribed false
            (playerOneSecurityAfterLiveDeviation parameter prescribed
              prefixLength))
          base)
        false := by
  rw [finiteAveragePayoff_after_playerOneSecurityAfterLive_of_live
    parameter prescribed prefixLength base hbase]
  simpa [hbase] using
    hsecurity (game.afterHistoryProfile prescribed base) horizon hhorizon

/-- Exact one-stage gain formula for the player-1 reset. -/
theorem expectedStagePayoff_playerOneSecurityAfterLive_sub
    (parameter : ℕ) (prescribed : game.BehaviorProfile)
    (initial : State) (prefixLength suffixLength : ℕ) :
    game.expectedStagePayoff
        (Function.update prescribed false
          (playerOneSecurityAfterLiveDeviation parameter prescribed
            prefixLength))
        initial (prefixLength + suffixLength) false -
      game.expectedStagePayoff prescribed initial
        (prefixLength + suffixLength) false =
      expect (game.histDist prescribed initial prefixLength) fun base =>
        if base.2 = State.live then
          game.expectedStagePayoff
              (Function.update (game.afterHistoryProfile prescribed base)
                false (playerOneSecurityStrategy parameter))
              base.2 suffixLength false -
            game.expectedStagePayoff
              (game.afterHistoryProfile prescribed base)
              base.2 suffixLength false
        else
          0 := by
  rw [expectedStagePayoff_add_eq_expect_afterHistory_for_sorinSplice,
    expectedStagePayoff_add_eq_expect_afterHistory_for_sorinSplice,
    histDist_playerOneSecurityAfterLive_at_prefix]
  rw [← expect_sub]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro base _
  by_cases hbase : base.2 = State.live
  · rw [game.expectedStagePayoff_eq_of_profilesAgreeOnStartsAt
      (profilesAgreeOnStartsAt_playerOneSecurityAfterLive_of_live
        parameter prescribed prefixLength base hbase)]
    simp [hbase]
  · rw [game.expectedStagePayoff_eq_of_profilesAgreeOnStartsAt
      (profilesAgreeOnStartsAt_playerOneSecurityAfterLive_of_not_live
        parameter prescribed prefixLength base hbase)]
    simp [hbase]

/-- Exact whole-horizon gain formula for the player-1 reset.  As for player 2,
all prefix terms cancel and only the live-prefix conditional suffix gains
remain. -/
theorem finiteAveragePayoff_playerOneSecurityAfterLive_sub
    (parameter : ℕ) (prescribed : game.BehaviorProfile)
    (initial : State) (prefixLength suffixLength : ℕ) :
    game.finiteAveragePayoff initial (prefixLength + suffixLength)
        (Function.update prescribed false
          (playerOneSecurityAfterLiveDeviation parameter prescribed
            prefixLength))
        false -
      game.finiteAveragePayoff initial (prefixLength + suffixLength)
        prescribed false =
      ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
        ∑ time ∈ Finset.range suffixLength,
          expect (game.histDist prescribed initial prefixLength) fun base =>
            if base.2 = State.live then
              game.expectedStagePayoff
                  (Function.update (game.afterHistoryProfile prescribed base)
                    false (playerOneSecurityStrategy parameter))
                  base.2 time false -
                game.expectedStagePayoff
                  (game.afterHistoryProfile prescribed base)
                  base.2 time false
            else
              0 := by
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff,
    game.finiteAveragePayoff_eq_sum_expectedStagePayoff,
    Finset.sum_range_add, Finset.sum_range_add]
  have hprefix :
      (∑ time ∈ Finset.range prefixLength,
          game.expectedStagePayoff
            (Function.update prescribed false
              (playerOneSecurityAfterLiveDeviation parameter prescribed
                prefixLength))
            initial time false) =
        ∑ time ∈ Finset.range prefixLength,
          game.expectedStagePayoff prescribed initial time false := by
    apply Finset.sum_congr rfl
    intro time htime
    exact expectedStagePayoff_eq_of_profilesAgreeBefore_for_sorinSplice
      (profilesAgreeBefore_playerOneSecurityAfterLive parameter prescribed
        prefixLength)
      (Finset.mem_range.mp htime) false
  rw [hprefix]
  calc
    ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
          ((∑ time ∈ Finset.range prefixLength,
              game.expectedStagePayoff prescribed initial time false) +
            ∑ time ∈ Finset.range suffixLength,
              game.expectedStagePayoff
                (Function.update prescribed false
                  (playerOneSecurityAfterLiveDeviation parameter prescribed
                    prefixLength))
                initial (prefixLength + time) false) -
        ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
          ((∑ time ∈ Finset.range prefixLength,
              game.expectedStagePayoff prescribed initial time false) +
            ∑ time ∈ Finset.range suffixLength,
              game.expectedStagePayoff prescribed initial
                (prefixLength + time) false) =
      ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
        ((∑ time ∈ Finset.range suffixLength,
            game.expectedStagePayoff
              (Function.update prescribed false
                (playerOneSecurityAfterLiveDeviation parameter prescribed
                  prefixLength))
              initial (prefixLength + time) false) -
          ∑ time ∈ Finset.range suffixLength,
            game.expectedStagePayoff prescribed initial
              (prefixLength + time) false) := by ring
    _ = ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
        ∑ time ∈ Finset.range suffixLength,
          (game.expectedStagePayoff
              (Function.update prescribed false
                (playerOneSecurityAfterLiveDeviation parameter prescribed
                  prefixLength))
              initial (prefixLength + time) false -
            game.expectedStagePayoff prescribed initial
              (prefixLength + time) false) := by
          rw [Finset.sum_sub_distrib]
    _ = ((prefixLength + suffixLength : ℕ) : ℝ)⁻¹ *
        ∑ time ∈ Finset.range suffixLength,
          expect (game.histDist prescribed initial prefixLength) fun base =>
            if base.2 = State.live then
              game.expectedStagePayoff
                  (Function.update (game.afterHistoryProfile prescribed base)
                    false (playerOneSecurityStrategy parameter))
                  base.2 time false -
                game.expectedStagePayoff
                  (game.afterHistoryProfile prescribed base)
                  base.2 time false
            else
              0 := by
          congr 1
          apply Finset.sum_congr rfl
          intro time _
          exact expectedStagePayoff_playerOneSecurityAfterLive_sub
            parameter prescribed initial prefixLength time

end SorinAbsorbingGame
end StochasticGame
end GameTheory
