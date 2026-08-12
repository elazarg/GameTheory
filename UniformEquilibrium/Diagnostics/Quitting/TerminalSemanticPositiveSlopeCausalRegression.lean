/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeAtom
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawTransferBalanceRegression

/-!
# A causal regression for positive stopping-law slope atoms

The signed terminal rectangle exposed by a positive best-response-envelope
slope is not automatically an insertion toggle of the reset mover.  This
file gives a literal two-player behavioral example.

Player `false` initially Quits surely and receives `-1`; changing its whole
stopping law toward Never consumes its debt.  Player `true` receives zero
whenever `false` quits, but receives `2` by quitting solo.  Along the exact
complete-law mixture of these two policies, the mover loses debt at rate one
while the observer gains debt at rate two.  Total debt therefore has strict
outward slope one.

Nevertheless adding the reset mover to any coalition never raises the
observer's terminal reward: the relevant insertion increments are `0` and
`-2`.  The positive charge is a two-deviation rectangle.  Reorienting it
through the observer's actual Quit-now deviation exposes the positive solo
atom.  Thus a raw positive rectangle needs a recipient-deviation/causal
disintegration step; it cannot be handed directly to the atomic-toggle
compiler under the reset mover's label.
-/

noncomputable section

namespace GameTheory
namespace PositiveSlopeCausalRegression

open StochasticGame
open QuittingSureSetOwnerRepair

/-- Reset mover. -/
abbrev mover : Bool := false

/-- Debt recipient. -/
abbrev observer : Bool := true

/-- The mover dislikes every terminal at which it quits.  The observer is
paid only when it quits alone. -/
def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun terminal player =>
    if player = mover then
      if mover ∈ terminal.val then -1 else 0
    else if terminal.val = {observer} then 2 else 0

theorem abs_reward_le_two
    (terminal : {S : Finset Bool // S.Nonempty}) (player : Bool) :
    |reward terminal player| ≤ 2 := by
  unfold reward
  split_ifs <;> norm_num

/-- Source: only the mover Quits, surely and immediately. -/
def source : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot {mover})

/-- Full reset endpoint: everybody Continues forever. -/
def endpoint : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot ∅)

theorem endpoint_eq_update_source_never :
    endpoint = Function.update source mover
      (quittingAlwaysContinueStrategy reward mover) := by
  funext player time history
  by_cases hplayer : player = mover
  · subst player
    simp [endpoint, source, quittingStationaryProfile,
      StochasticGame.stationaryBehaviorProfile, quittingPureSetRoot,
      quittingSetAction, quittingAlwaysContinueStrategy]
    rfl
  · have htrue : player = observer := by
      cases player <;> simp_all [mover, observer]
    subst player
    simp [endpoint, source, quittingStationaryProfile,
      StochasticGame.stationaryBehaviorProfile, quittingPureSetRoot,
      quittingSetAction, mover, observer]

/-- Exact whole-stopping-law reset ray from sure Quit to Never. -/
def mixed (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  Function.update source mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover (source mover)
      (quittingAlwaysContinueStrategy reward mover) lambda hlambda0 hlambda1)

theorem source_debt_mover :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source) mover = 1 := by
  unfold source
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward {mover} mover
    (by norm_num) abs_reward_le_two]
  norm_num [mover, quittingSetReward, reward]

theorem source_debt_observer :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source) observer = 0 := by
  unfold source
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward {mover} observer
    (by norm_num) abs_reward_le_two]
  norm_num [mover, observer, quittingSetReward, reward, Fin.ext_iff,
    show ({true, false} : Finset Bool) ≠ {true} by decide]

theorem endpoint_debt_mover :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward endpoint) mover = 0 := by
  unfold endpoint
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward ∅ mover
    (by norm_num) abs_reward_le_two]
  norm_num [mover, quittingSetReward, reward]

theorem endpoint_debt_observer :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward endpoint) observer = 2 := by
  unfold endpoint
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward ∅ observer
    (by norm_num) abs_reward_le_two]
  norm_num [observer, mover, quittingSetReward, reward]

/-- The reset mover's debt is exactly `1-lambda`. -/
theorem mixed_debt_mover
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (mixed lambda hlambda0 hlambda1)) mover = 1 - lambda := by
  have haffine := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
    reward source mover (source mover) (quittingAlwaysContinueStrategy reward mover)
      lambda hlambda0 hlambda1
  rw [Function.update_eq_self, ← endpoint_eq_update_source_never,
    source_debt_mover, endpoint_debt_mover] at haffine
  change quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (mixed lambda hlambda0 hlambda1)) mover = _ at haffine
  nlinarith

/-- Prescribed payoff is zero for the observer all along the reset ray. -/
theorem mixed_payoff_observer
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalPayoff reward (mixed lambda hlambda0 hlambda1) observer = 0 := by
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward source mover observer (source mover)
      (quittingAlwaysContinueStrategy reward mover) lambda hlambda0 hlambda1
  rw [Function.update_eq_self, ← endpoint_eq_update_source_never] at haffine
  unfold source endpoint at haffine
  rw [quittingTerminalPayoff_pureSetRoot,
    quittingTerminalPayoff_pureSetRoot] at haffine
  norm_num [mixed, observer, mover, quittingSetReward, reward] at haffine ⊢
  exact haffine

/-- Quitting immediately on the mixed ray pays the observer exactly
`2*lambda`: it is paid only in the Never component of the mover's law. -/
theorem mixed_quitNow_payoff_observer
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    let deviation := quittingPureTimeBehaviorStrategy reward observer (some 0)
    quittingTerminalPayoff reward
        (Function.update (mixed lambda hlambda0 hlambda1) observer deviation)
        observer = 2 * lambda := by
  dsimp only
  let deviation := quittingPureTimeBehaviorStrategy reward observer (some 0)
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update source observer deviation) mover observer
      (source mover) (quittingAlwaysContinueStrategy reward mover)
      lambda hlambda0 hlambda1
  have hsourceCommute :
      Function.update (Function.update source observer deviation) mover
          (source mover) = Function.update source observer deviation := by
    rw [Function.update_comm (by decide : observer ≠ mover)]
    simp
  have hendpointCommute :
      Function.update (Function.update source observer deviation) mover
          (quittingAlwaysContinueStrategy reward mover) =
        Function.update endpoint observer deviation := by
    rw [Function.update_comm (by decide : observer ≠ mover),
      endpoint_eq_update_source_never]
  have hmixedCommute :
      Function.update (Function.update source observer deviation) mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover
            (source mover) (quittingAlwaysContinueStrategy reward mover)
            lambda hlambda0 hlambda1) =
        Function.update (mixed lambda hlambda0 hlambda1) observer deviation := by
    rw [Function.update_comm (by decide : observer ≠ mover)]
    rfl
  rw [hmixedCommute, hsourceCommute, hendpointCommute] at haffine
  dsimp only [deviation] at haffine
  unfold source endpoint at haffine
  rw [quittingTerminalPayoff_update_pureSetRoot_quitNow,
    quittingTerminalPayoff_update_pureSetRoot_quitNow] at haffine
  norm_num [observer, mover, quittingSetReward, reward, Fin.ext_iff,
    show ({true, false} : Finset Bool) ≠ {true} by decide] at haffine ⊢
  linarith

/-- Every observer deviation on the mixed ray is worth at most `2*lambda`.
This is the envelope side of the rectangle: the sure-Quit component pays the
observer zero under every action, while the Never component is bounded by
the solo reward two. -/
theorem mixed_update_observer_payoff_le
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (deviation : (quittingGame reward).BehaviorStrategy observer) :
    quittingTerminalPayoff reward
        (Function.update (mixed lambda hlambda0 hlambda1) observer deviation)
        observer ≤ 2 * lambda := by
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update source observer deviation) mover observer
      (source mover) (quittingAlwaysContinueStrategy reward mover)
      lambda hlambda0 hlambda1
  have hsourceCommute :
      Function.update (Function.update source observer deviation) mover
          (source mover) = Function.update source observer deviation := by
    rw [Function.update_comm (by decide : observer ≠ mover)]
    simp
  have hendpointCommute :
      Function.update (Function.update source observer deviation) mover
          (quittingAlwaysContinueStrategy reward mover) =
        Function.update endpoint observer deviation := by
    rw [Function.update_comm (by decide : observer ≠ mover),
      endpoint_eq_update_source_never]
  have hmixedCommute :
      Function.update (Function.update source observer deviation) mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover
            (source mover) (quittingAlwaysContinueStrategy reward mover)
            lambda hlambda0 hlambda1) =
        Function.update (mixed lambda hlambda0 hlambda1) observer deviation := by
    rw [Function.update_comm (by decide : observer ≠ mover)]
    rfl
  rw [hmixedCommute, hsourceCommute, hendpointCommute] at haffine
  have hsourceUpper := quittingTerminalPayoff_update_pureSetRoot_le
    reward {mover} observer deviation
  have hendpointUpper := quittingTerminalPayoff_update_pureSetRoot_le
    reward ∅ observer deviation
  change quittingTerminalPayoff reward
      (Function.update source observer deviation) observer ≤ _ at hsourceUpper
  change quittingTerminalPayoff reward
      (Function.update endpoint observer deviation) observer ≤ _ at hendpointUpper
  norm_num [observer, mover, quittingSetReward, reward, Fin.ext_iff,
    show ({true, false} : Finset Bool) ≠ {true} by decide]
    at hsourceUpper hendpointUpper
  nlinarith

/-- The observer's full behavioral best-response cap is exactly
`2*lambda`. -/
theorem mixed_cap_observer
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingContinuationBestResponseValue reward
        (mixed lambda hlambda0 hlambda1) observer = 2 * lambda := by
  unfold quittingContinuationBestResponseValue
  apply le_antisymm
  · apply csSup_le
    · exact Set.range_nonempty _
    · rintro payoff ⟨deviation, rfl⟩
      exact mixed_update_observer_payoff_le lambda hlambda0 hlambda1 deviation
  · apply le_csSup
      (bddAbove_range_quittingTerminalPayoff_update reward
        (mixed lambda hlambda0 hlambda1) observer (by norm_num)
          abs_reward_le_two)
    let deviation := quittingPureTimeBehaviorStrategy reward observer (some 0)
    refine ⟨deviation, ?_⟩
    simpa only [deviation] using
      mixed_quitNow_payoff_observer lambda hlambda0 hlambda1

/-- The recipient debt rises exactly at rate two. -/
theorem mixed_debt_observer
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (mixed lambda hlambda0 hlambda1)) observer = 2 * lambda := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change quittingContinuationBestResponseValue reward
      (mixed lambda hlambda0 hlambda1) observer -
    quittingTerminalPayoff reward (mixed lambda hlambda0 hlambda1) observer = _
  rw [mixed_cap_observer lambda hlambda0 hlambda1,
    mixed_payoff_observer lambda hlambda0 hlambda1]
  ring

/-- **Strict positive total-debt slope.**  The mover consumes debt at rate
one, the observer receives debt at rate two, and total debt is `1+lambda`. -/
theorem mixed_totalDebt
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (mixed lambda hlambda0 hlambda1)) = 1 + lambda := by
  unfold quittingTerminalSemanticDebtSum
  rw [Fintype.sum_bool, mixed_debt_mover lambda hlambda0 hlambda1,
    mixed_debt_observer lambda hlambda0 hlambda1]
  ring

/-- Observer-coordinate effect of inserting the reset mover into one
opponent coalition, with the empty coalition evaluated against zero. -/
def resetMoverInsertionEffect (coalition : Finset Bool) : ℝ :=
  quittingStageCoalitionPayoff reward 0 (insert mover coalition) observer -
    quittingStageCoalitionPayoff reward 0 coalition observer

/-- **No positive reset-mover toggle.**  On every valid opponent coalition
of the reset mover, its insertion weakly hurts the debt recipient.  Hence the
positive total slope cannot be labelled as a positive insertion toggle of
the mover. -/
theorem resetMoverInsertionEffect_nonpos
    (coalition : Finset Bool)
    (hcoalition : coalition ∈ (Finset.univ.erase mover).powerset) :
    resetMoverInsertionEffect coalition ≤ 0 := by
  have hsubset : coalition ⊆ {observer} := by
    have herase : (Finset.univ.erase mover : Finset Bool) = {observer} := by
      decide
    rw [herase] at hcoalition
    exact Finset.mem_powerset.mp hcoalition
  by_cases hempty : coalition = ∅
  · subst coalition
    norm_num [resetMoverInsertionEffect, mover, observer,
      quittingStageCoalitionPayoff, reward]
  · have hobserver : observer ∈ coalition := by
      obtain ⟨player, hplayer⟩ :=
        Finset.nonempty_iff_ne_empty.mpr hempty
      have hplayerEq : player = observer := by
        simpa using hsubset hplayer
      simpa [hplayerEq] using hplayer
    have hcoalitionEq : coalition = {observer} := by
      apply Finset.Subset.antisymm hsubset
      simpa using hobserver
    subst coalition
    norm_num [resetMoverInsertionEffect, mover, observer,
      quittingStageCoalitionPayoff, reward, Fin.ext_iff,
      show ({false, true} : Finset Bool) ≠ {true} by decide]

/-- The positive rectangle is recovered by the recipient's own legal solo
deviation: its gain is exactly the full recipient debt `2*lambda`. -/
theorem quitNow_gain_eq_recipientDebt
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    let deviation := quittingPureTimeBehaviorStrategy reward observer (some 0)
    quittingTerminalPayoff reward
          (Function.update (mixed lambda hlambda0 hlambda1) observer deviation)
          observer -
        quittingTerminalPayoff reward (mixed lambda hlambda0 hlambda1) observer =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (mixed lambda hlambda0 hlambda1)) observer := by
  dsimp only
  rw [mixed_quitNow_payoff_observer, mixed_payoff_observer,
    mixed_debt_observer]
  ring

end PositiveSlopeCausalRegression

/-! ## Pure-time sharpening of the positive-slope rectangle -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Pure-time coordinate decoder.**

The cap branch of the positive-slope atom theorem can be witnessed by a
deterministic stopping time, including `Never`.  The conclusion separates
the boundary atom from finite chronological stopping explicitly.

The same pure-time deviation is evaluated at the literal reset endpoint and
source.  Thus the rectangle does not hide an independently selected best
response or terminal law. -/
theorem exists_prescribedAtom_or_pureTimeRectangleAtom_of_stoppingLawDebtSlope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda charge : ℝ) (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (hcharge : 0 < charge)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hslope : lambda * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (profile mover) target lambda hlambda0.le hlambda1))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer) :
    (∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 2 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward profile
            (Function.update profile mover target) observer (some terminal)) ∨
    ((∃ terminal : {S : Finset ι // S.Nonempty},
        charge / 4 ≤
          (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
            quittingTerminalPayoffDifferenceAtom reward
              (Function.update (Function.update profile mover target) observer
                (quittingPureTimeBehaviorStrategy reward observer none))
              (Function.update profile observer
                (quittingPureTimeBehaviorStrategy reward observer none))
              observer (some terminal)) ∨
      ∃ stop : ℕ, ∃ terminal : {S : Finset ι // S.Nonempty},
        charge / 4 ≤
          (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
            quittingTerminalPayoffDifferenceAtom reward
              (Function.update (Function.update profile mover target) observer
                (quittingPureTimeBehaviorStrategy reward observer (some stop)))
              (Function.update profile observer
                (quittingPureTimeBehaviorStrategy reward observer (some stop)))
              observer (some terminal)) := by
  let endpoint := Function.update profile mover target
  let mixed := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover
      (profile mover) target lambda hlambda0.le hlambda1)
  let sourcePair := quittingTerminalSemanticPair reward profile
  let endpointPair := quittingTerminalSemanticPair reward endpoint
  let mixedPair := quittingTerminalSemanticPair reward mixed
  have hchord := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward profile mover observer (profile mover) target lambda hlambda0.le
      hlambda1 hM hreward
  rw [Function.update_eq_self] at hchord
  change quittingTerminalSemanticDebt mixedPair observer ≤
      (1 - lambda) * quittingTerminalSemanticDebt sourcePair observer +
        lambda * quittingTerminalSemanticDebt endpointPair observer at hchord
  have hendpointSlope : charge ≤
      quittingTerminalSemanticDebt endpointPair observer -
        quittingTerminalSemanticDebt sourcePair observer := by
    change lambda * charge ≤
      quittingTerminalSemanticDebt mixedPair observer -
        quittingTerminalSemanticDebt sourcePair observer at hslope
    have hscaled : lambda * charge ≤ lambda *
        (quittingTerminalSemanticDebt endpointPair observer -
          quittingTerminalSemanticDebt sourcePair observer) := by
      nlinarith
    nlinarith
  let sourceCap := quittingContinuationBestResponseValue reward profile observer
  let endpointCap := quittingContinuationBestResponseValue reward endpoint observer
  let sourcePayoff := quittingTerminalPayoff reward profile observer
  let endpointPayoff := quittingTerminalPayoff reward endpoint observer
  have hsplit : charge ≤
      (endpointCap - sourceCap) + (sourcePayoff - endpointPayoff) := by
    dsimp only [sourcePair, endpointPair, quittingTerminalSemanticDebt,
      quittingTerminalSemanticPair] at hendpointSlope
    dsimp only [sourceCap, endpointCap, sourcePayoff, endpointPayoff]
    linarith
  by_cases hpayoff : charge / 2 ≤ sourcePayoff - endpointPayoff
  · exact Or.inl (exists_absorbingTerminalPayoffDifferenceAtom reward profile
      endpoint observer (charge / 2) (by positivity) hpayoff)
  · right
    have hcap : charge / 2 < endpointCap - sourceCap := by
      linarith
    have herror : 0 < charge / 8 := by positivity
    obtain ⟨deviation, hdeviation⟩ :=
      exists_quittingContinuation_deviation_ge_sub reward endpoint observer
        herror hM hreward
    obtain ⟨quitTime, hquitTime⟩ :=
      exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
        reward endpoint observer deviation herror
    let pureDeviation :=
      quittingPureTimeBehaviorStrategy reward observer quitTime
    have hsourceBound :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile observer pureDeviation hM hreward
    have hpureEndpoint : endpointCap - charge / 4 ≤
        quittingTerminalPayoff reward
          (Function.update endpoint observer pureDeviation) observer := by
      dsimp only [pureDeviation]
      linarith
    have hrectangle : charge / 4 ≤
        quittingTerminalPayoff reward
            (Function.update endpoint observer pureDeviation) observer -
          quittingTerminalPayoff reward
            (Function.update profile observer pureDeviation) observer := by
      dsimp only [sourceCap] at hcap hsourceBound
      linarith
    obtain ⟨terminal, hterminal⟩ :=
      exists_absorbingTerminalPayoffDifferenceAtom reward
        (Function.update endpoint observer pureDeviation)
        (Function.update profile observer pureDeviation) observer
        (charge / 4) (by positivity) hrectangle
    cases quitTime with
    | none =>
        exact Or.inl ⟨terminal, by
          simpa only [endpoint, pureDeviation] using hterminal⟩
    | some stop =>
        exact Or.inr ⟨stop, terminal, by
          simpa only [endpoint, pureDeviation] using hterminal⟩

end GameTheory
