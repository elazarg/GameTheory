/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingInfinitePureTimeExtremality
import GameTheory.Concepts.Stochastic.QuittingBellmanTelescope

/-!
# Behavioral pure quit-time extremality

Before absorption a quitting game has only one public history.  This module
first proves that every behavior profile has the same terminal payoff as the
history-independent root sequence obtained by reading its actions along that
live history.  It then applies infinite pure quit-time extremality to arbitrary
unilateral behavior deviations.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Canonical live-path root sequence -/

/-- Repeatedly shift a profile past one all-continue live stage. -/
def quittingAllContinueProfileSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ℕ → (quittingGame reward).BehaviorProfile
  | 0 => profile
  | time + 1 => quittingProfileAllContinueContinuation reward
      (quittingAllContinueProfileSpine reward profile time)

/-- The root law seen at each node of the iterated all-continue spine. -/
def quittingProfileSpineRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (time : ℕ) : ι → PMF Bool :=
  quittingProfileRoot reward
    (quittingAllContinueProfileSpine reward profile time)

omit [DecidableEq ι] in
/-- Prefixing an all-continue stage to the canonical live history gives the
next canonical live history. -/
theorem consHist_allContinue_quittingLiveHist
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (time : ℕ) :
    (quittingGame reward).consHist
        (none, quittingAllContinueAction)
        (quittingLiveHist reward time) =
      quittingLiveHist reward (time + 1) := by
  apply Prod.ext
  · funext index
    refine Fin.cases ?_ (fun later => ?_) index
    · rfl
    · rfl
  · rfl

omit [DecidableEq ι] in
/-- Evaluating an iterated all-continue shift on its local live history is
the same as evaluating the original profile on the corresponding global live
history. -/
theorem quittingAllContinueProfileSpine_apply_liveHist
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∀ (start : ℕ) (player : ι) (time : ℕ),
      quittingAllContinueProfileSpine reward profile start player time
          (quittingLiveHist reward time) =
        profile player (start + time)
          (quittingLiveHist reward (start + time)) := by
  intro start
  induction start with
  | zero =>
      intro player time
      rw [quittingAllContinueProfileSpine, Nat.zero_add]
  | succ start ih =>
      intro player time
      rw [quittingAllContinueProfileSpine]
      unfold quittingProfileAllContinueContinuation StochasticGame.shiftProfile
      rw [consHist_allContinue_quittingLiveHist]
      rw [ih player (time + 1)]
      have hindex : start + (time + 1) = start + 1 + time := by omega
      rw [hindex]

omit [DecidableEq ι] in
/-- The iterated-spine roots are exactly the direct roots extracted at the
canonical live histories. -/
theorem quittingProfileSpineRoot_eq_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingProfileSpineRoot reward profile =
      quittingProfileLiveRoot reward profile := by
  funext time player
  unfold quittingProfileSpineRoot quittingProfileRoot quittingProfileLiveRoot
  simpa [quittingGame] using
    (quittingAllContinueProfileSpine_apply_liveHist
      reward profile time player 0)

/-- The finite root recursion along the all-continue spine is the profile's
actual expected payoff at the same finite horizon. -/
theorem quittingFiniteRootPayoff_profileSpine_eq_expectedStagePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    ∀ (start fuel : ℕ),
      quittingFiniteRootPayoff reward
          (quittingProfileSpineRoot reward profile) who
          (fun time => quittingProfileSpineRoot reward profile time who)
          start fuel =
        (quittingGame reward).expectedStagePayoff
          (quittingAllContinueProfileSpine reward profile start)
          none fuel who := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      rw [quittingFiniteRootPayoff]
      unfold StochasticGame.expectedStagePayoff
      rw [(quittingGame reward).histDist_zero, expect_pure,
        stageEUAt_quittingGame_eq_stateReward]
      rfl
  | succ fuel ih =>
      rw [quittingFiniteRootPayoff,
        expectedStagePayoff_succ_quittingGame_eq_rootContinuation]
      rw [Function.update_eq_self]
      unfold quittingRootExpectedPayoff quittingProfileSpineRoot
        quittingProfileRoot
      change
        expect (pmfPi ((fun player =>
            quittingAllContinueProfileSpine reward profile start player 0
              ((quittingGame reward).emptyHist none))))
            (fun action => quittingRootPayoff reward
              (fun _ => quittingFiniteRootPayoff reward
                (quittingProfileSpineRoot reward profile) who
                (fun time => quittingProfileSpineRoot reward profile time who)
                (start + 1) fuel)
              action who) =
          expect (pmfPi ((fun player =>
            quittingAllContinueProfileSpine reward profile start player 0
              ((quittingGame reward).emptyHist none))))
            (fun action =>
              if h : (quittingQuitters action).Nonempty then
                reward ⟨quittingQuitters action, h⟩ who
              else
                (quittingGame reward).expectedStagePayoff
                  ((quittingGame reward).shiftProfile
                    (quittingAllContinueProfileSpine reward profile start)
                    (none, action)) none fuel who)
      apply congrArg (expect (pmfPi (fun player =>
        quittingAllContinueProfileSpine reward profile start player 0
          ((quittingGame reward).emptyHist none))))
      funext action
      by_cases hquit : (quittingQuitters action).Nonempty
      · simp [quittingRootPayoff, hquit]
      · have haction :=
          eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty
            action hquit
        subst action
        simp only [quittingRootPayoff, hquit, ↓reduceDIte]
        rw [show (quittingGame reward).shiftProfile
            (quittingAllContinueProfileSpine reward profile start)
            (none, quittingAllContinueAction) =
          quittingAllContinueProfileSpine reward profile (start + 1) by
            rw [quittingAllContinueProfileSpine]
            rfl]
        exact ih (start + 1)

/-- Every behavior profile has the same terminal payoff as the
history-independent root sequence read from its canonical live history. -/
theorem quittingTerminalPayoff_eq_rootSequence_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward profile who =
      quittingRootSequenceTerminalValue reward
        (quittingProfileLiveRoot reward profile) who 0 := by
  have hfinite :=
    quittingFiniteRootPayoff_profileSpine_eq_expectedStagePayoff
      reward profile who
  have hleft := tendsto_expectedStagePayoff_quittingGame reward profile who
  have hright := tendsto_quittingFiniteRootPayoff_self_terminalValue
    reward (quittingProfileSpineRoot reward profile) who 0
  have heq : quittingTerminalPayoff reward profile who =
      quittingRootSequenceTerminalValue reward
        (quittingProfileSpineRoot reward profile) who 0 := by
    apply tendsto_nhds_unique hleft
    simpa only [hfinite, quittingAllContinueProfileSpine] using hright
  simpa only [quittingProfileSpineRoot_eq_profileLiveRoot] using heq

/-! ## Unilateral deviations on the live path -/

/-- The hazard induced by a behavior strategy on the unique live public
history. -/
def quittingBehaviorLiveHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who : ι} (deviation : (quittingGame reward).BehaviorStrategy who)
    (time : ℕ) : PMF Bool :=
  deviation time (quittingLiveHist reward time)

/-- Updating one behavior strategy updates exactly that coordinate of every
canonical live root. -/
theorem quittingProfileLiveRoot_update_eq_rootSequenceUpdate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingProfileLiveRoot reward (Function.update profile who deviation) =
      quittingRootSequenceUpdate (quittingProfileLiveRoot reward profile)
        who (quittingBehaviorLiveHazard reward deviation) := by
  funext time player
  unfold quittingProfileLiveRoot quittingRootSequenceUpdate
    quittingBehaviorLiveHazard
  by_cases hp : player = who
  · subst player
    simp
  · simp [Function.update_of_ne hp]

/-- Every unilateral behavioral deviation has exactly the terminal payoff of
its induced live-path hazard against the original opponents' live roots. -/
theorem quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward (Function.update profile who deviation) who =
      quittingRootSequenceHazardTerminalValue reward
        (quittingProfileLiveRoot reward profile) who
        (quittingBehaviorLiveHazard reward deviation) 0 := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
  rfl

end GameTheory
