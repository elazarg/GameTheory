/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingNonSoloTail
import GameTheory.Concepts.Stochastic.FiniteHorizonProfileLawTransfer

/-!
# Cutoff deviations in quitting games

A cutoff deviation follows an arbitrary behavior deviation strictly before a
chosen time and then always continues.  The source and cutoff profiles have
the same law at the cutoff.  Thereafter the deviator cannot create new
singleton absorption, while every absorption involving an opponent is paid
for by the opponent-only live tail.

This is the strategy-level kernel needed for the negative solo-reward half of
the terminal-to-uniform argument.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Follow `deviation` before `cutoff`, then always continue. -/
def quittingContinueAfterStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff : ℕ) : (quittingGame reward).BehaviorStrategy who :=
  fun time history =>
    if time < cutoff then deviation time history else PMF.pure false

/-- Updating by a deviation and updating by its cutoff version agree at all
public histories strictly before the cutoff. -/
theorem profilesAgreeBefore_update_quittingContinueAfterStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff : ℕ) :
    (quittingGame reward).ProfilesAgreeBefore
      (Function.update profile who deviation)
      (Function.update profile who
        (quittingContinueAfterStrategy reward who deviation cutoff))
      cutoff := by
  intro player time history htime
  by_cases hp : player = who
  · subst player
    simp [quittingContinueAfterStrategy, htime]
  · simp [Function.update_of_ne hp]

/-- The source deviation and its cutoff version induce the same history law
through the cutoff. -/
theorem histDist_update_quittingContinueAfterStrategy_eq_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff time : ℕ) (htime : time ≤ cutoff) :
    (quittingGame reward).histDist
        (Function.update profile who deviation) none time =
      (quittingGame reward).histDist
        (Function.update profile who
          (quittingContinueAfterStrategy reward who deviation cutoff))
        none time :=
  (quittingGame reward).histDist_eq_of_profilesAgreeBefore
    (profilesAgreeBefore_update_quittingContinueAfterStrategy
      reward profile who deviation cutoff) time htime

/-- Every expected state observable agrees through the cutoff. -/
theorem expectedStateValue_update_quittingContinueAfterStrategy_eq_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff time : ℕ) (htime : time ≤ cutoff)
    (value : (quittingGame reward).State → ℝ) :
    (quittingGame reward).expectedStateValue
        (Function.update profile who deviation) none time value =
      (quittingGame reward).expectedStateValue
        (Function.update profile who
          (quittingContinueAfterStrategy reward who deviation cutoff))
        none time value := by
  unfold StochasticGame.expectedStateValue
  rw [histDist_update_quittingContinueAfterStrategy_eq_of_le
    reward profile who deviation cutoff time htime]

/-- Live mass agrees through the cutoff. -/
theorem quittingLiveMass_update_continueAfter_eq_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff time : ℕ) (htime : time ≤ cutoff) :
    quittingLiveMass reward (Function.update profile who deviation) time =
    quittingLiveMass reward
        (Function.update profile who
          (quittingContinueAfterStrategy reward who deviation cutoff)) time :=
  by
    rw [quittingLiveMass_eq_expectedStateValue,
      quittingLiveMass_eq_expectedStateValue]
    exact expectedStateValue_update_quittingContinueAfterStrategy_eq_of_le
      reward profile who deviation cutoff time htime
        (quittingLiveIndicator reward)

/-- Non-solo absorption mass agrees through the cutoff. -/
theorem quittingNonSoloMass_update_continueAfter_eq_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff time : ℕ) (htime : time ≤ cutoff) :
    quittingNonSoloMass reward
        (Function.update profile who deviation) who time =
      quittingNonSoloMass reward
        (Function.update profile who
          (quittingContinueAfterStrategy reward who deviation cutoff))
        who time :=
  expectedStateValue_update_quittingContinueAfterStrategy_eq_of_le
    reward profile who deviation cutoff time htime
      (quittingNonSoloIndicator reward who)

/-- Every particular absorbed-state mass agrees through the cutoff. -/
theorem quittingAbsorbedMass_update_continueAfter_eq_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff time : ℕ) (htime : time ≤ cutoff)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMass reward
        (Function.update profile who deviation) time terminal =
      quittingAbsorbedMass reward
        (Function.update profile who
          (quittingContinueAfterStrategy reward who deviation cutoff))
        time terminal :=
  expectedStateValue_update_quittingContinueAfterStrategy_eq_of_le
    reward profile who deviation cutoff time htime
      (quittingAbsorbedIndicator reward terminal)

/-- Expected stage payoff agrees through the cutoff.  In a quitting game the
current-stage reward depends only on the current state, so agreement of the
history law through `time` is enough. -/
theorem expectedStagePayoff_update_continueAfter_eq_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff time : ℕ) (htime : time ≤ cutoff) :
    (quittingGame reward).expectedStagePayoff
        (Function.update profile who deviation) none time who =
      (quittingGame reward).expectedStagePayoff
        (Function.update profile who
          (quittingContinueAfterStrategy reward who deviation cutoff))
        none time who := by
  rw [expectedStagePayoff_quittingGame_eq_sum_mass,
    expectedStagePayoff_quittingGame_eq_sum_mass]
  apply Finset.sum_congr rfl
  intro terminal _
  rw [quittingAbsorbedMass_update_continueAfter_eq_of_le
    reward profile who deviation cutoff time htime terminal]

/-- From the cutoff onward, the cutoff deviation's conditional all-continue
mass is exactly the opponents' all-continue mass. -/
theorem quittingJointContinueMass_update_continueAfter_eq_opponentOnly
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff time : ℕ) (htime : cutoff ≤ time) :
    quittingJointContinueMass reward
        (Function.update profile who
          (quittingContinueAfterStrategy reward who deviation cutoff)) time =
      quittingJointContinueMass reward
        (quittingOpponentOnlyProfile reward profile who) time := by
  unfold quittingJointContinueMass quittingOpponentOnlyProfile
    StochasticGame.stageActionDist
  congr 3
  funext player
  by_cases hp : player = who
  · subst player
    simp [quittingContinueAfterStrategy, quittingAlwaysContinueStrategy,
      Nat.not_lt.mpr htime]
  · simp [Function.update_of_ne hp]

/-- From the cutoff onward, non-solo mass plus live mass is conserved under
the cutoff deviation. -/
theorem quittingNonSoloMass_add_liveMass_update_continueAfter_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff time : ℕ) (htime : cutoff ≤ time) :
    quittingNonSoloMass reward
          (Function.update profile who
            (quittingContinueAfterStrategy reward who deviation cutoff))
          who (time + 1) +
        quittingLiveMass reward
          (Function.update profile who
            (quittingContinueAfterStrategy reward who deviation cutoff))
          (time + 1) =
      quittingNonSoloMass reward
          (Function.update profile who
            (quittingContinueAfterStrategy reward who deviation cutoff))
          who time +
        quittingLiveMass reward
          (Function.update profile who
            (quittingContinueAfterStrategy reward who deviation cutoff))
          time := by
  rw [quittingNonSoloMass_update_succ, quittingLiveMass_succ,
    quittingJointContinueMass_update_continueAfter_eq_opponentOnly
      reward profile who deviation cutoff time htime]
  ring

/-- Conservation of non-solo plus live mass holds at every time after the
cutoff. -/
theorem quittingNonSoloMass_add_liveMass_update_continueAfter_eq_cutoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff later : ℕ) (hlater : cutoff ≤ later) :
    quittingNonSoloMass reward
          (Function.update profile who
            (quittingContinueAfterStrategy reward who deviation cutoff))
          who later +
        quittingLiveMass reward
          (Function.update profile who
            (quittingContinueAfterStrategy reward who deviation cutoff)) later =
      quittingNonSoloMass reward
          (Function.update profile who
            (quittingContinueAfterStrategy reward who deviation cutoff))
          who cutoff +
        quittingLiveMass reward
          (Function.update profile who
            (quittingContinueAfterStrategy reward who deviation cutoff))
          cutoff := by
  induction later, hlater using Nat.le_induction with
  | base => rfl
  | succ time htime ih =>
      rw [quittingNonSoloMass_add_liveMass_update_continueAfter_succ
        reward profile who deviation cutoff time htime, ih]

/-- Live, non-solo, and singleton absorbed mass exhaust probability. -/
theorem quittingLiveMass_add_nonSoloMass_add_singletonMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) :
    quittingLiveMass reward profile time +
        quittingNonSoloMass reward profile who time +
        quittingAbsorbedMass reward profile time
          (quittingSingletonTerminal who) = 1 := by
  classical
  rw [quittingNonSoloMass_eq_sum_absorbedMass]
  have hconservation :=
    quittingLiveMass_add_sum_absorbedMass reward profile time
  have hsplit :
      (∑ S, quittingAbsorbedMass reward profile time S) =
        quittingAbsorbedMass reward profile time
            (quittingSingletonTerminal who) +
          ∑ S, if S = quittingSingletonTerminal who then 0 else
            quittingAbsorbedMass reward profile time S := by
    have hsingle :
        quittingAbsorbedMass reward profile time
            (quittingSingletonTerminal who) =
          ∑ S, if S = quittingSingletonTerminal who then
            quittingAbsorbedMass reward profile time S else 0 := by
      rw [Finset.sum_eq_single (quittingSingletonTerminal who)]
      · simp
      · intro S _ hS
        simp [hS]
      · simp
    rw [hsingle, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hS : S = quittingSingletonTerminal who
    · subst S
      simp
    · simp [hS]
  rw [hsplit] at hconservation
  linarith

/-- A cutoff deviation creates no new singleton absorption after the cutoff. -/
theorem quittingAbsorbedMass_singleton_update_continueAfter_eq_cutoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff later : ℕ) (hlater : cutoff ≤ later) :
    quittingAbsorbedMass reward
        (Function.update profile who
          (quittingContinueAfterStrategy reward who deviation cutoff))
        later (quittingSingletonTerminal who) =
      quittingAbsorbedMass reward
        (Function.update profile who
          (quittingContinueAfterStrategy reward who deviation cutoff))
        cutoff (quittingSingletonTerminal who) := by
  have hlaterConservation := quittingLiveMass_add_nonSoloMass_add_singletonMass
    reward (Function.update profile who
      (quittingContinueAfterStrategy reward who deviation cutoff)) who later
  have hcutoffConservation := quittingLiveMass_add_nonSoloMass_add_singletonMass
    reward (Function.update profile who
      (quittingContinueAfterStrategy reward who deviation cutoff)) who cutoff
  have hcorrected :=
    quittingNonSoloMass_add_liveMass_update_continueAfter_eq_cutoff
      reward profile who deviation cutoff later hlater
  linarith

/-- The limiting singleton absorption mass of a cutoff deviation is already
attained at the cutoff. -/
theorem quittingAbsorbedMassLimit_singleton_update_continueAfter_eq_cutoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff : ℕ) :
    quittingAbsorbedMassLimit reward
        (Function.update profile who
          (quittingContinueAfterStrategy reward who deviation cutoff))
        (quittingSingletonTerminal who) =
      quittingAbsorbedMass reward
        (Function.update profile who
          (quittingContinueAfterStrategy reward who deviation cutoff))
        cutoff (quittingSingletonTerminal who) := by
  let cutoffProfile := Function.update profile who
    (quittingContinueAfterStrategy reward who deviation cutoff)
  apply le_antisymm
  · apply le_of_tendsto'
      (tendsto_quittingAbsorbedMass reward cutoffProfile
        (quittingSingletonTerminal who))
    intro later
    by_cases hlater : cutoff ≤ later
    · exact (quittingAbsorbedMass_singleton_update_continueAfter_eq_cutoff
        reward profile who deviation cutoff later hlater).le
    · exact quittingAbsorbedMass_monotone reward cutoffProfile
        (quittingSingletonTerminal who) (Nat.le_of_not_ge hlater)
  · exact quittingAbsorbedMass_le_limit reward cutoffProfile cutoff
      (quittingSingletonTerminal who)

end GameTheory
