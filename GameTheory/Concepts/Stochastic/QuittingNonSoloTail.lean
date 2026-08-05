/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingNonSoloMass
import GameTheory.Concepts.Stochastic.QuittingLiveTail

/-!
# Opponent-caused absorption tails in quitting games

Fix a player `who` and a unilateral deviation.  Absorption outside the
singleton terminal state `{who}` can occur only when an opponent quits.  The
mass of those absorptions after a cutoff is therefore bounded by the live
mass that the opponents lose after that cutoff.

The useful invariant is exact and finite-time: non-solo absorbed mass plus
opponent-only live mass is nonincreasing.  Passing to the limit yields the
tail estimate used by cutoff deviations in the terminal-to-uniform bridge.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The non-solo state indicator is the sum of the absorbed-state indicators
away from the singleton terminal state `{who}`. -/
theorem quittingNonSoloIndicator_eq_sum_absorbedIndicator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (state : (quittingGame reward).State) :
    quittingNonSoloIndicator reward who state =
      ∑ S, if S = quittingSingletonTerminal who then 0 else
        quittingAbsorbedIndicator reward S state := by
  classical
  cases state with
  | none =>
      simp [quittingNonSoloIndicator, quittingAbsorbedIndicator, quittingGame]
  | some terminal =>
      by_cases hterminal : terminal = quittingSingletonTerminal who
      · subst terminal
        rw [show quittingNonSoloIndicator reward who
            (some (quittingSingletonTerminal who)) = 0 by
          simp [quittingNonSoloIndicator]]
        symm
        apply Finset.sum_eq_zero
        intro S _
        by_cases hS : S = quittingSingletonTerminal who
        · simp [hS]
        · simp only [hS, ↓reduceIte, quittingAbsorbedIndicator]
          rw [if_neg]
          intro heq
          exact hS (Option.some.inj heq).symm
      · rw [show quittingNonSoloIndicator reward who (some terminal) = 1 by
          simp [quittingNonSoloIndicator, hterminal]]
        rw [Finset.sum_eq_single terminal]
        · simp [quittingAbsorbedIndicator, hterminal]
        · intro S _ hS
          by_cases hsingleton : S = quittingSingletonTerminal who
          · simp [hsingleton]
          · simp only [hsingleton, ↓reduceIte, quittingAbsorbedIndicator]
            rw [if_neg]
            intro heq
            exact hS (Option.some.inj heq).symm
        · simp

/-- Non-solo mass is the sum of the absorbed masses away from `{who}`. -/
theorem quittingNonSoloMass_eq_sum_absorbedMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) :
    quittingNonSoloMass reward profile who time =
      ∑ S, if S = quittingSingletonTerminal who then 0 else
        quittingAbsorbedMass reward profile time S := by
  classical
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  let historyLaw := (quittingGame reward).histDist profile none time
  calc
    quittingNonSoloMass reward profile who time =
        expect historyLaw (fun history =>
          quittingNonSoloIndicator reward who history.2) := by
      rfl
    _ = expect historyLaw (fun history =>
        ∑ S, if S = quittingSingletonTerminal who then 0 else
          quittingAbsorbedIndicator reward S history.2) := by
      congr 1
      funext history
      exact quittingNonSoloIndicator_eq_sum_absorbedIndicator
        reward who history.2
    _ = ∑ S, expect historyLaw (fun history =>
        if S = quittingSingletonTerminal who then 0 else
          quittingAbsorbedIndicator reward S history.2) := by
      symm
      exact expect_sum_comm historyLaw fun S history =>
        if S = quittingSingletonTerminal who then 0 else
          quittingAbsorbedIndicator reward S history.2
    _ = ∑ S, if S = quittingSingletonTerminal who then 0 else
        quittingAbsorbedMass reward profile time S := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S = quittingSingletonTerminal who
      · simp [hS]
      · simp only [hS, ↓reduceIte]
        rfl

/-- Limiting probability of absorption outside the singleton terminal state
`{who}`. -/
def quittingNonSoloMassLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) : ℝ :=
  ∑ S, if S = quittingSingletonTerminal who then 0 else
    quittingAbsorbedMassLimit reward profile S

/-- Non-solo mass converges to the sum of the corresponding terminal
absorption masses. -/
theorem tendsto_quittingNonSoloMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) :
    Tendsto (quittingNonSoloMass reward profile who) atTop
      (nhds (quittingNonSoloMassLimit reward profile who)) := by
  rw [show quittingNonSoloMass reward profile who = fun time =>
      ∑ S, if S = quittingSingletonTerminal who then 0 else
        quittingAbsorbedMass reward profile time S by
      funext time
      exact quittingNonSoloMass_eq_sum_absorbedMass
        reward profile who time]
  unfold quittingNonSoloMassLimit
  apply tendsto_finsetSum Finset.univ
  intro S _
  by_cases hS : S = quittingSingletonTerminal who
  · simp [hS]
  · simp only [hS, ↓reduceIte]
    exact tendsto_quittingAbsorbedMass reward profile S

/-- Non-solo absorbed mass is nondecreasing. -/
theorem quittingNonSoloMass_monotone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) :
    Monotone (quittingNonSoloMass reward profile who) := by
  intro earlier later hlater
  rw [quittingNonSoloMass_eq_sum_absorbedMass,
    quittingNonSoloMass_eq_sum_absorbedMass]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S = quittingSingletonTerminal who
  · simp [hS]
  · simp only [hS, ↓reduceIte]
    exact quittingAbsorbedMass_monotone reward profile S hlater

/-- The limiting non-solo tail is the sum of the future absorption masses
away from the singleton terminal state `{who}`. -/
theorem quittingNonSoloMassLimit_sub_eq_sum_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) :
    quittingNonSoloMassLimit reward profile who -
        quittingNonSoloMass reward profile who time =
      ∑ S, if S = quittingSingletonTerminal who then 0 else
        (quittingAbsorbedMassLimit reward profile S -
          quittingAbsorbedMass reward profile time S) := by
  classical
  unfold quittingNonSoloMassLimit
  rw [quittingNonSoloMass_eq_sum_absorbedMass,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S = quittingSingletonTerminal who
  · simp [hS]
  · simp [hS]

/-- In one stage, the new non-solo absorption mass is no larger than the
opponent-only live mass lost in that stage. -/
theorem quittingNonSoloMass_update_succ_sub_le_opponentLiveDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (time : ℕ) :
    quittingNonSoloMass reward
          (Function.update profile who deviation) who (time + 1) -
        quittingNonSoloMass reward
          (Function.update profile who deviation) who time ≤
      quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) time -
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) (time + 1) := by
  let opponentProfile := quittingOpponentOnlyProfile reward profile who
  let deviationProfile := Function.update profile who deviation
  let continueMass := quittingJointContinueMass reward opponentProfile time
  have hlive : quittingLiveMass reward deviationProfile time ≤
      quittingLiveMass reward opponentProfile time :=
    quittingLiveMass_update_le_opponentOnly
      reward profile who deviation time
  have hfactor : 0 ≤ 1 - continueMass := sub_nonneg.mpr
    (quittingJointContinueMass_le_one reward opponentProfile time)
  have hmul := mul_le_mul_of_nonneg_right hlive hfactor
  rw [quittingNonSoloMass_update_succ, quittingLiveMass_succ]
  dsimp [deviationProfile, opponentProfile, continueMass] at hmul ⊢
  linarith

/-- Non-solo mass plus opponent-only live mass is nonincreasing. -/
theorem quittingNonSoloMass_add_opponentLiveMass_antitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    Antitone (fun time =>
      quittingNonSoloMass reward
          (Function.update profile who deviation) who time +
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) time) := by
  apply antitone_nat_of_succ_le
  intro time
  have hdrop :=
    quittingNonSoloMass_update_succ_sub_le_opponentLiveDrop
      reward profile who deviation time
  linarith

/-- Finite-time tail estimate: non-solo absorption accumulated after a
cutoff is paid for by the opponents' lost live mass. -/
theorem quittingNonSoloMass_update_sub_le_opponentLiveTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    {cutoff later : ℕ} (hlater : cutoff ≤ later) :
    quittingNonSoloMass reward
          (Function.update profile who deviation) who later -
        quittingNonSoloMass reward
          (Function.update profile who deviation) who cutoff ≤
      quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) cutoff -
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) later := by
  have hmono := quittingNonSoloMass_add_opponentLiveMass_antitone
    reward profile who deviation hlater
  linarith

/-- Limiting tail estimate: all future non-solo absorption after a cutoff is
bounded by the opponents' live tail after that cutoff. -/
theorem quittingNonSoloMassLimit_update_sub_le_opponentLiveTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff : ℕ) :
    quittingNonSoloMassLimit reward
          (Function.update profile who deviation) who -
        quittingNonSoloMass reward
          (Function.update profile who deviation) who cutoff ≤
      quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) cutoff -
        quittingLiveMassLimit reward
          (quittingOpponentOnlyProfile reward profile who) := by
  let deviationProfile := Function.update profile who deviation
  let opponentProfile := quittingOpponentOnlyProfile reward profile who
  apply le_of_tendsto_of_tendsto
    ((tendsto_quittingNonSoloMass reward deviationProfile who).sub
      tendsto_const_nhds)
    (tendsto_const_nhds.sub
      (tendsto_quittingLiveMass reward opponentProfile))
  filter_upwards [Filter.eventually_ge_atTop cutoff] with later hlater
  exact quittingNonSoloMass_update_sub_le_opponentLiveTail
    reward profile who deviation hlater

end GameTheory
