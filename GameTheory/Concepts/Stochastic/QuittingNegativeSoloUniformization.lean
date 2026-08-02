/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCutoffDeviation
import GameTheory.Concepts.Stochastic.QuittingFirstBranch
import GameTheory.Concepts.Stochastic.TerminalToUniformDeviationApproximation

/-!
# Uniformization with negative solo-quitting reward

When player `who` has a negative reward at its singleton terminal state, an
arbitrary long deviation is compared with the deviation that agrees up to a
cutoff and then always continues.  New singleton absorption can only reduce
the original deviation's payoff, while the cutoff deviation creates no new
singleton absorption.  On both sides, all remaining error is controlled by
the opponents' live tail.

This is the cutoff half of the Solan--Vieille terminal-to-uniform argument.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- If solo absorption is nonpositive, the increase in expected stage payoff
between two times is bounded by the increase in non-solo absorption mass. -/
theorem expectedStagePayoff_sub_le_nonSoloMass_sub_of_solo_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) {earlier later : ℕ} (hlater : earlier ≤ later)
    (bound : ℝ)
    (hreward : ∀ S, |reward S who| ≤ bound)
    (hsolo : reward (quittingSingletonTerminal who) who ≤ 0) :
    (quittingGame reward).expectedStagePayoff profile none later who -
        (quittingGame reward).expectedStagePayoff profile none earlier who ≤
      bound * (quittingNonSoloMass reward profile who later -
        quittingNonSoloMass reward profile who earlier) := by
  classical
  have hsum :
      (∑ S, (quittingAbsorbedMass reward profile later S -
          quittingAbsorbedMass reward profile earlier S) * reward S who) ≤
        ∑ S, if S = quittingSingletonTerminal who then 0 else
          (quittingAbsorbedMass reward profile later S -
            quittingAbsorbedMass reward profile earlier S) * bound := by
    apply Finset.sum_le_sum
    intro S _
    have hdelta : 0 ≤ quittingAbsorbedMass reward profile later S -
        quittingAbsorbedMass reward profile earlier S :=
      sub_nonneg.mpr
        (quittingAbsorbedMass_monotone reward profile S hlater)
    by_cases hS : S = quittingSingletonTerminal who
    · subst S
      simp only [↓reduceIte]
      exact mul_nonpos_of_nonneg_of_nonpos hdelta hsolo
    · simp only [hS, ↓reduceIte]
      calc
        (quittingAbsorbedMass reward profile later S -
              quittingAbsorbedMass reward profile earlier S) * reward S who ≤
            |(quittingAbsorbedMass reward profile later S -
              quittingAbsorbedMass reward profile earlier S) *
                reward S who| := le_abs_self _
        _ = (quittingAbsorbedMass reward profile later S -
              quittingAbsorbedMass reward profile earlier S) *
            |reward S who| := by
          rw [abs_mul, abs_of_nonneg hdelta]
        _ ≤ (quittingAbsorbedMass reward profile later S -
              quittingAbsorbedMass reward profile earlier S) * bound :=
          mul_le_mul_of_nonneg_left (hreward S) hdelta
  calc
    (quittingGame reward).expectedStagePayoff profile none later who -
        (quittingGame reward).expectedStagePayoff profile none earlier who =
      ∑ S, (quittingAbsorbedMass reward profile later S -
        quittingAbsorbedMass reward profile earlier S) * reward S who := by
      rw [expectedStagePayoff_quittingGame_eq_sum_mass,
        expectedStagePayoff_quittingGame_eq_sum_mass,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ ≤ ∑ S, if S = quittingSingletonTerminal who then 0 else
        (quittingAbsorbedMass reward profile later S -
          quittingAbsorbedMass reward profile earlier S) * bound := hsum
    _ = bound * (quittingNonSoloMass reward profile who later -
        quittingNonSoloMass reward profile who earlier) := by
      rw [quittingNonSoloMass_eq_sum_absorbedMass,
        quittingNonSoloMass_eq_sum_absorbedMass,
        ← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S = quittingSingletonTerminal who
      · simp [hS]
      · simp [hS]
        ring

/-- If singleton absorption has stabilized, terminal payoff differs from the
current expected stage payoff only through the non-solo tail. -/
theorem abs_terminalPayoff_sub_expectedStagePayoff_le_nonSoloTail_of_singleton_stable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) (bound : ℝ)
    (hreward : ∀ S, |reward S who| ≤ bound)
    (hsingleton : quittingAbsorbedMassLimit reward profile
        (quittingSingletonTerminal who) =
      quittingAbsorbedMass reward profile time
        (quittingSingletonTerminal who)) :
    |quittingTerminalPayoff reward profile who -
        (quittingGame reward).expectedStagePayoff profile none time who| ≤
      bound * (quittingNonSoloMassLimit reward profile who -
        quittingNonSoloMass reward profile who time) := by
  classical
  rw [quittingTerminalPayoff_sub_expectedStagePayoff_eq_sum_liveTail]
  calc
    |∑ S, (quittingAbsorbedMassLimit reward profile S -
        quittingAbsorbedMass reward profile time S) * reward S who| ≤
      ∑ S, |(quittingAbsorbedMassLimit reward profile S -
        quittingAbsorbedMass reward profile time S) * reward S who| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun S : {S : Finset ι // S.Nonempty} =>
          (quittingAbsorbedMassLimit reward profile S -
            quittingAbsorbedMass reward profile time S) * reward S who)
        Finset.univ
    _ = ∑ S, if S = quittingSingletonTerminal who then 0 else
        (quittingAbsorbedMassLimit reward profile S -
          quittingAbsorbedMass reward profile time S) * |reward S who| := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S = quittingSingletonTerminal who
      · subst S
        simp [hsingleton]
      · simp only [hS, ↓reduceIte]
        rw [abs_mul, abs_of_nonneg]
        exact sub_nonneg.mpr
          (quittingAbsorbedMass_le_limit reward profile time S)
    _ ≤ ∑ S, if S = quittingSingletonTerminal who then 0 else
        (quittingAbsorbedMassLimit reward profile S -
          quittingAbsorbedMass reward profile time S) * bound := by
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : S = quittingSingletonTerminal who
      · simp [hS]
      · simp only [hS, ↓reduceIte]
        exact mul_le_mul_of_nonneg_left (hreward S)
          (sub_nonneg.mpr
            (quittingAbsorbedMass_le_limit reward profile time S))
    _ = bound * (quittingNonSoloMassLimit reward profile who -
        quittingNonSoloMass reward profile who time) := by
      rw [quittingNonSoloMassLimit_sub_eq_sum_tail, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S = quittingSingletonTerminal who
      · simp [hS]
      · simp [hS]
        ring

/-- After the cutoff, the original negative-solo deviation is bounded above
by its cutoff-stage payoff plus one opponent live-tail error. -/
theorem expectedStagePayoff_update_le_cutoff_add_opponentLiveTail_of_solo_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff later : ℕ) (hlater : cutoff ≤ later)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound)
    (hsolo : reward (quittingSingletonTerminal who) who ≤ 0) :
    (quittingGame reward).expectedStagePayoff
        (Function.update profile who deviation) none later who ≤
      (quittingGame reward).expectedStagePayoff
          (Function.update profile who deviation) none cutoff who +
        bound * (quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile who) cutoff -
          quittingLiveMassLimit reward
            (quittingOpponentOnlyProfile reward profile who)) := by
  let deviationProfile := Function.update profile who deviation
  let opponentProfile := quittingOpponentOnlyProfile reward profile who
  have hpayoff :=
    expectedStagePayoff_sub_le_nonSoloMass_sub_of_solo_nonpos
      reward deviationProfile who hlater bound hreward hsolo
  have hnonSolo := quittingNonSoloMass_update_sub_le_opponentLiveTail
    reward profile who deviation hlater
  have hliveLimit := quittingLiveMassLimit_le reward opponentProfile later
  have htail :
      quittingLiveMass reward opponentProfile cutoff -
          quittingLiveMass reward opponentProfile later ≤
        quittingLiveMass reward opponentProfile cutoff -
          quittingLiveMassLimit reward opponentProfile := by
    linarith
  have hnonSoloLimit :
      quittingNonSoloMass reward deviationProfile who later -
          quittingNonSoloMass reward deviationProfile who cutoff ≤
        quittingLiveMass reward opponentProfile cutoff -
          quittingLiveMassLimit reward opponentProfile :=
    le_trans hnonSolo htail
  have hscaled := mul_le_mul_of_nonneg_left hnonSoloLimit hbound
  dsimp [deviationProfile, opponentProfile] at hpayoff hscaled ⊢
  linarith

/-- The cutoff deviation's terminal payoff is bounded below by the common
cutoff-stage payoff minus one opponent live-tail error. -/
theorem expectedStagePayoff_update_le_cutoffTerminal_add_opponentLiveTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff : ℕ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound) :
    (quittingGame reward).expectedStagePayoff
        (Function.update profile who deviation) none cutoff who ≤
      quittingTerminalPayoff reward
          (Function.update profile who
            (quittingContinueAfterStrategy reward who deviation cutoff)) who +
        bound * (quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile who) cutoff -
          quittingLiveMassLimit reward
            (quittingOpponentOnlyProfile reward profile who)) := by
  let cutoffProfile := Function.update profile who
    (quittingContinueAfterStrategy reward who deviation cutoff)
  let opponentProfile := quittingOpponentOnlyProfile reward profile who
  have hstageEq :=
    expectedStagePayoff_update_continueAfter_eq_of_le
      reward profile who deviation cutoff cutoff le_rfl
  have hsingleton :=
    quittingAbsorbedMassLimit_singleton_update_continueAfter_eq_cutoff
      reward profile who deviation cutoff
  have habs :=
    abs_terminalPayoff_sub_expectedStagePayoff_le_nonSoloTail_of_singleton_stable
      reward cutoffProfile who cutoff bound hreward hsingleton
  have htail :=
    quittingNonSoloMassLimit_update_sub_le_opponentLiveTail
      reward profile who
        (quittingContinueAfterStrategy reward who deviation cutoff) cutoff
  have hscaled := mul_le_mul_of_nonneg_left htail hbound
  have habove := neg_le_abs
    (quittingTerminalPayoff reward cutoffProfile who -
      (quittingGame reward).expectedStagePayoff
        cutoffProfile none cutoff who)
  dsimp [cutoffProfile, opponentProfile] at hstageEq habs hscaled habove ⊢
  linarith

/-- For every stage after the cutoff, the source deviation is bounded above
by the cutoff deviation's terminal payoff plus two opponent-tail errors. -/
theorem expectedStagePayoff_update_le_cutoffTerminal_add_two_opponentLiveTail_of_solo_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (cutoff later : ℕ) (hlater : cutoff ≤ later)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound)
    (hsolo : reward (quittingSingletonTerminal who) who ≤ 0) :
    (quittingGame reward).expectedStagePayoff
        (Function.update profile who deviation) none later who ≤
      quittingTerminalPayoff reward
          (Function.update profile who
            (quittingContinueAfterStrategy reward who deviation cutoff)) who +
        2 * bound * (quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile who) cutoff -
          quittingLiveMassLimit reward
            (quittingOpponentOnlyProfile reward profile who)) := by
  have hsource :=
    expectedStagePayoff_update_le_cutoff_add_opponentLiveTail_of_solo_nonpos
      reward profile who deviation cutoff later hlater bound hbound
        hreward hsolo
  have htarget :=
    expectedStagePayoff_update_le_cutoffTerminal_add_opponentLiveTail
      reward profile who deviation cutoff bound hbound hreward
  linarith

end GameTheory
