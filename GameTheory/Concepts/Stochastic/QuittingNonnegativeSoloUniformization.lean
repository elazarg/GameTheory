/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingNonSoloTail
import GameTheory.Concepts.Stochastic.TerminalToUniformDeviationApproximation

/-!
# Uniformization with nonnegative solo-quitting rewards

For a deviating player whose reward at the singleton terminal state `{who}`
is nonnegative, future singleton absorption cannot make its terminal payoff
smaller than its current expected stage payoff.  Only future absorption that
involves an opponent can hurt.  The non-solo tail estimate bounds that loss by
the opponents' live tail, which tends to zero without requiring the opponents
to absorb almost surely.

This is the positive-sign half of the Solan--Vieille terminal-to-uniform
argument for quitting games.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- With nonnegative solo reward, a deviating stage payoff exceeds its own
terminal payoff by at most the reward bound times the opponents' live tail. -/
theorem expectedStagePayoff_update_le_terminal_add_opponentLiveTail_of_solo_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (time : ℕ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who) :
    (quittingGame reward).expectedStagePayoff
        (Function.update profile who deviation) none time who ≤
      quittingTerminalPayoff reward
          (Function.update profile who deviation) who +
        bound * (quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile who) time -
          quittingLiveMassLimit reward
            (quittingOpponentOnlyProfile reward profile who)) := by
  classical
  let deviationProfile := Function.update profile who deviation
  let opponentProfile := quittingOpponentOnlyProfile reward profile who
  have hidentity :=
    quittingTerminalPayoff_sub_expectedStagePayoff_eq_sum_liveTail
      reward deviationProfile time who
  have hsum :
      (∑ S, -((quittingAbsorbedMassLimit reward deviationProfile S -
          quittingAbsorbedMass reward deviationProfile time S) *
            reward S who)) ≤
        ∑ S, if S = quittingSingletonTerminal who then 0 else
          (quittingAbsorbedMassLimit reward deviationProfile S -
            quittingAbsorbedMass reward deviationProfile time S) * bound := by
    apply Finset.sum_le_sum
    intro S _
    have hdelta : 0 ≤
        quittingAbsorbedMassLimit reward deviationProfile S -
          quittingAbsorbedMass reward deviationProfile time S :=
      sub_nonneg.mpr
        (quittingAbsorbedMass_le_limit reward deviationProfile time S)
    by_cases hS : S = quittingSingletonTerminal who
    · subst S
      simp only [↓reduceIte]
      exact neg_nonpos.mpr (mul_nonneg hdelta hsolo)
    · simp only [hS, ↓reduceIte]
      calc
        -((quittingAbsorbedMassLimit reward deviationProfile S -
              quittingAbsorbedMass reward deviationProfile time S) *
            reward S who) ≤
            |(quittingAbsorbedMassLimit reward deviationProfile S -
                quittingAbsorbedMass reward deviationProfile time S) *
              reward S who| := neg_le_abs _
        _ = (quittingAbsorbedMassLimit reward deviationProfile S -
              quittingAbsorbedMass reward deviationProfile time S) *
            |reward S who| := by
          rw [abs_mul, abs_of_nonneg hdelta]
        _ ≤ (quittingAbsorbedMassLimit reward deviationProfile S -
              quittingAbsorbedMass reward deviationProfile time S) *
            bound := mul_le_mul_of_nonneg_left (hreward S) hdelta
  have hstageTerminal :
      (quittingGame reward).expectedStagePayoff
          deviationProfile none time who -
        quittingTerminalPayoff reward deviationProfile who ≤
      bound * (quittingNonSoloMassLimit reward deviationProfile who -
        quittingNonSoloMass reward deviationProfile who time) := by
    calc
      (quittingGame reward).expectedStagePayoff
            deviationProfile none time who -
          quittingTerminalPayoff reward deviationProfile who =
          -(quittingTerminalPayoff reward deviationProfile who -
            (quittingGame reward).expectedStagePayoff
              deviationProfile none time who) := by ring
      _ = -(∑ S,
          (quittingAbsorbedMassLimit reward deviationProfile S -
            quittingAbsorbedMass reward deviationProfile time S) *
              reward S who) := by rw [hidentity]
      _ = ∑ S, -((quittingAbsorbedMassLimit reward deviationProfile S -
            quittingAbsorbedMass reward deviationProfile time S) *
              reward S who) := by rw [Finset.sum_neg_distrib]
      _ ≤ ∑ S, if S = quittingSingletonTerminal who then 0 else
          (quittingAbsorbedMassLimit reward deviationProfile S -
            quittingAbsorbedMass reward deviationProfile time S) * bound :=
        hsum
      _ = bound * (∑ S, if S = quittingSingletonTerminal who then 0 else
          (quittingAbsorbedMassLimit reward deviationProfile S -
            quittingAbsorbedMass reward deviationProfile time S)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S _
        by_cases hS : S = quittingSingletonTerminal who
        · simp [hS]
        · simp [hS]
          ring
      _ = bound * (quittingNonSoloMassLimit reward deviationProfile who -
          quittingNonSoloMass reward deviationProfile who time) := by
        rw [quittingNonSoloMassLimit_sub_eq_sum_tail]
  have htail :=
    quittingNonSoloMassLimit_update_sub_le_opponentLiveTail
      reward profile who deviation time
  have hscaled := mul_le_mul_of_nonneg_left htail hbound
  dsimp [deviationProfile, opponentProfile] at hstageTerminal hscaled ⊢
  linarith

/-- Finite-average form of the nonnegative-solo stagewise estimate. -/
theorem finiteAveragePayoff_update_le_terminal_add_opponentLiveTailCesaro_of_solo_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (horizon : ℕ) (hhorizon : 0 < horizon)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update profile who deviation) who ≤
      quittingTerminalPayoff reward
          (Function.update profile who deviation) who +
        bound * ((horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          (quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) time -
            quittingLiveMassLimit reward
              (quittingOpponentOnlyProfile reward profile who))) := by
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  rw [(quittingGame reward).finiteAveragePayoff_eq_sum_expectedStagePayoff]
  have hsum :
      (∑ time ∈ Finset.range horizon,
        (quittingGame reward).expectedStagePayoff
          (Function.update profile who deviation) none time who) ≤
      ∑ time ∈ Finset.range horizon,
        (quittingTerminalPayoff reward
            (Function.update profile who deviation) who +
          bound * (quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) time -
            quittingLiveMassLimit reward
              (quittingOpponentOnlyProfile reward profile who))) := by
    apply Finset.sum_le_sum
    intro time _
    exact
      expectedStagePayoff_update_le_terminal_add_opponentLiveTail_of_solo_nonneg
        reward profile who deviation time bound hbound hreward hsolo
  calc
    (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        (quittingGame reward).expectedStagePayoff
          (Function.update profile who deviation) none time who ≤
      (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        (quittingTerminalPayoff reward
            (Function.update profile who deviation) who +
          bound * (quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) time -
            quittingLiveMassLimit reward
              (quittingOpponentOnlyProfile reward profile who))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      have hne : (horizon : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hhorizon)
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      field_simp

/-- The Cesaro average of an opponent live tail tends to zero. -/
theorem tendsto_opponentLiveTailCesaro_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    Tendsto (fun horizon : ℕ => (horizon : ℝ)⁻¹ *
        ∑ time ∈ Finset.range horizon,
          (quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) time -
            quittingLiveMassLimit reward
              (quittingOpponentOnlyProfile reward profile who)))
      atTop (nhds 0) := by
  let opponentProfile := quittingOpponentOnlyProfile reward profile who
  have hconstant : Tendsto
      (fun _ : ℕ => quittingLiveMassLimit reward opponentProfile)
      atTop (nhds (quittingLiveMassLimit reward opponentProfile)) :=
    tendsto_const_nhds
  have htail := (tendsto_quittingLiveMass reward opponentProfile).sub hconstant
  simpa [opponentProfile] using htail.cesaro

/-- If every player's solo-quitting reward is nonnegative, terminal
deviations uniformly upper-approximate finite-horizon deviations. -/
theorem quittingGame_hasUniformDeviationUpperApproximation_of_solo_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S who, |reward S who| ≤ bound)
    (hsolo : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who) :
    (quittingGame reward).HasUniformDeviationUpperApproximation
      none (quittingTerminalPayoff reward) profile := by
  intro error herror
  have heventually : ∀ᶠ horizon : ℕ in atTop, ∀ who,
      bound * ((horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        (quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile who) time -
          quittingLiveMassLimit reward
            (quittingOpponentOnlyProfile reward profile who))) < error := by
    apply Filter.eventually_all.mpr
    intro who
    have hscaled : Tendsto (fun horizon : ℕ =>
        bound * ((horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          (quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) time -
            quittingLiveMassLimit reward
              (quittingOpponentOnlyProfile reward profile who))))
        atTop (nhds 0) := by
      simpa using (Filter.Tendsto.const_mul bound
        (tendsto_opponentLiveTailCesaro_zero reward profile who))
    exact (tendsto_order.1 hscaled).2 error herror
  obtain ⟨threshold, hthreshold⟩ :=
    Filter.eventually_atTop.1 heventually
  refine ⟨max 1 threshold, fun horizon hhorizon who deviation => ?_⟩
  refine ⟨deviation, ?_⟩
  have hpositive : 0 < horizon :=
    lt_of_lt_of_le Nat.zero_lt_one
      (le_trans (Nat.le_max_left 1 threshold) hhorizon)
  have hfinite :=
    finiteAveragePayoff_update_le_terminal_add_opponentLiveTailCesaro_of_solo_nonneg
      reward profile who deviation horizon hpositive bound hbound
        (fun S => hreward S who) (hsolo who)
  have hsmall := hthreshold horizon
    (le_trans (Nat.le_max_right 1 threshold) hhorizon) who
  linarith

/-- Terminal epsilon-Nash is uniform epsilon-prime Nash when every solo
quitting reward is nonnegative. -/
theorem quittingGame_isUniformεEquilibrium_of_terminalNash_of_solo_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {ε ε' : ℝ} (herror : ε < ε')
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S who, |reward S who| ≤ bound)
    (hsolo : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who) :
    (quittingGame reward).IsUniformεEquilibrium none ε' profile := by
  exact StochasticGame.isUniformεEquilibrium_of_isεAsymptoticNash_of_upperApproximation
    (quittingGame reward) none (quittingTerminalPayoff reward) profile
      herror hnash
      (quittingGame_hasUniformDeviationUpperApproximation_of_solo_nonneg
        reward profile bound hbound hreward hsolo)
      (fun who => tendsto_finiteAveragePayoff_quittingGame
        reward profile who)

end GameTheory
