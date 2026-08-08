/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Paths.OpponentLiveMass
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Paths.LiveTail
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Terminal.ToUniformDeviationApproximation

/-!
# Uniformization when opponents absorb almost surely

Fix a quitting-game profile.  If, for each player, the opponents quit almost
surely when that player always continues, then every unilateral deviation's
finite-average payoff is uniformly bounded by its own terminal payoff plus a
common Cesaro survival error.  This proves the first case of the
Solan--Vieille terminal-to-uniform argument.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One deviating stage payoff is bounded by the deviation's terminal payoff
plus the opponent-only survival probability at that stage. -/
theorem expectedStagePayoff_update_le_terminal_add_opponentLiveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (time : ℕ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound) :
    (quittingGame reward).expectedStagePayoff
        (Function.update profile who deviation) none time who ≤
      quittingTerminalPayoff reward
        (Function.update profile who deviation) who +
      bound * quittingLiveMass reward
        (quittingOpponentOnlyProfile reward profile who) time := by
  let deviationProfile := Function.update profile who deviation
  have htail :=
    abs_quittingTerminalPayoff_sub_expectedStagePayoff_le_liveTail
      reward deviationProfile time who bound hreward
  have hlive := quittingLiveMass_update_le_opponentOnly
    reward profile who deviation time
  have hlimit := quittingLiveMassLimit_nonneg reward deviationProfile
  have hdifference :
      quittingLiveMass reward deviationProfile time -
          quittingLiveMassLimit reward deviationProfile ≤
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) time := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hdifference hbound
  dsimp [deviationProfile] at htail hscaled
  have habove := neg_le_abs
    (quittingTerminalPayoff reward
      (Function.update profile who deviation) who -
      (quittingGame reward).expectedStagePayoff
        (Function.update profile who deviation) none time who)
  linarith

/-- The finite-average version of the stagewise opponent-survival bound. -/
theorem finiteAveragePayoff_update_le_terminal_add_opponentLiveCesaro
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (horizon : ℕ) (hhorizon : 0 < horizon)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update profile who deviation) who ≤
      quittingTerminalPayoff reward
        (Function.update profile who deviation) who +
      bound * ((horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) time) := by
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
        bound * quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) time) := by
    apply Finset.sum_le_sum
    intro time _
    exact expectedStagePayoff_update_le_terminal_add_opponentLiveMass
      reward profile who deviation time bound hbound hreward
  calc
    (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        (quittingGame reward).expectedStagePayoff
          (Function.update profile who deviation) none time who ≤
      (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        (quittingTerminalPayoff reward
          (Function.update profile who deviation) who +
        bound * quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) time) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      have hne : (horizon : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hhorizon)
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      field_simp

/-- If the opponents absorb almost surely, their Cesaro live mass tends to
zero. -/
theorem tendsto_opponentLiveCesaro_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (habsorbs : quittingLiveMassLimit reward
      (quittingOpponentOnlyProfile reward profile who) = 0) :
    Tendsto (fun horizon : ℕ => (horizon : ℝ)⁻¹ *
        ∑ time ∈ Finset.range horizon,
          quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile who) time)
      atTop (nhds 0) := by
  have hlive := tendsto_quittingLiveMass reward
    (quittingOpponentOnlyProfile reward profile who)
  rw [habsorbs] at hlive
  exact hlive.cesaro

/-- In the almost-sure opponent-absorption case, terminal deviations give
the required uniform one-sided approximation; the limiting deviation is the
finite-horizon deviation itself. -/
theorem quittingGame_hasUniformDeviationUpperApproximation_of_opponentsAbsorb
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S who, |reward S who| ≤ bound)
    (habsorbs : ∀ who, quittingLiveMassLimit reward
      (quittingOpponentOnlyProfile reward profile who) = 0) :
    (quittingGame reward).HasUniformDeviationUpperApproximation
      none (quittingTerminalPayoff reward) profile := by
  intro error herror
  have heventually : ∀ᶠ horizon : ℕ in atTop, ∀ who,
      bound * ((horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) time) < error := by
    apply Filter.eventually_all.mpr
    intro who
    have hscaled : Tendsto (fun horizon : ℕ =>
        bound * ((horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile who) time))
        atTop (nhds 0) := by
      simpa using (Filter.Tendsto.const_mul bound
        (tendsto_opponentLiveCesaro_zero reward profile who
          (habsorbs who)))
    exact (tendsto_order.1 hscaled).2 error herror
  obtain ⟨threshold, hthreshold⟩ :=
    Filter.eventually_atTop.1 heventually
  refine ⟨max 1 threshold, fun horizon hhorizon who deviation => ?_⟩
  refine ⟨deviation, ?_⟩
  have hpositive : 0 < horizon :=
    lt_of_lt_of_le Nat.zero_lt_one
      (le_trans (Nat.le_max_left 1 threshold) hhorizon)
  have hfinite :=
    finiteAveragePayoff_update_le_terminal_add_opponentLiveCesaro
      reward profile who deviation horizon hpositive bound hbound
        (fun S => hreward S who)
  have hsmall := hthreshold horizon
    (le_trans (Nat.le_max_right 1 threshold) hhorizon) who
  linarith

/-- Terminal epsilon-Nash is uniform epsilon-prime Nash in the
almost-sure opponent-absorption case. -/
theorem quittingGame_isUniformεEquilibrium_of_terminalNash_of_opponentsAbsorb
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {ε ε' : ℝ} (herror : ε < ε')
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S who, |reward S who| ≤ bound)
    (habsorbs : ∀ who, quittingLiveMassLimit reward
      (quittingOpponentOnlyProfile reward profile who) = 0) :
    (quittingGame reward).IsUniformεEquilibrium none ε' profile := by
  exact StochasticGame.isUniformεEquilibrium_of_isεAsymptoticNash_of_upperApproximation
    (quittingGame reward) none (quittingTerminalPayoff reward) profile
      herror hnash
      (quittingGame_hasUniformDeviationUpperApproximation_of_opponentsAbsorb
        reward profile bound hbound hreward habsorbs)
      (fun who => tendsto_finiteAveragePayoff_quittingGame
        reward profile who)

end GameTheory
