/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformization

/-!
# Selecting a fixed uniform payoff from terminal equilibria

The profile-level terminal-to-uniform theorem leaves one existence-level
quantifier: terminal approximate equilibria at successively smaller errors may
have different payoff vectors.  Their terminal payoffs lie in a common compact
finite-dimensional cube.  A convergent subsequence, the strict-error
terminal-to-uniform theorem, and fixed-profile Cesaro convergence select one
uniform equilibrium payoff.

Consequently, for finite quitting games, existence of terminal approximate
equilibria at every positive accuracy is equivalent to existence of a uniform
equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Terminal payoffs of arbitrary profiles lie in the cube determined by the
canonical finite reward bound. -/
theorem quittingTerminalPayoff_mem_rewardCube
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile ∈
      Set.Icc (fun _ => -quittingRewardBound reward)
        (fun _ => quittingRewardBound reward) := by
  constructor <;> intro who
  · exact neg_le_of_abs_le (abs_quittingTerminalPayoff_le reward profile who
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward))
  · exact le_of_abs_le (abs_quittingTerminalPayoff_le reward profile who
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward))

/-- Terminal approximate equilibria at every positive accuracy select one
fixed uniform equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hterminal : ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let approximationError : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have herrorPositive : ∀ n, 0 < approximationError n := by
    intro n
    dsimp [approximationError]
    positivity
  have hexists : ∀ n, ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (approximationError n) profile :=
    fun n => hterminal (approximationError n) (herrorPositive n)
  choose profiles hprofiles using hexists
  let terminalPayoffs : ℕ → Payoff ι := fun n =>
    quittingTerminalPayoff reward (profiles n)
  have hmem : ∀ n, terminalPayoffs n ∈
      Set.Icc (fun _ => -quittingRewardBound reward)
        (fun _ => quittingRewardBound reward) := by
    intro n
    exact quittingTerminalPayoff_mem_rewardCube reward (profiles n)
  obtain ⟨payoff, hpayoffMem, subsequence, hsubsequence,
      hpayoffLimit⟩ :=
    (isCompact_Icc : IsCompact
      (Set.Icc (fun _ : ι => -quittingRewardBound reward)
        (fun _ : ι => quittingRewardBound reward))).tendsto_subseq hmem
  refine ⟨payoff, fun ε hε => ?_⟩
  have hhalf : 0 < ε / 2 := by linarith
  have herrorLimit : Tendsto approximationError atTop (nhds 0) := by
    simpa [approximationError] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsubsequenceError : Tendsto
      (approximationError ∘ subsequence) atTop (nhds 0) :=
    herrorLimit.comp hsubsequence.tendsto_atTop
  have heventuallyError : ∀ᶠ n : ℕ in atTop,
      approximationError (subsequence n) < ε :=
    (tendsto_order.1 hsubsequenceError).2 ε hε
  have heventuallyPayoff : ∀ᶠ n : ℕ in atTop, ∀ who,
      |terminalPayoffs (subsequence n) who - payoff who| < ε / 2 := by
    apply Filter.eventually_all.mpr
    intro who
    have hcoordinate : Tendsto
        (fun n => terminalPayoffs (subsequence n) who)
        atTop (nhds (payoff who)) :=
      (continuous_apply who).tendsto payoff |>.comp hpayoffLimit
    have hball := hcoordinate.eventually
      (Metric.ball_mem_nhds (payoff who) hhalf)
    filter_upwards [hball] with n hn
    simpa only [Metric.mem_ball, Real.dist_eq] using hn
  have heventuallyBoth : ∀ᶠ n : ℕ in atTop,
      approximationError (subsequence n) < ε ∧
        ∀ who, |terminalPayoffs (subsequence n) who - payoff who| < ε / 2 :=
    heventuallyError.and heventuallyPayoff
  obtain ⟨selectionThreshold, hselectionThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyBoth
  let selectedIndex := subsequence selectionThreshold
  let selectedProfile := profiles selectedIndex
  have hselected := hselectionThreshold selectionThreshold le_rfl
  have hselectedError : approximationError selectedIndex < ε := by
    exact hselected.1
  have hselectedPayoff : ∀ who,
      |quittingTerminalPayoff reward selectedProfile who - payoff who| <
        ε / 2 := by
    simpa [selectedIndex, selectedProfile, terminalPayoffs] using hselected.2
  have huniform : (quittingGame reward).IsUniformεEquilibrium
      none ε selectedProfile :=
    quittingGame_isUniformεEquilibrium_of_terminalNash_finite
      reward selectedProfile hselectedError (hprofiles selectedIndex)
  obtain ⟨nashThreshold, hnashThreshold⟩ := huniform
  have heventuallyDelivery : ∀ᶠ horizon : ℕ in atTop, ∀ who,
      |(quittingGame reward).finiteAveragePayoff none horizon
          selectedProfile who -
        quittingTerminalPayoff reward selectedProfile who| < ε / 2 := by
    apply Filter.eventually_all.mpr
    intro who
    have hball :=
      (tendsto_finiteAveragePayoff_quittingGame
        reward selectedProfile who).eventually
        (Metric.ball_mem_nhds
          (quittingTerminalPayoff reward selectedProfile who) hhalf)
    filter_upwards [hball] with horizon hhorizon
    simpa only [Metric.mem_ball, Real.dist_eq] using hhorizon
  obtain ⟨deliveryThreshold, hdeliveryThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨selectedProfile, max nashThreshold deliveryThreshold,
    fun horizon hhorizon => ?_⟩
  constructor
  · exact hnashThreshold horizon
      (le_trans (Nat.le_max_left _ _) hhorizon)
  · intro who
    have hdelivery := hdeliveryThreshold horizon
      (le_trans (Nat.le_max_right _ _) hhorizon) who
    calc
      |(quittingGame reward).finiteAveragePayoff none horizon
            selectedProfile who - payoff who| =
          |((quittingGame reward).finiteAveragePayoff none horizon
              selectedProfile who -
            quittingTerminalPayoff reward selectedProfile who) +
            (quittingTerminalPayoff reward selectedProfile who -
              payoff who)| := by ring_nf
      _ ≤ |(quittingGame reward).finiteAveragePayoff none horizon
              selectedProfile who -
            quittingTerminalPayoff reward selectedProfile who| +
          |quittingTerminalPayoff reward selectedProfile who -
            payoff who| := abs_add_le _ _
      _ ≤ ε := by
        linarith [hselectedPayoff who]

/-- For finite quitting games, terminal approximate existence at every
positive error is equivalent to existence of a uniform equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ profile : (quittingGame reward).BehaviorProfile,
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) ε profile := by
  constructor
  · rintro ⟨payoff, hpayoff⟩ ε hε
    have hhalf : 0 < ε / 2 := by linarith
    obtain ⟨profile, threshold, hprofile⟩ := hpayoff (ε / 2) hhalf
    have huniform : (quittingGame reward).IsUniformεEquilibrium
        none (ε / 2) profile :=
      ⟨threshold, fun horizon hhorizon => (hprofile horizon hhorizon).1⟩
    have hterminal : (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (ε / 2) profile :=
      (quittingGame reward).isεAsymptoticNash_of_isUniformεEquilibrium
        none (quittingTerminalPayoff reward) huniform
        (fun selectedProfile who =>
          tendsto_finiteAveragePayoff_quittingGame
            reward selectedProfile who)
    exact ⟨profile, hterminal.mono (by linarith)⟩
  · exact quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors reward

end GameTheory
