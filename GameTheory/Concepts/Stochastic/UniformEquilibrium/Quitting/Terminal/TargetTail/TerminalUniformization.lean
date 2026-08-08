/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Punishment.NonnegativeSoloUniformization
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Punishment.NegativeSoloUniformization

/-!
# Terminal equilibria uniformize in finite quitting games

Every unilateral finite-horizon deviation in a finite quitting game admits a
terminal-payoff comparison deviation with a uniform one-sided error.

* If the deviator's singleton quitting reward is nonnegative, use the same
  deviation.  Only the Cesaro average of the opponents' live tail can hurt.
* If it is negative, follow the deviation to a common cutoff and then always
  continue.  The error is a vanishing prefix term plus the opponents' live
  tail at the cutoff.

Thus every terminal epsilon-Nash profile is a uniform epsilon-prime
equilibrium for every larger error.  This is the profile-level content of the
terminal-to-uniform proposition for finite quitting games.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A canonical finite bound for every coordinate of a quitting payoff
table.  The sum form avoids any nonempty maximum convention. -/
def quittingRewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  ∑ S, ∑ who, |reward S who|

omit [DecidableEq ι] in
/-- The canonical quitting reward bound is nonnegative. -/
theorem quittingRewardBound_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 ≤ quittingRewardBound reward := by
  unfold quittingRewardBound
  positivity

omit [DecidableEq ι] in
/-- Every terminal reward coordinate is below the canonical finite bound. -/
theorem abs_reward_le_quittingRewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) :
    |reward terminal who| ≤ quittingRewardBound reward := by
  unfold quittingRewardBound
  have hcoordinate : |reward terminal who| ≤
      ∑ player, |reward terminal player| := by
    exact Finset.single_le_sum
      (fun player _ => abs_nonneg (reward terminal player))
      (Finset.mem_univ who)
  have hterminal : (∑ player, |reward terminal player|) ≤
      ∑ S, ∑ player, |reward S player| := by
    exact Finset.single_le_sum
      (fun S _ => Finset.sum_nonneg fun player _ =>
        abs_nonneg (reward S player))
      (Finset.mem_univ terminal)
  exact hcoordinate.trans hterminal

/-- Every finite quitting-game profile has the one-sided deviation
approximation needed to transfer terminal Nash inequalities to uniform Nash
inequalities. -/
theorem quittingGame_hasUniformDeviationUpperApproximation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S who, |reward S who| ≤ bound) :
    (quittingGame reward).HasUniformDeviationUpperApproximation
      none (quittingTerminalPayoff reward) profile := by
  intro error herror
  have hhalf : 0 < error / 2 := by linarith
  have heventuallyCesaro : ∀ᶠ horizon : ℕ in atTop, ∀ who,
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
  obtain ⟨cesaroThreshold, hcesaroThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyCesaro
  have heventuallyTail : ∀ᶠ cutoff : ℕ in atTop, ∀ who,
      2 * bound * (quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile who) cutoff -
          quittingLiveMassLimit reward
            (quittingOpponentOnlyProfile reward profile who)) < error / 2 := by
    apply Filter.eventually_all.mpr
    intro who
    let opponentProfile := quittingOpponentOnlyProfile reward profile who
    have hconstant : Tendsto
        (fun _ : ℕ => quittingLiveMassLimit reward opponentProfile)
        atTop (nhds (quittingLiveMassLimit reward opponentProfile)) :=
      tendsto_const_nhds
    have htail :=
      (tendsto_quittingLiveMass reward opponentProfile).sub hconstant
    have hscaled := Filter.Tendsto.const_mul (2 * bound) htail
    have hscaledZero : Tendsto (fun cutoff : ℕ =>
        2 * bound * (quittingLiveMass reward opponentProfile cutoff -
          quittingLiveMassLimit reward opponentProfile)) atTop (nhds 0) := by
      simpa using hscaled
    exact (tendsto_order.1 hscaledZero).2 (error / 2) hhalf
  obtain ⟨cutoff, htailAfter⟩ :=
    Filter.eventually_atTop.1 heventuallyTail
  have htailSmall : ∀ who,
      2 * bound * (quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile who) cutoff -
          quittingLiveMassLimit reward
            (quittingOpponentOnlyProfile reward profile who)) < error / 2 :=
    htailAfter cutoff le_rfl
  have hinv : Tendsto (fun horizon : ℕ => (horizon : ℝ)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hprefixLimit : Tendsto (fun horizon : ℕ =>
      2 * bound * ((horizon : ℝ)⁻¹ * (cutoff : ℝ)))
      atTop (nhds 0) := by
    have hscaled := Filter.Tendsto.const_mul
      (2 * bound * (cutoff : ℝ)) hinv
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have heventuallyPrefix : ∀ᶠ horizon : ℕ in atTop,
      2 * bound * ((horizon : ℝ)⁻¹ * (cutoff : ℝ)) < error / 2 :=
    (tendsto_order.1 hprefixLimit).2 (error / 2) hhalf
  obtain ⟨prefixThreshold, hprefixThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyPrefix
  let threshold := max cutoff (max 1 (max cesaroThreshold prefixThreshold))
  refine ⟨threshold, fun horizon hhorizon who deviation => ?_⟩
  have hcutoffHorizon : cutoff ≤ horizon :=
    le_trans (Nat.le_max_left cutoff
      (max 1 (max cesaroThreshold prefixThreshold))) hhorizon
  have hpositiveHorizon : 0 < horizon := by
    apply lt_of_lt_of_le Nat.zero_lt_one
    exact le_trans
      (le_trans (Nat.le_max_left 1 (max cesaroThreshold prefixThreshold))
        (Nat.le_max_right cutoff
          (max 1 (max cesaroThreshold prefixThreshold))))
      hhorizon
  have hcesaroHorizon : cesaroThreshold ≤ horizon := by
    apply le_trans _ hhorizon
    exact le_trans
      (le_trans (Nat.le_max_left cesaroThreshold prefixThreshold)
        (Nat.le_max_right 1 (max cesaroThreshold prefixThreshold)))
      (Nat.le_max_right cutoff
        (max 1 (max cesaroThreshold prefixThreshold)))
  have hprefixHorizon : prefixThreshold ≤ horizon := by
    apply le_trans _ hhorizon
    exact le_trans
      (le_trans (Nat.le_max_right cesaroThreshold prefixThreshold)
        (Nat.le_max_right 1 (max cesaroThreshold prefixThreshold)))
      (Nat.le_max_right cutoff
        (max 1 (max cesaroThreshold prefixThreshold)))
  by_cases hsolo : 0 ≤ reward (quittingSingletonTerminal who) who
  · refine ⟨deviation, ?_⟩
    have hfinite :=
      finiteAveragePayoff_update_le_terminal_add_opponentLiveTailCesaro_of_solo_nonneg
        reward profile who deviation horizon hpositiveHorizon bound hbound
          (fun S => hreward S who) hsolo
    have hsmall := hcesaroThreshold horizon hcesaroHorizon who
    linarith
  · let cutoffDeviation :=
      quittingContinueAfterStrategy reward who deviation cutoff
    refine ⟨cutoffDeviation, ?_⟩
    have hfinite :=
      finiteAveragePayoff_update_le_cutoffTerminal_add_prefix_add_tail_of_solo_nonpos
        reward profile who deviation cutoff horizon hcutoffHorizon
          hpositiveHorizon bound hbound hreward (le_of_not_ge hsolo)
    have hprefixSmall := hprefixThreshold horizon hprefixHorizon
    have htailWho := htailSmall who
    have hcombined :
        2 * bound * ((horizon : ℝ)⁻¹ * (cutoff : ℝ) +
          (quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) cutoff -
            quittingLiveMassLimit reward
              (quittingOpponentOnlyProfile reward profile who))) < error := by
      rw [mul_add]
      linarith
    dsimp [cutoffDeviation]
    linarith

/-- Terminal epsilon-Nash implies uniform epsilon-prime equilibrium for every
strictly larger error in every finite quitting game. -/
theorem quittingGame_isUniformεEquilibrium_of_terminalNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {ε ε' : ℝ} (herror : ε < ε')
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S who, |reward S who| ≤ bound) :
    (quittingGame reward).IsUniformεEquilibrium none ε' profile := by
  exact StochasticGame.isUniformεEquilibrium_of_isεAsymptoticNash_of_upperApproximation
    (quittingGame reward) none (quittingTerminalPayoff reward) profile
      herror hnash
      (quittingGame_hasUniformDeviationUpperApproximation
        reward profile bound hbound hreward)
      (fun who => tendsto_finiteAveragePayoff_quittingGame
        reward profile who)

/-- Bound-free finite-game form of the terminal-to-uniform theorem.  Finiteness
of the player set and terminal table supplies the required reward bound
automatically. -/
theorem quittingGame_isUniformεEquilibrium_of_terminalNash_finite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {ε ε' : ℝ} (herror : ε < ε')
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile) :
    (quittingGame reward).IsUniformεEquilibrium none ε' profile := by
  exact quittingGame_isUniformεEquilibrium_of_terminalNash
    reward profile herror hnash (quittingRewardBound reward)
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)

end GameTheory
