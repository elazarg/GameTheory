/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingBehaviorPureTimeExtremality
import GameTheory.Concepts.Stochastic.QuittingExceptionalHazard

/-!
# One-exception synthesis for quitting deviations

When total live mass tends to zero, at most one player can retain positive
opponent-only survival.  This module selects that possible exception and
combines the selection with the zero-survival/nonnegative-solo infinite
local-to-global theorem.  Thus every unilateral behavioral deviation is
controlled after checking a singleton-reward sign for at most one player.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Under total absorption, one can designate a player so that every other
player's opponent-only survival clock contracts to zero. -/
theorem exists_quittingExceptionalPlayer
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (htotal : Tendsto (quittingLiveMass reward profile) atTop (nhds 0)) :
    ∃ exceptional : ι, ∀ who, who ≠ exceptional →
      Tendsto (quittingLiveMass reward
        (quittingOpponentOnlyProfile reward profile who)) atTop (nhds 0) := by
  classical
  by_cases hall : ∀ who, Tendsto (quittingLiveMass reward
      (quittingOpponentOnlyProfile reward profile who)) atTop (nhds 0)
  · exact ⟨Classical.choice inferInstance, fun who _ => hall who⟩
  · obtain ⟨exceptional, hexceptional⟩ := not_forall.mp hall
    refine ⟨exceptional, fun who hne => ?_⟩
    exact (tendsto_zero_quittingOpponentLiveMass_or
      reward profile htotal hne).resolve_right hexceptional

/-- If all nonexceptional opponent clocks contract, and the exceptional clock
either also contracts or has nonnegative singleton reward, then the weighted
residual bound controls every unilateral behavioral deviation. -/
theorem quittingTerminalDeviationGap_le_tsum_liveResidual_of_oneException
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (exceptional : ι) (bound : ℝ) (hbound0 : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hothers : ∀ who, who ≠ exceptional →
      Tendsto (quittingLiveMass reward
        (quittingOpponentOnlyProfile reward profile who)) atTop (nhds 0))
    (hexceptional :
      Tendsto (quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile exceptional))
          atTop (nhds 0) ∨
        0 ≤ reward (quittingSingletonTerminal exceptional) exceptional)
    (hsummable : ∀ who, Summable (fun time =>
      quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward profile) who 0 time *
        quittingPrescribedOneStepResidual reward
          (quittingProfileLiveRoot reward profile) who
          (quittingRootSequenceTerminalValue reward
            (quittingProfileLiveRoot reward profile) who) time)) :
    ∀ (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who),
      quittingTerminalPayoff reward
            (Function.update profile who deviation) who -
          quittingTerminalPayoff reward profile who ≤
        ∑' time, quittingOpponentSurvivalWeight
            (quittingProfileLiveRoot reward profile) who 0 time *
          quittingPrescribedOneStepResidual reward
            (quittingProfileLiveRoot reward profile) who
            (quittingRootSequenceTerminalValue reward
              (quittingProfileLiveRoot reward profile) who) time := by
  intro who deviation
  let opponentProfile := quittingOpponentOnlyProfile reward profile who
  let limit := quittingLiveMassLimit reward opponentProfile
  have hlimit : Tendsto (quittingOpponentSurvivalWeight
      (quittingProfileLiveRoot reward profile) who 0) atTop (nhds limit) := by
    have hweights : quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) who 0 =
        quittingLiveMass reward opponentProfile := by
      funext fuel
      exact quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
        reward profile who fuel
    rw [hweights]
    exact tendsto_quittingLiveMass reward opponentProfile
  have hbranch : limit = 0 ∨
      0 ≤ reward (quittingSingletonTerminal who) who := by
    by_cases hwho : who = exceptional
    · subst who
      rcases hexceptional with hzero | hsolo
      · left
        exact tendsto_nhds_unique
          (tendsto_quittingLiveMass reward opponentProfile) hzero
      · exact Or.inr hsolo
    · left
      exact tendsto_nhds_unique
        (tendsto_quittingLiveMass reward opponentProfile)
        (hothers who hwho)
  have hroot :=
    quittingRootSequenceHazardTerminalGap_le_tsum_residual_of_zero_or_nonnegativeSolo
      reward (quittingProfileLiveRoot reward profile) who
      (quittingBehaviorLiveHazard reward deviation) bound limit
      hbound0 hreward hlimit hbranch (hsummable who)
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  exact hroot

/-- **One-exception synthesis.**  Under total absorption, there is one
designated player such that checking either contraction of that player's
opponent clock or nonnegativity of that player's singleton reward suffices to
control every unilateral behavioral deviation. -/
theorem exists_quittingExceptionalPlayer_terminalDeviationGap_le
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (bound : ℝ) (hbound0 : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (htotal : Tendsto (quittingLiveMass reward profile) atTop (nhds 0))
    (hsummable : ∀ who, Summable (fun time =>
      quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward profile) who 0 time *
        quittingPrescribedOneStepResidual reward
          (quittingProfileLiveRoot reward profile) who
          (quittingRootSequenceTerminalValue reward
            (quittingProfileLiveRoot reward profile) who) time)) :
    ∃ exceptional : ι,
      (Tendsto (quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile exceptional))
          atTop (nhds 0) ∨
        0 ≤ reward (quittingSingletonTerminal exceptional) exceptional) →
      ∀ (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who),
        quittingTerminalPayoff reward
              (Function.update profile who deviation) who -
            quittingTerminalPayoff reward profile who ≤
          ∑' time, quittingOpponentSurvivalWeight
              (quittingProfileLiveRoot reward profile) who 0 time *
            quittingPrescribedOneStepResidual reward
              (quittingProfileLiveRoot reward profile) who
              (quittingRootSequenceTerminalValue reward
                (quittingProfileLiveRoot reward profile) who) time := by
  obtain ⟨exceptional, hothers⟩ :=
    exists_quittingExceptionalPlayer reward profile htotal
  refine ⟨exceptional, fun hexceptional => ?_⟩
  exact quittingTerminalDeviationGap_le_tsum_liveResidual_of_oneException
    reward profile exceptional bound hbound0 hreward hothers hexceptional
      hsummable

end GameTheory
