/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingPhaseSwitchDeviationCap

/-!
# Coupled phase-switch caps

The scalar phase-switch cap in `QuittingPhaseSwitchDeviationCap` first compares
play with a plan truncated to the all-Continue continuation.  That is the right
interface when the truncated prefix is independently deviation-safe, but it can
charge a spurious escape payoff when the prescribed prefix payoff is negative.

This file keeps the deviated survival coefficient attached to both terms.  If a
prefix deviation is bounded by `(1 - s) * anchor + prefixError` and the tail is
bounded by `anchor + tailError`, then the exact phase-switch decomposition gives
`anchor + prefixError + s * tailError`.  Since `s ∈ [0,1]`, nonnegative tail
error yields the clean bound `anchor + prefixError + tailError` without any sign
hypothesis on `anchor`.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The coupled hazard-level phase-switch cap.**  The prefix cap and the tail
cap share one anchor.  The survival coefficient therefore cancels the anchor
exactly instead of comparing the prefix with a zero continuation first. -/
theorem quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_coupled
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    {anchor prefixError tailError : ℝ}
    (htailError : 0 ≤ tailError)
    (hprefix : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan switch) who
          (quittingTruncatedHazard g switch) 0 ≤
        (1 - quittingJointSurvivalWeight
          (quittingRootSequenceUpdate plan who g) 0 switch) * anchor +
          prefixError)
    (htail : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        anchor + tailError)
    (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who hazard 0 ≤
      anchor + prefixError + tailError := by
  set survival := quittingJointSurvivalWeight
    (quittingRootSequenceUpdate plan who hazard) 0 switch with hsurvival
  have hsurvival0 : 0 ≤ survival :=
    quittingJointSurvivalWeight_nonneg _ 0 switch
  have hsurvival1 : survival ≤ 1 :=
    quittingJointSurvivalWeight_le_one _ 0 switch
  have hprefixBound := hprefix hazard
  have htailBound := htail (fun offset => hazard (switch + offset))
  have htailScaled :=
    mul_le_mul_of_nonneg_left htailBound hsurvival0
  have hscale : survival * tailError ≤ tailError := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsurvival1) htailError]
  rw [quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots]
  rw [← hsurvival]
  nlinarith

/-- **The coupled behavior-level phase-switch cap.**  An arbitrary behavior
deviation is reduced to its live hazard, after which the coupled hazard theorem
applies verbatim. -/
theorem quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le_coupled
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    {anchor prefixError tailError : ℝ}
    (htailError : 0 ≤ tailError)
    (hprefix : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan switch) who
          (quittingTruncatedHazard g switch) 0 ≤
        (1 - quittingJointSurvivalWeight
          (quittingRootSequenceUpdate plan who g) 0 switch) * anchor +
          prefixError)
    (htail : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        anchor + tailError)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update (quittingPhaseSwitchProfile reward plan punish switch)
          who deviation) who ≤
      anchor + prefixError + tailError := by
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingProfileLiveRoot_quittingPhaseSwitchProfile]
  exact
    quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_coupled
      reward plan punish switch who htailError hprefix htail
      (quittingBehaviorLiveHazard reward deviation)

end GameTheory
