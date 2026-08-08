/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Paths.SupportWitnessClockCollapse
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Punishment.FreeReduction
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Terminal.TargetTail.TargetAnchoredTail

/-!
# Uniform-equilibrium reduction through support witnesses

`QuittingSupportWitnessClockCollapse` removes the stochastic Case-1 crossing
estimate once the one-stage action witnessing Simon's `Eδ` correspondence is
retained.  This file compiles that deterministic switch package into an
actual terminal approximate Nash profile.

The only continuation datum left is player-indexed and one-sided.  For every
possible marked target, one supplies a tail on which that target is already a
best reply and whose target value is close to the plan's value at the switch.
No common punishment tail is required.  After the global first own-survival
crossing selects the marked target, its closed tail is spliced onto the plan.

* the marked target is controlled by the prefix ledger and the closed-tail
  continuation value;
* every other player is controlled by the selected target's small own
  survival, since that survival is a factor of their deleted reach; and
* the target's prescribed payoff changes by only the plan's small joint reach.

The resulting error is

`ledgerCap + 2 * δ + continuationSlack + 7 * threshold * rewardBound`.

Thus support-witness packages at every positive accuracy yield a single
uniform-equilibrium payoff by the existing compact payoff-selection theorem.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The support-witness producer needed by the deterministic phase-switch
compiler.  The global switch is the first stage at which some player's own
planned survival falls below `threshold`.

The tail clause is player-indexed: after the switch has selected `target`, a
different target-closed tail may be chosen for that player. -/
def HasQuittingSupportWitnessTailPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) : Prop :=
  ∃ (plan : ℕ → ι → PMF Bool)
      (δ ledgerCap threshold continuationSlack : ℝ),
    0 ≤ δ ∧
    0 < ledgerCap ∧
    0 < threshold ∧
    0 ≤ continuationSlack ∧
    δ ≤ ledgerCap * threshold ∧
    IsQuittingRootSequenceSupportApproxNash reward plan δ ∧
    (∃ cutoff, ∃ player,
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard plan player) cutoff ≤ threshold) ∧
    (∀ target : ι,
      ∃ tail : ℕ → ι → PMF Bool,
        IsQuittingTargetClosedAt reward tail target 0 ∧
        quittingRootSequenceTerminalValue reward tail target 0 ≤
          quittingRootSequenceTerminalValue reward plan target
              (quittingSupportSurvivalSwitchIndex plan threshold) +
            continuationSlack) ∧
    ledgerCap + 2 * δ + continuationSlack +
        threshold * (7 * quittingRewardBound reward) ≤ ε

/-- A target-closed tail caps the marked player's deviations by its prescribed
value.  Every unmarked player's deviations are bounded trivially by the
reward bound. -/
theorem exists_quittingPhaseSwitchPunishCap_of_targetClosedTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ℕ → ι → PMF Bool) (target : ι)
    (hclosed : IsQuittingTargetClosedAt reward tail target 0) :
    ∃ cap : ι → ℝ,
      cap target = quittingRootSequenceTerminalValue reward tail target 0 ∧
      (∀ (who : ι) (hazard : ℕ → PMF Bool),
        quittingRootSequenceHazardTerminalValue reward tail who hazard 0 ≤
          cap who) ∧
      ∀ who : ι, cap who ≤ quittingRewardBound reward := by
  let cap : ι → ℝ := fun who =>
    if who = target then
      quittingRootSequenceTerminalValue reward tail target 0
    else quittingRewardBound reward
  refine ⟨cap, by simp [cap], ?_, ?_⟩
  · intro who hazard
    by_cases hwho : who = target
    · subst who
      simpa [cap] using hclosed hazard
    · have hdeviationBound :=
        abs_quittingRootSequenceTerminalValue_le reward
          (quittingRootSequenceUpdate tail who hazard) who 0
          (quittingRewardBound_nonneg reward)
          (abs_reward_le_quittingRewardBound reward)
      have hupper :
          quittingRootSequenceHazardTerminalValue reward tail who hazard 0 ≤
            quittingRewardBound reward := by
        unfold quittingRootSequenceHazardTerminalValue
        exact (le_abs_self _).trans hdeviationBound
      simpa [cap, hwho] using hupper
  · intro who
    by_cases hwho : who = target
    · subst who
      have hvalueBound :=
        abs_quittingRootSequenceTerminalValue_le
          reward tail target 0 (quittingRewardBound_nonneg reward)
            (abs_reward_le_quittingRewardBound reward)
      have hupper :
          quittingRootSequenceTerminalValue reward tail target 0 ≤
            quittingRewardBound reward :=
        (le_abs_self _).trans hvalueBound
      simpa [cap] using hupper
    · simp [cap, hwho]

/-- **Support-witness terminal-equilibrium compiler.**  A support-local
witness sequence, one genuine own-survival crossing, and a player-indexed
closed tail at the selected boundary produce a terminal `ε`-Nash profile.

This is the source-faithful replacement for the old all-player deleted-reach
package.  The marked player only needs joint reach; deleted reach is required
for the other players and is supplied automatically by the marked player's
own survival clock. -/
theorem exists_isεAsymptoticNash_of_hasQuittingSupportWitnessTailPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {ε : ℝ}
    (hpackage : HasQuittingSupportWitnessTailPackage reward ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile := by
  obtain ⟨plan, δ, ledgerCap, threshold, continuationSlack,
    hδ, hledgerCap, hthreshold, hcontinuationSlack, hscale,
    hsupport, hexists, htails, herror⟩ := hpackage
  let switch := quittingSupportSurvivalSwitchIndex plan threshold
  obtain ⟨hledger, hregret, target, hjoint, hother⟩ :=
    quittingSupportApproxNash_survivalSwitchPackage
      reward plan hδ hledgerCap hthreshold hscale hsupport hexists
  obtain ⟨tail, hclosed, halign⟩ := htails target
  obtain ⟨punishCap, hcapTarget, hpunish, hcapBound⟩ :=
    exists_quittingPhaseSwitchPunishCap_of_targetClosedTail
      reward tail target hclosed
  have htargetContinuation :
      punishCap target + 0 ≤
        quittingRootSequenceTerminalValue reward plan target switch +
          continuationSlack := by
    rw [hcapTarget]
    simpa [switch] using halign
  have hreachBound :
      0 ≤ threshold * quittingRewardBound reward :=
    mul_nonneg hthreshold.le (quittingRewardBound_nonneg reward)
  have htargetError :
      ((ledgerCap + δ) + δ + continuationSlack) +
          threshold * (2 * quittingRewardBound reward) ≤ ε := by
    nlinarith
  have hotherError : ∀ who : ι, who ≠ target →
      ((ledgerCap + δ) + δ +
          threshold * (5 * quittingRewardBound reward)) +
        threshold *
          (max (punishCap who + 0) 0 + quittingRewardBound reward) ≤ ε := by
    intro who _
    have hcapMax : max (punishCap who) 0 ≤ quittingRewardBound reward := by
      exact max_le (hcapBound who) (quittingRewardBound_nonneg reward)
    have htailFactor :
        max (punishCap who + 0) 0 + quittingRewardBound reward ≤
          2 * quittingRewardBound reward := by
      calc
        max (punishCap who + 0) 0 + quittingRewardBound reward ≤
            quittingRewardBound reward + quittingRewardBound reward := by
              simpa only [add_zero] using
                add_le_add hcapMax (le_refl (quittingRewardBound reward))
        _ = 2 * quittingRewardBound reward := by ring
    have hscaled := mul_le_mul_of_nonneg_left htailFactor hthreshold.le
    nlinarith
  refine ⟨quittingPhaseSwitchProfile reward plan tail switch, ?_⟩
  exact isεAsymptoticNash_quittingPhaseSwitchProfile_marked
    (reward := reward) (plan := plan) (punish := tail)
    (switch := switch) (target := target)
    (ledgerCap := ledgerCap + δ) (quitRegretCap := δ)
    (continuationSlack := continuationSlack)
    (targetJointReach := threshold) (otherReach := threshold)
    (punishError := 0) (bound := quittingRewardBound reward)
    (punishCap := punishCap)
    (quittingRewardBound_nonneg reward) hδ hcontinuationSlack
    (abs_reward_le_quittingRewardBound reward)
    hledger hregret
    (fun who hazard => by simpa using hpunish who hazard)
    htargetContinuation
    (by simpa [switch] using hjoint)
    (fun who hwho => by simpa [switch] using hother who hwho)
    htargetError hotherError

/-- Support-witness tail packages at every positive tolerance yield one
uniform-equilibrium payoff. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_supportWitnessTailPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpackage : ∀ ε : ℝ, 0 < ε →
      HasQuittingSupportWitnessTailPackage reward ε) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors reward
    fun ε hε =>
      exists_isεAsymptoticNash_of_hasQuittingSupportWitnessTailPackage
        reward (hpackage ε hε)

end GameTheory
