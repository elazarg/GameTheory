/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingTruncationLedgerFold
import GameTheory.Concepts.Stochastic.QuittingPhaseSwitchResiduals

/-!
# Marked-player phase-switch cap

The usual phase-switch cap asks for a small deleted opponent-survival weight
for every player.  Simon's phase-switch argument is asymmetric and does not
need that hypothesis for the punished player.  The punished player's
continuation is capped directly; the prefix ledger then prices the option of
continuing into that capped continuation.  Only the prescribed profile's
joint survival is needed to compare the original plan with the switched
profile.

This file formalises that missing marked-player branch.

* A pure quit strictly before the switch is unaffected by the punishment.
* A deviation which continues through the switch is bounded by the prefix
  ledger plus the gap between the punishment cap and the plan's continuation
  value at the switch.
* An arbitrary hazard reduces to those two shapes by infinite pure-time
  extremality.
* The resulting marked Nash consumer asks for joint survival for the marked
  player and deleted survival only for the other players.

The final two lemmas wire Simon's planned-survival clock into both required
survival bounds: the target's own survival controls the joint survival, while
`QuittingPhaseSwitchResiduals` already shows that it controls every other
player's deleted survival.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A deterministic quit strictly before the switch never observes the
punishment phase, so its payoff is exactly its payoff against the original
plan. -/
theorem quittingRootSequencePureTimeTerminalValue_quittingPhaseSwitchRoots_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    {quitTime : ℕ} (hquit : quitTime < switch) :
    quittingRootSequencePureTimeTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who (some quitTime) 0 =
      quittingRootSequencePureTimeTerminalValue reward plan who
        (some quitTime) 0 := by
  have htruncated :
      quittingTruncatedHazard (quittingPureTimeHazard (some quitTime)) switch =
        quittingPureTimeHazard (some quitTime) := by
    funext time
    by_cases htime : time < switch
    · rw [quittingTruncatedHazard_of_lt _ htime]
    · rw [quittingTruncatedHazard_of_le _ (Nat.not_lt.mp htime),
        quittingPureTimeHazard_some_of_ne (show time ≠ quitTime by omega)]
  have hdecomp :=
    quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots
      reward plan punish switch who (quittingPureTimeHazard (some quitTime))
  have hsurvival :=
    quittingJointSurvivalWeight_quittingRootSequenceUpdate_pureTime_eq_zero
      plan who hquit
  rw [htruncated, hsurvival, zero_mul, add_zero] at hdecomp
  have hplan :=
    quittingRootSequencePureTimeTerminalValue_quittingTruncatedRoots_of_lt
      reward plan who hquit
  simpa only [quittingRootSequencePureTimeTerminalValue] using hdecomp.trans hplan

/-- If a deviation surely continues throughout the plan prefix, then a cap on
its punishment continuation can be inserted directly at the switch.  Abel
summation prices the prefix ledger, and no deleted-survival estimate for the
marked player is used. -/
theorem
    quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_planValue_of_prefix_continue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    (hazard : ℕ → PMF Bool)
    {ledgerCap continuationSlack continuationCap : ℝ}
    (hcontinuationSlack : 0 ≤ continuationSlack)
    (hledger : ∀ index, index ≤ switch →
      quittingLedger reward plan who index ≤ ledgerCap)
    (hprefix : ∀ time, time < switch → hazard time = PMF.pure false)
    (hpunish :
      quittingRootSequenceHazardTerminalValue reward punish who
          (fun offset => hazard (switch + offset)) 0 ≤ continuationCap)
    (hcontinuation :
      continuationCap ≤
        quittingRootSequenceTerminalValue reward plan who switch +
          continuationSlack) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who hazard 0 ≤
      quittingRootSequenceTerminalValue reward plan who 0 +
        ledgerCap + continuationSlack := by
  have htruncated : quittingTruncatedHazard hazard switch =
      quittingAlwaysContinueHazard := by
    funext time
    by_cases htime : time < switch
    · rw [quittingTruncatedHazard_of_lt _ htime, hprefix time htime]
      rfl
    · rw [quittingTruncatedHazard_of_le _ (Nat.not_lt.mp htime)]
      rfl
  have hsurvival :
      quittingJointSurvivalWeight
          (quittingRootSequenceUpdate plan who hazard) 0 switch =
        quittingOpponentSurvivalWeight plan who 0 switch := by
    calc
      quittingJointSurvivalWeight
          (quittingRootSequenceUpdate plan who hazard) 0 switch =
          quittingJointSurvivalWeight
            (quittingRootSequenceUpdate plan who quittingAlwaysContinueHazard)
              0 switch := by
            refine quittingJointSurvivalWeight_congr _ _ 0 switch ?_
            intro offset hoffset
            simp [quittingRootSequenceUpdate, hprefix offset hoffset,
              quittingAlwaysContinueHazard]
      _ = quittingOpponentSurvivalWeight plan who 0 switch :=
        quittingJointSurvivalWeight_quittingRootSequenceUpdate_alwaysContinue
          plan who 0 switch
  have hdecomp :=
    quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots
      reward plan punish switch who hazard
  rw [htruncated, hsurvival] at hdecomp
  have hweight0 :
      0 ≤ quittingOpponentSurvivalWeight plan who 0 switch :=
    quittingOpponentSurvivalWeight_nonneg plan who 0 switch
  have htailTerm := mul_le_mul_of_nonneg_left hpunish hweight0
  have htransfer :=
    quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_alwaysContinue_eq_sub
      reward plan who switch
  have hcash :=
    quittingRootSequenceHazardTerminalValue_quittingAlwaysContinueHazard_sub_eq_ledgerSum
      reward plan who switch
  have hcore :
      quittingRootSequenceHazardTerminalValue reward
            (quittingTruncatedRoots plan switch) who
            quittingAlwaysContinueHazard 0 +
          quittingOpponentSurvivalWeight plan who 0 switch * continuationCap -
          quittingRootSequenceTerminalValue reward plan who 0 =
        (∑ stage ∈ Finset.range switch,
            quittingOpponentSurvivalWeight plan who 0 stage *
              quittingLedgerStageAdvantage reward plan who stage) +
          quittingOpponentSurvivalWeight plan who 0 switch *
            (continuationCap -
              quittingRootSequenceTerminalValue reward plan who switch) := by
    calc
      quittingRootSequenceHazardTerminalValue reward
              (quittingTruncatedRoots plan switch) who
              quittingAlwaysContinueHazard 0 +
            quittingOpponentSurvivalWeight plan who 0 switch * continuationCap -
            quittingRootSequenceTerminalValue reward plan who 0 =
          (quittingRootSequenceHazardTerminalValue reward plan who
              quittingAlwaysContinueHazard 0 -
            quittingOpponentSurvivalWeight plan who 0 switch *
              quittingRootSequenceTerminalValue reward
                (quittingRootSequenceUpdate plan who
                  quittingAlwaysContinueHazard) who switch) +
            quittingOpponentSurvivalWeight plan who 0 switch * continuationCap -
            quittingRootSequenceTerminalValue reward plan who 0 := by
              rw [htransfer]
      _ =
          (quittingRootSequenceHazardTerminalValue reward plan who
              quittingAlwaysContinueHazard 0 -
            quittingRootSequenceTerminalValue reward plan who 0) +
            quittingOpponentSurvivalWeight plan who 0 switch *
              (continuationCap -
                quittingRootSequenceTerminalValue reward
                  (quittingRootSequenceUpdate plan who
                    quittingAlwaysContinueHazard) who switch) := by ring
      _ =
          ((∑ stage ∈ Finset.range switch,
              quittingOpponentSurvivalWeight plan who 0 stage *
                quittingLedgerStageAdvantage reward plan who stage) +
            quittingOpponentSurvivalWeight plan who 0 switch *
              (quittingRootSequenceHazardTerminalValue reward plan who
                  quittingAlwaysContinueHazard switch -
                quittingRootSequenceTerminalValue reward plan who switch)) +
            quittingOpponentSurvivalWeight plan who 0 switch *
              (continuationCap -
                quittingRootSequenceTerminalValue reward
                  (quittingRootSequenceUpdate plan who
                    quittingAlwaysContinueHazard) who switch) := by
              rw [hcash]
      _ =
          (∑ stage ∈ Finset.range switch,
              quittingOpponentSurvivalWeight plan who 0 stage *
                quittingLedgerStageAdvantage reward plan who stage) +
            quittingOpponentSurvivalWeight plan who 0 switch *
              (continuationCap -
                quittingRootSequenceTerminalValue reward plan who switch) := by
              rw [quittingRootSequenceHazardTerminalValue]
              ring
  have habel := sum_mul_le_initialWeight_mul_of_partialSum_le
    (weight := quittingOpponentSurvivalWeight plan who 0)
    (summand := quittingLedgerStageAdvantage reward plan who) switch
    (fun stage => antitone_quittingOpponentSurvivalWeight plan who 0
      (Nat.le_succ stage))
    hweight0 hledger
  rw [show quittingOpponentSurvivalWeight plan who 0 0 = 1 by
    simp [quittingOpponentSurvivalWeight], one_mul] at habel
  have hweight1 :
      quittingOpponentSurvivalWeight plan who 0 switch ≤ 1 :=
    quittingOpponentSurvivalWeight_le_one_of_mass plan who 0 switch
  have htailDifference :
      continuationCap -
          quittingRootSequenceTerminalValue reward plan who switch ≤
        continuationSlack := by
    linarith
  have hscaledDifference :=
    mul_le_mul_of_nonneg_left htailDifference hweight0
  have hscaledSlack :
      quittingOpponentSurvivalWeight plan who 0 switch * continuationSlack ≤
        continuationSlack := by
    have hmissing := mul_nonneg
      (sub_nonneg.mpr hweight1) hcontinuationSlack
    nlinarith
  have hprefixCap :
      quittingRootSequenceHazardTerminalValue reward
            (quittingTruncatedRoots plan switch) who
            quittingAlwaysContinueHazard 0 +
          quittingOpponentSurvivalWeight plan who 0 switch * continuationCap ≤
        quittingRootSequenceTerminalValue reward plan who 0 +
          ledgerCap + continuationSlack := by
    nlinarith [hcore, habel, hscaledDifference, hscaledSlack]
  calc
    quittingRootSequenceHazardTerminalValue reward
          (quittingPhaseSwitchRoots plan punish switch) who hazard 0 =
        quittingRootSequenceHazardTerminalValue reward
            (quittingTruncatedRoots plan switch) who
            quittingAlwaysContinueHazard 0 +
          quittingOpponentSurvivalWeight plan who 0 switch *
            quittingRootSequenceHazardTerminalValue reward punish who
              (fun offset => hazard (switch + offset)) 0 := hdecomp
    _ ≤ quittingRootSequenceHazardTerminalValue reward
            (quittingTruncatedRoots plan switch) who
            quittingAlwaysContinueHazard 0 +
          quittingOpponentSurvivalWeight plan who 0 switch *
            continuationCap := add_le_add (le_refl _) htailTerm
    _ ≤ quittingRootSequenceTerminalValue reward plan who 0 +
          ledgerCap + continuationSlack := hprefixCap

local notation "phaseSwitchPrefixCap" =>
  quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_le_planValue_of_prefix_continue

/-- The marked player's arbitrary hazard is capped relative to the original
plan without any deleted-survival hypothesis.  Pure-time extremality splits
at the switch: early quit dates use the ledger and quit-regret cap; late quit
dates and Never use the continuation-aligned prefix lemma above. -/
theorem
    quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_marked_le_planValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    {ledgerCap quitRegretCap continuationSlack continuationCap : ℝ}
    (hquitRegretCap : 0 ≤ quitRegretCap)
    (hcontinuationSlack : 0 ≤ continuationSlack)
    (hledger : ∀ index, index ≤ switch →
      quittingLedger reward plan who index ≤ ledgerCap)
    (hregret : ∀ stage, stage < switch →
      quittingLedgerQuitRegret reward plan who stage ≤ quitRegretCap)
    (hpunish : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        continuationCap)
    (hcontinuation :
      continuationCap ≤
        quittingRootSequenceTerminalValue reward plan who switch +
          continuationSlack)
    (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who hazard 0 ≤
      quittingRootSequenceTerminalValue reward plan who 0 +
        (ledgerCap + quitRegretCap + continuationSlack) := by
  refine le_of_forall_pos_le_add fun slack hslack => ?_
  obtain ⟨quitTime, hquitTime⟩ :=
    exists_quittingRootSequencePureTimeTerminalValue_ge_sub
      reward (quittingPhaseSwitchRoots plan punish switch) who hazard hslack
  cases quitTime with
  | none =>
      have hprefix : ∀ time, time < switch →
          quittingPureTimeHazard none time = PMF.pure false := by
        intro time _
        rfl
      have hlate :=
        phaseSwitchPrefixCap
          reward plan punish switch who (quittingPureTimeHazard none)
          hcontinuationSlack hledger hprefix (hpunish _) hcontinuation
      simp only [quittingRootSequencePureTimeTerminalValue] at hquitTime
      linarith
  | some quitTime =>
      by_cases hquit : quitTime < switch
      · have hphase :=
          quittingRootSequencePureTimeTerminalValue_quittingPhaseSwitchRoots_of_lt
            reward plan punish switch who hquit
        have hplan :=
          quittingRootSequencePureTimeTerminalValue_some_le_of_ledger_le
            reward plan who quitTime hquitRegretCap
            (fun index hindex => hledger index (hindex.trans hquit.le))
            (hregret quitTime hquit)
        linarith
      · have hprefix : ∀ time, time < switch →
            quittingPureTimeHazard (some quitTime) time = PMF.pure false := by
          intro time htime
          exact quittingPureTimeHazard_some_of_ne (by omega)
        have hlate :=
          phaseSwitchPrefixCap
            reward plan punish switch who
            (quittingPureTimeHazard (some quitTime)) hcontinuationSlack
            hledger hprefix (hpunish _) hcontinuation
        simp only [quittingRootSequencePureTimeTerminalValue] at hquitTime
        linarith

omit [DecidableEq ι] in
/-- Replacing the plan tail by a punishment tail changes the prescribed value
by at most the plan's joint reach times twice the reward bound. -/
theorem quittingRootSequenceTerminalValue_plan_le_phaseSwitch_add_jointReach
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    {jointReach bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hjoint : quittingJointSurvivalWeight plan 0 switch ≤ jointReach) :
    quittingRootSequenceTerminalValue reward plan who 0 ≤
      quittingRootSequenceTerminalValue reward
          (quittingPhaseSwitchRoots plan punish switch) who 0 +
        jointReach * (2 * bound) := by
  have hplan :=
    quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
      reward plan who switch
  have hswitch :=
    quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots
      reward plan punish switch who
  have hplanTail :
      |quittingRootSequenceTerminalValue reward plan who switch| ≤ bound :=
    abs_quittingRootSequenceTerminalValue_le reward plan who switch hbound hreward
  have hpunishTail :
      |quittingRootSequenceTerminalValue reward punish who 0| ≤ bound :=
    abs_quittingRootSequenceTerminalValue_le reward punish who 0 hbound hreward
  rw [abs_le] at hplanTail hpunishTail
  have hsurvival0 : 0 ≤ quittingJointSurvivalWeight plan 0 switch :=
    quittingJointSurvivalWeight_nonneg plan 0 switch
  have htailDifference :
      quittingRootSequenceTerminalValue reward plan who switch -
          quittingRootSequenceTerminalValue reward punish who 0 ≤
        2 * bound := by
    linarith [hplanTail.2, hpunishTail.1]
  have hscaledDifference :=
    mul_le_mul_of_nonneg_left htailDifference hsurvival0
  have hscaledReach :
      quittingJointSurvivalWeight plan 0 switch * (2 * bound) ≤
        jointReach * (2 * bound) :=
    mul_le_mul_of_nonneg_right hjoint (by linarith)
  linarith [hplan, hswitch, hscaledDifference, hscaledReach]

/-- The complete marked-player cap, now measured against the actual switched
profile.  The only survival hypothesis for the marked player is the plan's
joint survival. -/
theorem quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_marked_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    {ledgerCap quitRegretCap continuationSlack continuationCap jointReach bound : ℝ}
    (hbound : 0 ≤ bound)
    (hquitRegretCap : 0 ≤ quitRegretCap)
    (hcontinuationSlack : 0 ≤ continuationSlack)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hledger : ∀ index, index ≤ switch →
      quittingLedger reward plan who index ≤ ledgerCap)
    (hregret : ∀ stage, stage < switch →
      quittingLedgerQuitRegret reward plan who stage ≤ quitRegretCap)
    (hpunish : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        continuationCap)
    (hcontinuation :
      continuationCap ≤
        quittingRootSequenceTerminalValue reward plan who switch +
          continuationSlack)
    (hjoint : quittingJointSurvivalWeight plan 0 switch ≤ jointReach)
    (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingPhaseSwitchRoots plan punish switch) who hazard 0 ≤
      quittingRootSequenceTerminalValue reward
          (quittingPhaseSwitchRoots plan punish switch) who 0 +
        ((ledgerCap + quitRegretCap + continuationSlack) +
          jointReach * (2 * bound)) := by
  have hplanCap :=
    quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_marked_le_planValue
      reward plan punish switch who hquitRegretCap hcontinuationSlack
      hledger hregret hpunish hcontinuation hazard
  have hcompare :=
    quittingRootSequenceTerminalValue_plan_le_phaseSwitch_add_jointReach
      reward plan punish switch who hbound hreward hjoint
  linarith

/-- Behaviour-strategy form of the marked-player cap. -/
theorem quittingTerminalPayoff_update_quittingPhaseSwitchProfile_marked_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (who : ι)
    {ledgerCap quitRegretCap continuationSlack continuationCap jointReach bound : ℝ}
    (hbound : 0 ≤ bound)
    (hquitRegretCap : 0 ≤ quitRegretCap)
    (hcontinuationSlack : 0 ≤ continuationSlack)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hledger : ∀ index, index ≤ switch →
      quittingLedger reward plan who index ≤ ledgerCap)
    (hregret : ∀ stage, stage < switch →
      quittingLedgerQuitRegret reward plan who stage ≤ quitRegretCap)
    (hpunish : ∀ g : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        continuationCap)
    (hcontinuation :
      continuationCap ≤
        quittingRootSequenceTerminalValue reward plan who switch +
          continuationSlack)
    (hjoint : quittingJointSurvivalWeight plan 0 switch ≤ jointReach)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update (quittingPhaseSwitchProfile reward plan punish switch)
          who deviation) who ≤
      quittingTerminalPayoff reward
          (quittingPhaseSwitchProfile reward plan punish switch) who +
        ((ledgerCap + quitRegretCap + continuationSlack) +
          jointReach * (2 * bound)) := by
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingProfileLiveRoot_quittingPhaseSwitchProfile]
  exact quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots_marked_le
    reward plan punish switch who hbound hquitRegretCap hcontinuationSlack
    hreward hledger hregret hpunish hcontinuation hjoint
    (quittingBehaviorLiveHazard reward deviation)

/-- A phase-switch profile is terminal approximate Nash when one marked player
is controlled by the marked cap and every other player is controlled by the
ordinary deleted-survival cap. -/
theorem isεAsymptoticNash_quittingPhaseSwitchProfile_marked
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan punish : ℕ → ι → PMF Bool) (switch : ℕ) (target : ι)
    {ledgerCap quitRegretCap continuationSlack targetJointReach otherReach
      punishError bound ε : ℝ}
    {punishCap : ι → ℝ}
    (hbound : 0 ≤ bound)
    (hquitRegretCap : 0 ≤ quitRegretCap)
    (hcontinuationSlack : 0 ≤ continuationSlack)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hledger : ∀ (who : ι) (index : ℕ), index ≤ switch →
      quittingLedger reward plan who index ≤ ledgerCap)
    (hregret : ∀ (who : ι) (stage : ℕ), stage < switch →
      quittingLedgerQuitRegret reward plan who stage ≤ quitRegretCap)
    (hpunish : ∀ (who : ι) (g : ℕ → PMF Bool),
      quittingRootSequenceHazardTerminalValue reward punish who g 0 ≤
        punishCap who + punishError)
    (htargetContinuation :
      punishCap target + punishError ≤
        quittingRootSequenceTerminalValue reward plan target switch +
          continuationSlack)
    (htargetJointReach :
      quittingJointSurvivalWeight plan 0 switch ≤ targetJointReach)
    (hotherReach : ∀ who : ι, who ≠ target →
      quittingOpponentSurvivalWeight plan who 0 switch ≤ otherReach)
    (htargetError :
      (ledgerCap + quitRegretCap + continuationSlack) +
          targetJointReach * (2 * bound) ≤ ε)
    (hotherError : ∀ who : ι, who ≠ target →
      (ledgerCap + quitRegretCap + otherReach * (5 * bound)) +
          otherReach *
            (max (punishCap who + punishError) 0 + bound) ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingPhaseSwitchProfile reward plan punish switch) := by
  intro who deviation
  by_cases hwho : who = target
  · subst who
    have hcap :=
      quittingTerminalPayoff_update_quittingPhaseSwitchProfile_marked_le
        reward plan punish switch target hbound hquitRegretCap
        hcontinuationSlack hreward (hledger target) (hregret target)
        (hpunish target) htargetContinuation htargetJointReach deviation
    linarith
  · have hcap :=
      quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le_of_plan_ledger_le
        reward plan punish switch who hbound hquitRegretCap hreward
        (hledger who) (hregret who) (hotherReach who hwho)
        (hpunish who) deviation
    linarith [hotherError who hwho]

omit [DecidableEq ι] in
/-- The full continue mass at one root is at most any selected player's own
continue probability. -/
theorem quittingStationaryContinueMass_le_ownContinueProbability
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryContinueMass root ≤ (root who false).toReal := by
  classical
  rw [quittingStationaryContinueMass_eq_deletedContinueMass_mul_own]
  all_goals
    have hdeleted1 :
        quittingRootDeletedContinueMass root who ≤ 1 :=
      quittingStationaryContinueMass_le_one
        (Function.update root who (PMF.pure false))
    have hmissing :
        0 ≤ (1 - quittingRootDeletedContinueMass root who) *
          (root who false).toReal :=
      mul_nonneg (sub_nonneg.mpr hdeleted1) ENNReal.toReal_nonneg
    nlinarith

omit [DecidableEq ι] in
/-- A player's own planned-survival curve bounds the plan's joint survival. -/
theorem quittingJointSurvivalWeight_le_quittingHazardSurvival_ownHazard
    (plan : ℕ → ι → PMF Bool) (who : ι) (fuel : ℕ) :
    quittingJointSurvivalWeight plan 0 fuel ≤
      quittingHazardSurvival (quittingRootSequenceOwnHazard plan who) fuel := by
  rw [quittingJointSurvivalWeight_eq_prod,
    quittingHazardSurvival_quittingRootSequenceOwnHazard]
  simp only [Nat.zero_add]
  apply Finset.prod_le_prod
  · intro offset _
    exact quittingStationaryContinueMass_nonneg (plan offset)
  · intro offset _
    exact quittingStationaryContinueMass_le_ownContinueProbability
      (plan offset) who

omit [DecidableEq ι] in
/-- At a target's planned-survival stopping index, the plan's joint survival
is below the same threshold. -/
theorem
    quittingJointSurvivalWeight_le_of_eq_quittingRootSequencePlannedSurvivalStoppingIndex
    (plan : ℕ → ι → PMF Bool) (target : ι) (threshold : ℝ) {switch : ℕ}
    (hswitch : switch =
      quittingRootSequencePlannedSurvivalStoppingIndex plan target threshold)
    (hexists : ∃ cutoff,
      quittingHazardSurvival (quittingRootSequenceOwnHazard plan target) cutoff ≤
        threshold) :
    quittingJointSurvivalWeight plan 0 switch ≤ threshold := by
  have hbound :=
    quittingHazardSurvival_quittingRootSequencePlannedSurvivalStoppingIndex_le
      plan target hexists
  rw [← hswitch] at hbound
  exact (quittingJointSurvivalWeight_le_quittingHazardSurvival_ownHazard
    plan target switch).trans hbound

/-- Simon's Case-2 clock supplies exactly the marked survival package: joint
survival for the target and deleted survival for every other player. -/
theorem quittingCaseTwoMarkedSurvivalBounds
    (plan : ℕ → ι → PMF Bool) (target : ι) (threshold : ℝ) {switch : ℕ}
    (hswitch : switch =
      quittingRootSequencePlannedSurvivalStoppingIndex plan target threshold)
    (hexists : ∃ cutoff,
      quittingHazardSurvival (quittingRootSequenceOwnHazard plan target) cutoff ≤
        threshold) :
    quittingJointSurvivalWeight plan 0 switch ≤ threshold ∧
      ∀ who : ι, who ≠ target →
        quittingOpponentSurvivalWeight plan who 0 switch ≤ threshold := by
  constructor
  · exact
      quittingJointSurvivalWeight_le_of_eq_quittingRootSequencePlannedSurvivalStoppingIndex
        plan target threshold hswitch hexists
  · exact quittingOpponentSurvivalWeight_le_of_target_plannedSurvivalStoppingIndex
      plan target threshold hswitch hexists

end GameTheory
