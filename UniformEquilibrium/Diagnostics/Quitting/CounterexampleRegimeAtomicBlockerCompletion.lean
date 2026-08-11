/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Punishment.InstantPunishment
import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix

/-!
# Atomic completion of a forced-owner row

Fix an owner whose date-zero action is sure Quit.  The other players then
face a finite normal-form game on the product root: the continuation is never
reached when any outsider deviates, because the owner still quits surely.
If their displayed product row is Nash in that finite game, attaching an
owner-specific near-minimax punishment after the all-Continue outcome gives
every outsider zero literal behavioral debt.  The owner's only possible gain
is the exact refusal balance, plus the probability of reaching the punishment
tail times its approximation error.

This is the atomic blocker-completion reduction.  It does not assert that a
forced-owner Nash row with nonnegative balance exists; that is the remaining
finite support-enlargement problem.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A mixed Nash row of the finite game in which `owner` is forced to Quit.
The first conjunct records the forced action.  The second is exact Nash only
for outsiders; changing an outsider's marginal leaves the owner surely
quitting, so the zero continuation is the literal one-shot payoff. -/
def IsQuittingForcedOwnerNashRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (root : ι → PMF Bool) : Prop :=
  root owner = PMF.pure true ∧
    ∀ who, who ≠ owner → ∀ deviation : PMF Bool,
      quittingRootExpectedPayoff reward 0
          (Function.update root who deviation) who ≤
        quittingRootExpectedPayoff reward 0 root who

/-- Probability that every outsider Continues in the forced-owner row. -/
def quittingForcedOwnerAllOutsidersContinueMass
    (root : ι → PMF Bool) (owner : ι) : ℝ :=
  quittingStationaryFixedOpponentsContinueMass root owner

/-- The owner's payoff when it obeys and Quits at date zero. -/
def quittingForcedOwnerObeyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) : ℝ :=
  quittingRootAbsorbingContribution reward root owner

/-- The owner's refusal cap when the punishment continuation is evaluated at
the behavioral punishment value. -/
def quittingForcedOwnerRefusalCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) : ℝ :=
  quittingStationaryFixedOpponentsContinueReward reward root owner +
    quittingForcedOwnerAllOutsidersContinueMass root owner *
      quittingPunishmentValue reward owner

/-- Obedience minus refusal: the exact atomic blocker balance. -/
def quittingAtomicBlockerBalance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) : ℝ :=
  quittingForcedOwnerObeyValue reward root owner -
    quittingForcedOwnerRefusalCap reward root owner

/-- Error of the atomic completion using an `ε`-optimal punishment row. -/
def quittingAtomicBlockerCompletionError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) (ε : ℝ) : ℝ :=
  max 0 (-quittingAtomicBlockerBalance reward root owner +
    quittingForcedOwnerAllOutsidersContinueMass root owner * ε)

theorem IsQuittingForcedOwnerNashRow.hasSureQuitter
    {owner : ι} {root : ι → PMF Bool}
    (hrow : IsQuittingForcedOwnerNashRow reward owner root) :
    QuittingRootHasSureQuitter root :=
  ⟨owner, hrow.1⟩

theorem IsQuittingForcedOwnerNashRow.continueMass_eq_zero
    {owner : ι} {root : ι → PMF Bool}
    (hrow : IsQuittingForcedOwnerNashRow reward owner root) :
    quittingStationaryContinueMass root = 0 := by
  unfold quittingStationaryContinueMass
  have hzero :=
    (quittingRootHasSureQuitter_iff_allContinue_mass_zero root).mp
      hrow.hasSureQuitter
  rw [show (quittingAllContinueAction : ι → Bool) =
      (fun _ => false) by rfl, hzero]
  simp

/-- An outsider deviation still faces the surely quitting owner, so the
probability of reaching any continuation is zero. -/
theorem IsQuittingForcedOwnerNashRow.outsiderContinueMass_eq_zero
    {owner who : ι} {root : ι → PMF Bool}
    (hrow : IsQuittingForcedOwnerNashRow reward owner root)
    (hwho : who ≠ owner) :
    quittingStationaryFixedOpponentsContinueMass root who = 0 := by
  have hle := quittingStationaryContinueMass_le_ownContinueProbability
    (Function.update root who (PMF.pure false)) owner
  have howner :
      Function.update root who (PMF.pure false) owner = PMF.pure true := by
    rw [Function.update_of_ne (Ne.symm hwho)]
    exact hrow.1
  rw [howner] at hle
  have hnonneg := quittingStationaryFixedOpponentsContinueMass_nonneg root who
  change quittingStationaryContinueMass
      (Function.update root who (PMF.pure false)) = 0
  change 0 ≤ quittingStationaryContinueMass
      (Function.update root who (PMF.pure false)) at hnonneg
  simpa using le_antisymm (by simpa using hle) hnonneg

/-- The literal one-stage punished profile absorbs at date zero and therefore
pays the forced-owner row's absorbing contribution to every player. -/
theorem quittingTerminalPayoff_atomicBlockerCompletion
    {owner : ι} {root punishRow : ι → PMF Bool}
    (hrow : IsQuittingForcedOwnerNashRow reward owner root) (who : ι) :
    quittingTerminalPayoff reward
        (quittingOneStagePunishedProfile reward root punishRow) who =
      quittingRootAbsorbingContribution reward root who :=
  quittingTerminalPayoff_oneStagePunishedProfile reward root punishRow who
    hrow.continueMass_eq_zero

/-- Every arbitrary behavioral deviation of an outsider is bounded by its
prescribed forced-owner payoff.  The punishment tail is irrelevant because
the surely quitting owner makes the deviated date-zero row absorbing. -/
theorem quittingTerminalPayoff_update_atomicBlockerCompletion_outsider_le
    {owner who : ι} {root punishRow : ι → PMF Bool}
    (hrow : IsQuittingForcedOwnerNashRow reward owner root)
    (hwho : who ≠ owner)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingOneStagePunishedProfile reward root punishRow)
          who deviation) who ≤
      quittingRootAbsorbingContribution reward root who := by
  have hcap := quittingTerminalPayoff_update_oneStagePunishedProfile_le
    reward root punishRow who deviation
  have hquit := hrow.2 who hwho (PMF.pure true)
  have hcontinue := hrow.2 who hwho (PMF.pure false)
  have hquit' : quittingStationaryFixedOpponentsQuitValue reward root who ≤
      quittingRootAbsorbingContribution reward root who := by
    simpa [quittingStationaryFixedOpponentsQuitValue,
      quittingFixedOpponentsQuitValue,
      quittingRootAbsorbingContribution] using hquit
  have hcontinue' :
      quittingStationaryFixedOpponentsContinueReward reward root who ≤
        quittingRootAbsorbingContribution reward root who := by
    simpa [quittingStationaryFixedOpponentsContinueReward,
      quittingFixedOpponentsContinueReward,
      quittingRootAbsorbingContribution] using hcontinue
  rw [hrow.outsiderContinueMass_eq_zero hwho, zero_mul, add_zero] at hcap
  exact hcap.trans (max_le hquit' hcontinue')

/-- Every arbitrary behavioral deviation of the owner is bounded by the
atomic blocker-completion error above its obedience payoff. -/
theorem quittingTerminalPayoff_update_atomicBlockerCompletion_owner_le
    {owner : ι} {root punishRow : ι → PMF Bool}
    (hrow : IsQuittingForcedOwnerNashRow reward owner root)
    {ε : ℝ}
    (hpunish : quittingStationaryUnilateralCap reward punishRow owner ≤
      quittingPunishmentValue reward owner + ε)
    (deviation : (quittingGame reward).BehaviorStrategy owner) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingOneStagePunishedProfile reward root punishRow)
          owner deviation) owner ≤
      quittingForcedOwnerObeyValue reward root owner +
        quittingAtomicBlockerCompletionError reward root owner ε := by
  have hcap := quittingTerminalPayoff_update_oneStagePunishedProfile_le
    reward root punishRow owner deviation
  have hupdate : Function.update root owner (PMF.pure true) = root := by
    rw [← hrow.1, Function.update_eq_self]
  have hquit : quittingStationaryFixedOpponentsQuitValue reward root owner =
      quittingForcedOwnerObeyValue reward root owner := by
    simp only [quittingStationaryFixedOpponentsQuitValue,
      quittingFixedOpponentsQuitValue]
    rw [hupdate]
    rfl
  have hp0 : 0 ≤ quittingForcedOwnerAllOutsidersContinueMass root owner :=
    quittingStationaryFixedOpponentsContinueMass_nonneg root owner
  have hscaled := mul_le_mul_of_nonneg_left hpunish hp0
  have herror0 : 0 ≤
      quittingAtomicBlockerCompletionError reward root owner ε :=
    le_max_left _ _
  have herrorBalance :
      -quittingAtomicBlockerBalance reward root owner +
          quittingForcedOwnerAllOutsidersContinueMass root owner * ε ≤
        quittingAtomicBlockerCompletionError reward root owner ε :=
    le_max_right _ _
  rw [hquit] at hcap
  refine hcap.trans (max_le (le_add_of_nonneg_right herror0) ?_)
  unfold quittingAtomicBlockerBalance at herrorBalance
  unfold quittingForcedOwnerRefusalCap at herrorBalance
  change quittingStationaryFixedOpponentsContinueReward reward root owner +
      quittingForcedOwnerAllOutsidersContinueMass root owner *
        quittingStationaryUnilateralCap reward punishRow owner ≤
    quittingForcedOwnerObeyValue reward root owner +
      quittingAtomicBlockerCompletionError reward root owner ε
  nlinarith

/-- Outsiders have exactly zero full behavioral best-response debt in the
atomic completion. -/
theorem quittingTerminalDeviationDebt_atomicBlockerCompletion_outsider_eq_zero
    {owner who : ι} {root punishRow : ι → PMF Bool}
    (hrow : IsQuittingForcedOwnerNashRow reward owner root)
    (hwho : who ≠ owner) :
    quittingTerminalDeviationDebt reward
        (quittingOneStagePunishedProfile reward root punishRow) who = 0 := by
  let profile := quittingOneStagePunishedProfile reward root punishRow
  let value := quittingRootAbsorbingContribution reward root who
  have hupper : quittingContinuationBestResponseValue reward profile who ≤
      value := by
    unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨quittingTerminalPayoff reward profile who,
        ⟨profile who, by
          change quittingTerminalPayoff reward
            (Function.update profile who (profile who)) who = _
          rw [Function.update_eq_self]⟩⟩
    rintro payoff ⟨deviation, rfl⟩
    exact quittingTerminalPayoff_update_atomicBlockerCompletion_outsider_le
      hrow hwho deviation
  have hvalue : quittingTerminalPayoff reward profile who = value :=
    quittingTerminalPayoff_atomicBlockerCompletion hrow who
  have hnonneg := quittingTerminalDeviationDebt_nonneg reward profile who
    (quittingRewardBound_nonneg reward)
    (abs_reward_le_quittingRewardBound reward)
  unfold quittingTerminalDeviationDebt at hnonneg ⊢
  linarith

/-- The owner's full behavioral debt is at most the exact blocker error. -/
theorem quittingTerminalDeviationDebt_atomicBlockerCompletion_owner_le
    {owner : ι} {root punishRow : ι → PMF Bool}
    (hrow : IsQuittingForcedOwnerNashRow reward owner root)
    {ε : ℝ}
    (hpunish : quittingStationaryUnilateralCap reward punishRow owner ≤
      quittingPunishmentValue reward owner + ε) :
    quittingTerminalDeviationDebt reward
        (quittingOneStagePunishedProfile reward root punishRow) owner ≤
      quittingAtomicBlockerCompletionError reward root owner ε := by
  let profile := quittingOneStagePunishedProfile reward root punishRow
  let value := quittingForcedOwnerObeyValue reward root owner
  let error := quittingAtomicBlockerCompletionError reward root owner ε
  have hupper : quittingContinuationBestResponseValue reward profile owner ≤
      value + error := by
    unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨quittingTerminalPayoff reward profile owner,
        ⟨profile owner, by
          change quittingTerminalPayoff reward
            (Function.update profile owner (profile owner)) owner = _
          rw [Function.update_eq_self]⟩⟩
    rintro payoff ⟨deviation, rfl⟩
    exact quittingTerminalPayoff_update_atomicBlockerCompletion_owner_le
      hrow hpunish deviation
  have hvalue : quittingTerminalPayoff reward profile owner = value :=
    quittingTerminalPayoff_atomicBlockerCompletion hrow owner
  unfold quittingTerminalDeviationDebt
  dsimp only [profile, value, error] at hupper hvalue ⊢
  linarith

/-- Every positive accuracy admits the literal atomic completion with zero
outsider debt and the stated owner-debt bound. -/
theorem exists_quittingAtomicBlockerCompletion
    {owner : ι} {root : ι → PMF Bool}
    (hrow : IsQuittingForcedOwnerNashRow reward owner root)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ punishRow : ι → PMF Bool,
      (∀ who, who ≠ owner →
        quittingTerminalDeviationDebt reward
          (quittingOneStagePunishedProfile reward root punishRow) who = 0) ∧
      quittingTerminalDeviationDebt reward
          (quittingOneStagePunishedProfile reward root punishRow) owner ≤
        quittingAtomicBlockerCompletionError reward root owner ε := by
  obtain ⟨punishRow, hpunish⟩ :=
    exists_quittingStationaryPunishmentRoot_lt_add reward owner hε
  exact ⟨punishRow,
    fun who hwho =>
      quittingTerminalDeviationDebt_atomicBlockerCompletion_outsider_eq_zero
        hrow hwho,
    quittingTerminalDeviationDebt_atomicBlockerCompletion_owner_le
      hrow hpunish.le⟩

/-- A positive global terminal-exploitability floor forces every forced-owner
Nash row to have blocker balance at most the negative floor. -/
theorem quittingAtomicBlockerBalance_le_neg_of_terminalExploitabilityGap
    {owner : ι} {root : ι → PMF Bool} {η : ℝ}
    (hrow : IsQuittingForcedOwnerNashRow reward owner root)
    (hη : 0 < η) (hgap : HasTerminalExploitabilityGap reward η) :
    quittingAtomicBlockerBalance reward root owner ≤ -η := by
  by_contra hnot
  have hstrict : 0 < η + quittingAtomicBlockerBalance reward root owner := by
    linarith
  let ε := (η + quittingAtomicBlockerBalance reward root owner) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨punishRow, houtsiderDebt, hownerDebt⟩ :=
    exists_quittingAtomicBlockerCompletion hrow hε
  let profile := quittingOneStagePunishedProfile reward root punishRow
  obtain ⟨who, deviation, hexploit⟩ := hgap profile
  have hM := quittingRewardBound_nonneg reward
  have hreward := abs_reward_le_quittingRewardBound reward
  have hdeviationBest :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile who deviation hM hreward
  have hp0_le :
      quittingForcedOwnerAllOutsidersContinueMass root owner ≤ 1 :=
    quittingStationaryFixedOpponentsContinueMass_le_one root owner
  have hη_le_error : η ≤
      quittingAtomicBlockerCompletionError reward root owner ε := by
    by_cases hwho : who = owner
    · subst who
      unfold quittingTerminalDeviationDebt at hownerDebt
      linarith
    · have hzero := houtsiderDebt who hwho
      unfold quittingTerminalDeviationDebt at hzero
      linarith
  unfold quittingAtomicBlockerCompletionError at hη_le_error
  dsimp [ε] at hη_le_error
  have hinside_lt :
      -quittingAtomicBlockerBalance reward root owner +
          quittingForcedOwnerAllOutsidersContinueMass root owner *
            ((η + quittingAtomicBlockerBalance reward root owner) / 2) < η := by
    nlinarith [mul_le_mul_of_nonneg_right hp0_le hstrict.le]
  have hmax_lt :
      max 0
        (-quittingAtomicBlockerBalance reward root owner +
          quittingForcedOwnerAllOutsidersContinueMass root owner *
            ((η + quittingAtomicBlockerBalance reward root owner) / 2)) < η :=
    max_lt hη hinside_lt
  linarith

namespace QuittingCounterexampleRegime

/-- Counterexample-regime form of the atomic blocker obstruction. -/
theorem quittingAtomicBlockerBalance_le_neg_terminalGap
    (regime : QuittingCounterexampleRegime reward)
    {owner : ι} {root : ι → PMF Bool}
    (hrow : IsQuittingForcedOwnerNashRow reward owner root) :
    quittingAtomicBlockerBalance reward root owner ≤ -regime.terminalGap :=
  quittingAtomicBlockerBalance_le_neg_of_terminalExploitabilityGap hrow
    regime.terminalGap_pos regime.terminalExploitability

end QuittingCounterexampleRegime

end GameTheory
