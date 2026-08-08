/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Marked.PhaseSwitchCap

/-!
# Support witnesses collapse Simon's ledger clock

A bare membership `next ∈ Fδ(current)` forgets which one-stage mixed action
witnesses the membership.  Simon's source correspondence carries the witness:
whenever an action is used with positive probability, that action is within
`δ` of the other endpoint.  Retaining this support-local information has a
strong consequence for the phase-switch proof.

For player `who` at stage `k`, write `q_k` for the prescribed Quit
probability and `D_k` for Quit minus Continue.  The ledger identity already
proved in `QuittingLedgerPunishClock` is

`ledgerIncrement_k = -q_k * D_k`.

The support condition `q_k > 0 -> D_k >= -δ` therefore gives

`ledgerIncrement_k <= δ * q_k`.

The elementary product--sum inequality

`(∏_{k<n} (1-q_k)) * (1 + ∑_{k<n} q_k) <= 1`

then implies the clock-collapse theorem: if own planned survival is still
strictly above `threshold` and `δ <= ledgerCap * threshold`, the ledger is
still strictly below `ledgerCap`.  Thus a ledger crossing forces an own
survival crossing.  No rank-one martingale or crossing-count estimate is
needed for a path that retains its support witness.

The final package uses the first stage at which *some* player's own survival
crosses the threshold.  Before that stage every ledger is below the cap; at
the stage itself every ledger is below `ledgerCap + δ`; and one selected
player supplies joint survival for itself and deleted survival for every
other player.  This is exactly the asymmetric survival interface consumed by
`QuittingMarkedPhaseSwitchCap`.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The support-local form of Simon's one-stage `Eδ` condition.  Every action
played with positive probability is within `δ` of the other endpoint. -/
def IsQuittingRootSupportApproxNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (δ : ℝ) (root : ι → PMF Bool) : Prop :=
  ∀ who,
    (0 < (root who true).toReal →
      -δ ≤ quittingRootEndpointDifference reward tail root who) ∧
    (0 < (root who false).toReal →
      quittingRootEndpointDifference reward tail root who ≤ δ)

/-- A root sequence retains a support-local witness at every stage, against
its actual continuation vector. -/
def IsQuittingRootSequenceSupportApproxNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (δ : ℝ) : Prop :=
  ∀ stage,
    IsQuittingRootSupportApproxNash reward
      (quittingRootSequenceTailVector reward roots (stage + 1)) δ
      (roots stage)

/-- The support-local condition implies the usual weighted endpoint
`δ`-Nash condition.  This direction loses the support information, which is
why the converse is not used for the clock-collapse argument. -/
theorem isQuittingRootEndpointNash_of_supportApproxNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsupport : IsQuittingRootSupportApproxNash reward tail δ root) :
    IsεQuittingRootEndpointNash reward tail δ root := by
  intro who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hcontinue0 : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  have hquit0 : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hcontinue1 : (root who false).toReal ≤ 1 := by linarith
  have hquit1 : (root who true).toReal ≤ 1 := by linarith
  constructor
  · by_cases hzero : (root who false).toReal = 0
    · rw [hzero, zero_mul]
      exact hδ
    · have hpositive : 0 < (root who false).toReal :=
        lt_of_le_of_ne hcontinue0 (Ne.symm hzero)
      have hgap := (hsupport who).2 hpositive
      have hscaled := mul_le_mul_of_nonneg_left hgap hcontinue0
      have hcontract : (root who false).toReal * δ ≤ δ :=
        mul_le_of_le_one_left hδ hcontinue1
      exact hscaled.trans hcontract
  · by_cases hzero : (root who true).toReal = 0
    · rw [hzero, zero_mul]
      linarith
    · have hpositive : 0 < (root who true).toReal :=
        lt_of_le_of_ne hquit0 (Ne.symm hzero)
      have hgap := (hsupport who).1 hpositive
      have hscaled := mul_le_mul_of_nonneg_left hgap hquit0
      have hfloor : -δ ≤ (root who true).toReal * (-δ) := by
        have hmissing :
            0 ≤ (1 - (root who true).toReal) * δ :=
          mul_nonneg (sub_nonneg.mpr hquit1) hδ
        nlinarith
      exact hfloor.trans hscaled

/-- Under a support witness, a stage's ledger charge is proportional to the
player's own prescribed Quit probability, rather than merely bounded by the
unweighted tolerance `δ`. -/
theorem quittingLedgerStageAdvantage_le_delta_mul_ownQuitProbability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ) {δ : ℝ}
    (hsupport : IsQuittingRootSupportApproxNash reward
      (quittingRootSequenceTailVector reward roots (stage + 1)) δ
      (roots stage)) :
    quittingLedgerStageAdvantage reward roots who stage ≤
      δ * (roots stage who true).toReal := by
  rw [quittingLedgerStageAdvantage_eq_neg_quitProbability_mul_endpointDifference]
  have hquit0 : 0 ≤ (roots stage who true).toReal := ENNReal.toReal_nonneg
  by_cases hzero : (roots stage who true).toReal = 0
  · simp [hzero]
  · have hpositive : 0 < (roots stage who true).toReal :=
      lt_of_le_of_ne hquit0 (Ne.symm hzero)
    have hgap := (hsupport who).1 hpositive
    have hnonneg :
        0 ≤ (roots stage who true).toReal *
          (quittingRootEndpointDifference reward
              (quittingRootSequenceTailVector reward roots (stage + 1))
              (roots stage) who + δ) :=
      mul_nonneg hquit0 (by linarith)
    nlinarith

/-- The cumulative ledger is bounded by `δ` times the cumulative prescribed
Quit probabilities of that player. -/
theorem quittingLedger_le_delta_mul_sum_ownQuitProbability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (index : ℕ) {δ : ℝ}
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward roots δ) :
    quittingLedger reward roots who index ≤
      δ * ∑ stage ∈ Finset.range index, (roots stage who true).toReal := by
  unfold quittingLedger
  calc
    (∑ stage ∈ Finset.range index,
        quittingLedgerStageAdvantage reward roots who stage) ≤
      ∑ stage ∈ Finset.range index,
        δ * (roots stage who true).toReal := by
          apply Finset.sum_le_sum
          intro stage _
          exact quittingLedgerStageAdvantage_le_delta_mul_ownQuitProbability
            reward roots who stage (hsupport stage)
    _ = δ * ∑ stage ∈ Finset.range index,
        (roots stage who true).toReal := by
          rw [Finset.mul_sum]

/-- The same support witness supplies the ordinary one-stage Quit-regret
bound consumed by the phase-switch compiler. -/
theorem quittingLedgerQuitRegret_le_of_supportApproxNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (stage : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward roots δ) :
    quittingLedgerQuitRegret reward roots who stage ≤ δ :=
  quittingLedgerQuitRegret_le_of_isεQuittingRootEndpointNash
    reward roots who stage
      (isQuittingRootEndpointNash_of_supportApproxNash reward _ _ hδ
        (hsupport stage))

/-- A finite Bernoulli survival product controls the unweighted sum of its
Quit probabilities. -/
theorem quittingHazardSurvival_mul_one_add_sum_quit_le_one
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingHazardSurvival hazard cutoff *
        (1 + ∑ time ∈ Finset.range cutoff,
          (hazard time true).toReal) ≤ 1 := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [quittingHazardSurvival_succ, Finset.sum_range_succ]
      have hsurvival0 := quittingHazardSurvival_nonneg hazard cutoff
      have hquit0 := quittingHazard_quit_nonneg hazard cutoff
      have hcontinue0 := quittingHazard_continue_nonneg hazard cutoff
      have hsum := quittingHazard_continue_add_quit hazard cutoff
      have hprefix0 :
          0 ≤ ∑ time ∈ Finset.range cutoff,
            (hazard time true).toReal := by
        apply Finset.sum_nonneg
        intro time _
        exact quittingHazard_quit_nonneg hazard time
      have hlocal :
          (hazard cutoff false).toReal *
              (1 + ((∑ time ∈ Finset.range cutoff,
                (hazard time true).toReal) +
                  (hazard cutoff true).toReal)) ≤
            1 + ∑ time ∈ Finset.range cutoff,
              (hazard time true).toReal := by
        have hcross := mul_nonneg hquit0 hprefix0
        have hsquare := sq_nonneg (hazard cutoff true).toReal
        nlinarith
      calc
        quittingHazardSurvival hazard cutoff *
              (hazard cutoff false).toReal *
              (1 + ((∑ time ∈ Finset.range cutoff,
                (hazard time true).toReal) +
                  (hazard cutoff true).toReal)) =
            quittingHazardSurvival hazard cutoff *
              ((hazard cutoff false).toReal *
                (1 + ((∑ time ∈ Finset.range cutoff,
                  (hazard time true).toReal) +
                    (hazard cutoff true).toReal))) := by ring
        _ ≤ quittingHazardSurvival hazard cutoff *
              (1 + ∑ time ∈ Finset.range cutoff,
                (hazard time true).toReal) :=
          mul_le_mul_of_nonneg_left hlocal hsurvival0
        _ ≤ 1 := ih

/-- **Clock collapse.**  While a player's own prescribed survival remains
strictly above `threshold`, its ledger remains strictly below `ledgerCap`,
provided the support tolerance is at most `ledgerCap * threshold`. -/
theorem quittingLedger_lt_of_supportApproxNash_of_threshold_lt_ownSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (index : ℕ)
    {δ ledgerCap threshold : ℝ}
    (hledgerCap : 0 < ledgerCap) (hthreshold : 0 < threshold)
    (hscale : δ ≤ ledgerCap * threshold)
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward roots δ)
    (hsurvival : threshold <
      quittingHazardSurvival (quittingRootSequenceOwnHazard roots who) index) :
    quittingLedger reward roots who index < ledgerCap := by
  let quitSum : ℝ :=
    ∑ stage ∈ Finset.range index, (roots stage who true).toReal
  have hquitSum0 : 0 ≤ quitSum := by
    dsimp only [quitSum]
    apply Finset.sum_nonneg
    intro stage _
    exact ENNReal.toReal_nonneg
  have hledger :=
    quittingLedger_le_delta_mul_sum_ownQuitProbability
      reward roots who index hsupport
  change quittingLedger reward roots who index ≤ δ * quitSum at hledger
  have hproduct :=
    quittingHazardSurvival_mul_one_add_sum_quit_le_one
      (quittingRootSequenceOwnHazard roots who) index
  change
    quittingHazardSurvival (quittingRootSequenceOwnHazard roots who) index *
        (1 + quitSum) ≤ 1 at hproduct
  have hone : 0 < 1 + quitSum := by linarith
  have hstrict := mul_lt_mul_of_pos_right hsurvival hone
  have hthresholdSum : threshold * quitSum < 1 := by
    nlinarith [hstrict, hproduct]
  have hscaleSum := mul_le_mul_of_nonneg_right hscale hquitSum0
  have hcap := mul_lt_mul_of_pos_left hthresholdSum hledgerCap
  calc
    quittingLedger reward roots who index ≤ δ * quitSum := hledger
    _ ≤ (ledgerCap * threshold) * quitSum := hscaleSum
    _ = ledgerCap * (threshold * quitSum) := by ring
    _ < ledgerCap * 1 := hcap
    _ = ledgerCap := by ring

/-- Contrapositive form: every ledger crossing forces the same player's own
survival to have crossed the selected threshold. -/
theorem quittingHazardSurvival_own_le_of_supportApproxNash_of_ledger_crossing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (index : ℕ)
    {δ ledgerCap threshold : ℝ}
    (hledgerCap : 0 < ledgerCap) (hthreshold : 0 < threshold)
    (hscale : δ ≤ ledgerCap * threshold)
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward roots δ)
    (hcross : ledgerCap ≤ quittingLedger reward roots who index) :
    quittingHazardSurvival (quittingRootSequenceOwnHazard roots who) index ≤
      threshold := by
  by_contra hnot
  have hsurvival : threshold <
      quittingHazardSurvival (quittingRootSequenceOwnHazard roots who) index :=
    lt_of_not_ge hnot
  have hledger :=
    quittingLedger_lt_of_supportApproxNash_of_threshold_lt_ownSurvival
      reward roots who index hledgerCap hthreshold hscale hsupport hsurvival
  exact (not_lt_of_ge hcross) hledger

/-- Consequently, whenever both clocks genuinely fire, the own-survival
clock is no later than the ledger clock. -/
theorem
    quittingRootSequencePlannedSurvivalStoppingIndex_le_ledgerStoppingIndex_of_supportApproxNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {δ ledgerCap threshold : ℝ}
    (hledgerCap : 0 < ledgerCap) (hthreshold : 0 < threshold)
    (hscale : δ ≤ ledgerCap * threshold)
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward roots δ)
    (hledgerExists : ∃ index,
      ledgerCap ≤ quittingLedger reward roots who index)
    (hsurvivalExists : ∃ index,
      quittingHazardSurvival (quittingRootSequenceOwnHazard roots who) index ≤
        threshold) :
    quittingRootSequencePlannedSurvivalStoppingIndex roots who threshold ≤
      quittingLedgerStoppingIndex reward roots who ledgerCap := by
  have hcross := le_quittingLedger_quittingLedgerStoppingIndex
    reward roots who hledgerExists
  have hsurvival :=
    quittingHazardSurvival_own_le_of_supportApproxNash_of_ledger_crossing
      reward roots who
        (quittingLedgerStoppingIndex reward roots who ledgerCap)
        hledgerCap hthreshold hscale hsupport hcross
  unfold quittingRootSequencePlannedSurvivalStoppingIndex
  unfold quittingPlannedSurvivalStoppingIndex
  rw [dif_pos hsurvivalExists]
  exact Nat.find_min' hsurvivalExists hsurvival

/-- The first stage at which at least one player's own planned survival is at
or below `threshold`, or `0` if no such stage exists.  This global clock does
not confuse a non-firing per-player clock with a genuine crossing at stage
zero. -/
def quittingSupportSurvivalSwitchIndex
    (roots : ℕ → ι → PMF Bool) (threshold : ℝ) : ℕ := by
  classical
  exact
    if hexists : ∃ index, ∃ who,
        quittingHazardSurvival
          (quittingRootSequenceOwnHazard roots who) index ≤ threshold then
      Nat.find hexists
    else 0

omit [DecidableEq ι] in
/-- At a genuine global support-survival switch, some player supplies the
threshold crossing. -/
theorem exists_ownSurvival_le_quittingSupportSurvivalSwitchIndex
    (roots : ℕ → ι → PMF Bool) (threshold : ℝ)
    (hexists : ∃ index, ∃ who,
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard roots who) index ≤ threshold) :
    ∃ who,
      quittingHazardSurvival (quittingRootSequenceOwnHazard roots who)
          (quittingSupportSurvivalSwitchIndex roots threshold) ≤ threshold := by
  unfold quittingSupportSurvivalSwitchIndex
  rw [dif_pos hexists]
  exact Nat.find_spec hexists

omit [DecidableEq ι] in
/-- Before the global switch, every player's own survival is still strictly
above the threshold. -/
theorem threshold_lt_ownSurvival_of_lt_quittingSupportSurvivalSwitchIndex
    (roots : ℕ → ι → PMF Bool) (threshold : ℝ)
    (hexists : ∃ index, ∃ who,
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard roots who) index ≤ threshold)
    (who : ι) {stage : ℕ}
    (hstage : stage < quittingSupportSurvivalSwitchIndex roots threshold) :
    threshold <
      quittingHazardSurvival (quittingRootSequenceOwnHazard roots who) stage := by
  unfold quittingSupportSurvivalSwitchIndex at hstage
  rw [dif_pos hexists] at hstage
  by_contra hnot
  have hle :
      quittingHazardSurvival (quittingRootSequenceOwnHazard roots who) stage ≤
        threshold := le_of_not_gt hnot
  exact (Nat.find_min hexists hstage) ⟨who, hle⟩

/-- Every player's ledger is strictly below `ledgerCap` before the global
support-survival switch. -/
theorem quittingLedger_lt_of_lt_quittingSupportSurvivalSwitchIndex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {index : ℕ}
    {δ ledgerCap threshold : ℝ}
    (hledgerCap : 0 < ledgerCap) (hthreshold : 0 < threshold)
    (hscale : δ ≤ ledgerCap * threshold)
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward roots δ)
    (hexists : ∃ cutoff, ∃ player,
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard roots player) cutoff ≤ threshold)
    (hindex : index < quittingSupportSurvivalSwitchIndex roots threshold) :
    quittingLedger reward roots who index < ledgerCap :=
  quittingLedger_lt_of_supportApproxNash_of_threshold_lt_ownSurvival
    reward roots who index hledgerCap hthreshold hscale hsupport
      (threshold_lt_ownSurvival_of_lt_quittingSupportSurvivalSwitchIndex
        roots threshold hexists who hindex)

/-- At the switch itself, the one final support-local ledger charge costs at
most one further `δ`. -/
theorem quittingLedger_le_cap_add_delta_at_quittingSupportSurvivalSwitchIndex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {δ ledgerCap threshold : ℝ}
    (hδ : 0 ≤ δ) (hledgerCap : 0 < ledgerCap)
    (hthreshold : 0 < threshold)
    (hscale : δ ≤ ledgerCap * threshold)
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward roots δ)
    (hexists : ∃ cutoff, ∃ player,
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard roots player) cutoff ≤ threshold) :
    quittingLedger reward roots who
        (quittingSupportSurvivalSwitchIndex roots threshold) ≤
      ledgerCap + δ := by
  rcases Nat.eq_zero_or_pos
      (quittingSupportSurvivalSwitchIndex roots threshold) with hzero | hpositive
  · rw [hzero, quittingLedger_zero]
    linarith
  · obtain ⟨previous, hswitch⟩ :=
      Nat.exists_eq_succ_of_ne_zero hpositive.ne'
    have hprevious : previous <
        quittingSupportSurvivalSwitchIndex roots threshold := by omega
    have hledger :=
      quittingLedger_lt_of_lt_quittingSupportSurvivalSwitchIndex
        reward roots who hledgerCap hthreshold hscale hsupport hexists hprevious
    have hstage :=
      quittingLedgerStageAdvantage_le_delta_mul_ownQuitProbability
        reward roots who previous (hsupport previous)
    have hsum :=
      quittingRoot_continueProbability_add_quitProbability (roots previous) who
    have hcontinue0 : 0 ≤ (roots previous who false).toReal :=
      ENNReal.toReal_nonneg
    have hquit1 : (roots previous who true).toReal ≤ 1 := by linarith
    have hstep :
        δ * (roots previous who true).toReal ≤ δ :=
      mul_le_of_le_one_right hδ hquit1
    rw [hswitch, Nat.succ_eq_add_one, quittingLedger_succ]
    linarith

/-- The global switch selects one marked player whose own survival bounds the
plan's joint survival, while bounding every other player's deleted survival. -/
theorem exists_target_survivalBounds_at_quittingSupportSurvivalSwitchIndex
    (roots : ℕ → ι → PMF Bool) (threshold : ℝ)
    (hexists : ∃ cutoff, ∃ player,
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard roots player) cutoff ≤ threshold) :
    ∃ target,
      quittingJointSurvivalWeight roots 0
          (quittingSupportSurvivalSwitchIndex roots threshold) ≤ threshold ∧
      ∀ who : ι, who ≠ target →
        quittingOpponentSurvivalWeight roots who 0
          (quittingSupportSurvivalSwitchIndex roots threshold) ≤ threshold := by
  obtain ⟨target, htarget⟩ :=
    exists_ownSurvival_le_quittingSupportSurvivalSwitchIndex
      roots threshold hexists
  refine ⟨target, ?_, ?_⟩
  · exact
      (quittingJointSurvivalWeight_le_quittingHazardSurvival_ownHazard
        roots target (quittingSupportSurvivalSwitchIndex roots threshold)).trans
          htarget
  · intro who hwho
    exact
      (quittingOpponentSurvivalWeight_le_quittingHazardSurvival_ownHazard
        roots hwho.symm
          (quittingSupportSurvivalSwitchIndex roots threshold)).trans htarget

/-- **Support-witness switch package.**  One witness-carrying root sequence
and one genuine own-survival crossing simultaneously supply:

* every ledger cap through the switch, with one `δ` overshoot;
* every pre-switch one-stage Quit-regret cap;
* a marked target with joint reach at most `threshold`; and
* deleted reach at most `threshold` for every other player.

This is the deterministic replacement for Simon's Case-1/Case-2 split. -/
theorem quittingSupportApproxNash_survivalSwitchPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    {δ ledgerCap threshold : ℝ}
    (hδ : 0 ≤ δ) (hledgerCap : 0 < ledgerCap)
    (hthreshold : 0 < threshold)
    (hscale : δ ≤ ledgerCap * threshold)
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward roots δ)
    (hexists : ∃ cutoff, ∃ player,
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard roots player) cutoff ≤ threshold) :
    (∀ who index, index ≤ quittingSupportSurvivalSwitchIndex roots threshold →
      quittingLedger reward roots who index ≤ ledgerCap + δ) ∧
    (∀ who stage, stage < quittingSupportSurvivalSwitchIndex roots threshold →
      quittingLedgerQuitRegret reward roots who stage ≤ δ) ∧
    ∃ target,
      quittingJointSurvivalWeight roots 0
          (quittingSupportSurvivalSwitchIndex roots threshold) ≤ threshold ∧
      ∀ who : ι, who ≠ target →
        quittingOpponentSurvivalWeight roots who 0
          (quittingSupportSurvivalSwitchIndex roots threshold) ≤ threshold := by
  refine ⟨?_, ?_,
    exists_target_survivalBounds_at_quittingSupportSurvivalSwitchIndex
      roots threshold hexists⟩
  · intro who index hindex
    by_cases hstrict : index <
        quittingSupportSurvivalSwitchIndex roots threshold
    · exact le_trans
        (le_of_lt (quittingLedger_lt_of_lt_quittingSupportSurvivalSwitchIndex
          reward roots who hledgerCap hthreshold hscale hsupport hexists hstrict))
        (by linarith)
    · have heq : index =
          quittingSupportSurvivalSwitchIndex roots threshold := by omega
      rw [heq]
      exact quittingLedger_le_cap_add_delta_at_quittingSupportSurvivalSwitchIndex
        reward roots who hδ hledgerCap hthreshold hscale hsupport hexists
  · intro who stage _
    exact quittingLedgerQuitRegret_le_of_supportApproxNash
      reward roots who stage hδ hsupport

end GameTheory
