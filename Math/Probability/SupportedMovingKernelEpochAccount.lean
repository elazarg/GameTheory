/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.MovingKernelEpochPotentialAccount
import Math.ProbabilityMassFunction

/-!
# Support-sensitive potential accounts for moving kernels

The pointwise drift inequality used by a moving-kernel potential account may
only be available on states that support the current marginal law.  This file
isolates the exact weaker input needed by the telescope: an expected one-step
drift inequality along that law.

The inequality is allowed to start after a fixed epoch.  Earlier epochs are
paid by explicit finite sums of absolute expected costs.  Thus the resulting
completed/current budget is valid at every horizon, including horizons inside
an early epoch, while its asymptotic rate is governed only by the tail
potential bills.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter Math.OnlineLearning

variable {S : Type*} [Fintype S]

/-- The explicit bill for an epoch before the eventual drift estimate starts.
It pays the absolute expected cost of every stage in the epoch. -/
def earlyEpochExpectedCostBill
    (law : ℕ → PMF S) (cost : ℕ → S → ℝ) (epoch : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range (anytimeEpochLength epoch),
    |expect
      (law (epochStart anytimeEpochLength epoch + offset))
      (cost epoch)|

/-- Before `startEpoch`, pay the explicit expected-cost bill.  From
`startEpoch` onward, pay the finite-state potential bill. -/
def supportedMovingKernelEpochBill
    (law : ℕ → PMF S) (cost potential : ℕ → S → ℝ)
    (startEpoch epoch : ℕ) : ℝ :=
  if epoch < startEpoch then
    earlyEpochExpectedCostBill law cost epoch
  else
    epochPotentialBill potential epoch

omit [Fintype S] in
private theorem expect_le_expect_of_le_on_support
    [Finite S]
    (law : PMF S) (left right : S → ℝ)
    (le_on_support :
      ∀ state, state ∈ law.support → left state ≤ right state) :
    expect law left ≤ expect law right := by
  classical
  let supportedLeft : S → ℝ :=
    fun state => if state ∈ law.support then left state else right state
  calc
    expect law left = expect law supportedLeft := by
      apply ProbabilityMassFunction.expect_congr_on_support
      intro state state_mem
      dsimp only [supportedLeft]
      rw [if_pos state_mem]
    _ ≤ expect law right := by
      apply expect_mono
      intro state
      by_cases state_mem : state ∈ law.support
      · dsimp only [supportedLeft]
        rw [if_pos state_mem]
        exact le_on_support state state_mem
      · dsimp only [supportedLeft]
        rw [if_neg state_mem]

omit [Fintype S] in
private theorem sum_expected_cost_le_telescope_of_expected_drift
    (law : ℕ → PMF S)
    (cost potential : S → ℝ)
    (start horizon : ℕ)
    (expected_drift :
      ∀ offset, offset < horizon →
        expect (law (start + offset)) cost ≤
          expect (law (start + offset + 1)) potential -
            expect (law (start + offset)) potential) :
    (∑ offset ∈ Finset.range horizon,
      expect (law (start + offset)) cost) ≤
        expect (law (start + horizon)) potential -
          expect (law start) potential := by
  induction horizon with
  | zero =>
      simp
  | succ horizon inductionHypothesis =>
      have previous :
          (∑ offset ∈ Finset.range horizon,
            expect (law (start + offset)) cost) ≤
              expect (law (start + horizon)) potential -
                expect (law start) potential := by
        apply inductionHypothesis
        intro offset offset_lt
        exact expected_drift offset
          (offset_lt.trans (Nat.lt_succ_self horizon))
      have finalStep :=
        expected_drift horizon (Nat.lt_succ_self horizon)
      rw [Finset.sum_range_succ]
      calc
        _ ≤
            (expect (law (start + horizon)) potential -
                expect (law start) potential) +
              (expect (law (start + horizon + 1)) potential -
                expect (law (start + horizon)) potential) :=
          add_le_add previous finalStep
        _ =
            expect (law (start + (horizon + 1))) potential -
              expect (law start) potential := by
          rw [show start + horizon + 1 = start + (horizon + 1) by omega]
          ring

private theorem expected_potential_sub_le_epochPotentialBill
    (first last : PMF S) (potential : ℕ → S → ℝ) (epoch : ℕ) :
    expect last (potential epoch) - expect first (potential epoch) ≤
      epochPotentialBill potential epoch := by
  have pointwise_abs (state : S) :
      |potential epoch state| ≤
        finiteStatePotentialBound (potential epoch) := by
    simpa [statePotentialAccount] using
      abs_statePotentialAccount_le_finiteStatePotentialBound
        (potential epoch) (fun _ => state) 0
  have last_le :
      expect last (potential epoch) ≤
        finiteStatePotentialBound (potential epoch) := by
    calc
      expect last (potential epoch) ≤
          expect last
            (fun _ => finiteStatePotentialBound (potential epoch)) := by
        apply expect_mono
        intro state
        exact (le_abs_self _).trans (pointwise_abs state)
      _ = finiteStatePotentialBound (potential epoch) :=
        expect_const _ _
  have first_ge :
      -finiteStatePotentialBound (potential epoch) ≤
        expect first (potential epoch) := by
    calc
      -finiteStatePotentialBound (potential epoch) =
          expect first
            (fun _ => -finiteStatePotentialBound (potential epoch)) := by
        rw [expect_const]
      _ ≤ expect first (potential epoch) := by
        apply expect_mono
        intro state
        exact neg_le_of_abs_le (pointwise_abs state)
  unfold epochPotentialBill
  linarith

/-- One epoch prefix is paid either by its explicit early bill or by the tail
potential bill.  The tail assumption is only an expected one-step inequality
along the actual marginal law. -/
theorem expected_epochCost_le_supportedBill_of_expectedDrift
    (law : ℕ → PMF S)
    (cost potential : ℕ → S → ℝ)
    (startEpoch : ℕ)
    (expected_drift :
      ∀ epoch, startEpoch ≤ epoch →
        ∀ offset, offset < anytimeEpochLength epoch →
          expect
              (law (epochStart anytimeEpochLength epoch + offset))
              (cost epoch) ≤
            expect
                (law
                  (epochStart anytimeEpochLength epoch + offset + 1))
                (potential epoch) -
              expect
                (law
                  (epochStart anytimeEpochLength epoch + offset))
                (potential epoch))
    (epoch horizon : ℕ)
    (horizon_le : horizon ≤ anytimeEpochLength epoch) :
    (∑ offset ∈ Finset.range horizon,
      expect
        (law (epochStart anytimeEpochLength epoch + offset))
        (cost epoch)) ≤
      supportedMovingKernelEpochBill
        law cost potential startEpoch epoch := by
  by_cases early : epoch < startEpoch
  · unfold supportedMovingKernelEpochBill
    rw [if_pos early]
    unfold earlyEpochExpectedCostBill
    calc
      (∑ offset ∈ Finset.range horizon,
        expect
          (law (epochStart anytimeEpochLength epoch + offset))
          (cost epoch)) ≤
          ∑ offset ∈ Finset.range horizon,
            |expect
              (law (epochStart anytimeEpochLength epoch + offset))
              (cost epoch)| := by
        apply Finset.sum_le_sum
        intro offset offset_mem
        exact le_abs_self _
      _ ≤
          ∑ offset ∈ Finset.range (anytimeEpochLength epoch),
            |expect
              (law (epochStart anytimeEpochLength epoch + offset))
              (cost epoch)| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono horizon_le
        · intro offset offset_mem offset_not_mem
          exact abs_nonneg _
  · have tail : startEpoch ≤ epoch := Nat.le_of_not_gt early
    unfold supportedMovingKernelEpochBill
    rw [if_neg early]
    have telescope :=
      sum_expected_cost_le_telescope_of_expected_drift
        law (cost epoch) (potential epoch)
        (epochStart anytimeEpochLength epoch) horizon
        (fun offset offset_lt =>
          expected_drift epoch tail offset
            (offset_lt.trans_le horizon_le))
    exact telescope.trans
      (expected_potential_sub_le_epochPotentialBill
        (law (epochStart anytimeEpochLength epoch))
        (law (epochStart anytimeEpochLength epoch + horizon))
        potential epoch)

omit [Fintype S] in
/-- A support-restricted pointwise drift inequality implies the expected
one-step premise used by the support-sensitive account. -/
theorem expectedDrift_of_drift_on_marginalSupport
    [Finite S]
    (law : ℕ → PMF S)
    (kernel : ℕ → S → PMF S)
    (cost potential : ℕ → S → ℝ)
    (law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind (kernel (anytimeEpochIndex stage)))
    (startEpoch : ℕ)
    (cost_le_drift_on_support :
      ∀ epoch, startEpoch ≤ epoch →
        ∀ offset, offset < anytimeEpochLength epoch →
          ∀ state,
            state ∈
                (law
                  (epochStart anytimeEpochLength epoch + offset)).support →
              cost epoch state ≤
                expect (kernel epoch state) (potential epoch) -
                  potential epoch state) :
    ∀ epoch, startEpoch ≤ epoch →
      ∀ offset, offset < anytimeEpochLength epoch →
        expect
            (law (epochStart anytimeEpochLength epoch + offset))
            (cost epoch) ≤
          expect
              (law (epochStart anytimeEpochLength epoch + offset + 1))
              (potential epoch) -
            expect
              (law (epochStart anytimeEpochLength epoch + offset))
              (potential epoch) := by
  intro epoch epoch_ge offset offset_lt
  let stage := epochStart anytimeEpochLength epoch + offset
  have index_eq : anytimeEpochIndex stage = epoch := by
    apply anytimeEpochIndex_eq
    · simp [stage]
    · rw [epochStart_succ]
      simp only [stage]
      omega
  calc
    expect (law stage) (cost epoch) ≤
        expect (law stage)
          (fun state =>
            expect (kernel epoch state) (potential epoch) -
              potential epoch state) := by
      apply expect_le_expect_of_le_on_support
      exact cost_le_drift_on_support
        epoch epoch_ge offset offset_lt
    _ =
        expect ((law stage).bind (kernel epoch)) (potential epoch) -
          expect (law stage) (potential epoch) := by
      rw [expect_sub, expect_bind]
    _ =
        expect (law (stage + 1)) (potential epoch) -
          expect (law stage) (potential epoch) := by
      rw [law_step stage, index_eq]

omit [Fintype S] in
private theorem cumulativeExpectedScheduledCost_le_budget_of_epochPrefix
    (law : ℕ → PMF S) (cost : ℕ → S → ℝ) (bill : ℕ → ℝ)
    (epoch_prefix :
      ∀ epoch horizon, horizon ≤ anytimeEpochLength epoch →
        (∑ offset ∈ Finset.range horizon,
          expect
            (law (epochStart anytimeEpochLength epoch + offset))
            (cost epoch)) ≤
          bill epoch)
    (horizon : ℕ) :
    cumulativeExpectedScheduledCost law cost horizon ≤
      completedAndCurrentEpochBudget bill horizon := by
  let epoch := anytimeEpochIndex horizon
  let offset := anytimeEpochOffset horizon
  have time_eq :
      epochStart anytimeEpochLength epoch + offset = horizon :=
    anytimeEpochStart_add_offset horizon
  unfold cumulativeExpectedScheduledCost
    completedAndCurrentEpochBudget
  change
    (∑ stage ∈ Finset.range horizon,
      expect (law stage) (cost (anytimeEpochIndex stage))) ≤
        (∑ k ∈ Finset.range epoch, bill k) + bill epoch
  rw [← time_eq, Finset.sum_range_add]
  apply add_le_add
  · induction epoch with
    | zero =>
        simp [epochStart]
    | succ epoch inductionHypothesis =>
        rw [epochStart_succ, Finset.sum_range_succ,
          Finset.sum_range_add]
        apply add_le_add inductionHypothesis
        have epochBound :=
          epoch_prefix epoch (anytimeEpochLength epoch) le_rfl
        have scheduledCost_eq :
            (∑ stepIndex ∈ Finset.range (anytimeEpochLength epoch),
              expect
                (law
                  (epochStart anytimeEpochLength epoch + stepIndex))
                (cost
                  (anytimeEpochIndex
                    (epochStart anytimeEpochLength epoch +
                      stepIndex)))) =
              ∑ stepIndex ∈ Finset.range (anytimeEpochLength epoch),
                expect
                  (law
                    (epochStart anytimeEpochLength epoch + stepIndex))
                  (cost epoch) := by
          apply Finset.sum_congr rfl
          intro stepIndex stepIndex_mem
          have stepIndex_lt :
              stepIndex < anytimeEpochLength epoch :=
            Finset.mem_range.mp stepIndex_mem
          have local_index_eq :
              anytimeEpochIndex
                  (epochStart anytimeEpochLength epoch + stepIndex) =
                epoch := by
            apply anytimeEpochIndex_eq
            · omega
            · rw [epochStart_succ]
              omega
          rw [local_index_eq]
        rw [scheduledCost_eq]
        exact epochBound
  · have epochBound :=
      epoch_prefix epoch offset (anytimeEpochOffset_le horizon)
    have scheduledCost_eq :
        (∑ stepIndex ∈ Finset.range offset,
          expect
            (law (epochStart anytimeEpochLength epoch + stepIndex))
            (cost
              (anytimeEpochIndex
                (epochStart anytimeEpochLength epoch + stepIndex)))) =
          ∑ stepIndex ∈ Finset.range offset,
            expect
              (law (epochStart anytimeEpochLength epoch + stepIndex))
              (cost epoch) := by
      apply Finset.sum_congr rfl
      intro stepIndex stepIndex_mem
      have stepIndex_lt : stepIndex < offset :=
        Finset.mem_range.mp stepIndex_mem
      have local_index_eq :
          anytimeEpochIndex
              (epochStart anytimeEpochLength epoch + stepIndex) =
            epoch := by
        apply anytimeEpochIndex_eq
        · omega
        · have offset_lt := anytimeEpochOffset_lt horizon
          change offset < anytimeEpochLength epoch at offset_lt
          rw [epochStart_succ]
          omega
      rw [local_index_eq]
    rw [scheduledCost_eq]
    exact epochBound

/-- The expected-drift premise gives an all-horizon completed/current budget.
Early epochs are paid explicitly; all later epochs use potential bills. -/
theorem cumulativeExpectedScheduledCost_le_supportedBudget
    (law : ℕ → PMF S)
    (cost potential : ℕ → S → ℝ)
    (startEpoch : ℕ)
    (expected_drift :
      ∀ epoch, startEpoch ≤ epoch →
        ∀ offset, offset < anytimeEpochLength epoch →
          expect
              (law (epochStart anytimeEpochLength epoch + offset))
              (cost epoch) ≤
            expect
                (law
                  (epochStart anytimeEpochLength epoch + offset + 1))
                (potential epoch) -
              expect
                (law
                  (epochStart anytimeEpochLength epoch + offset))
                (potential epoch))
    (horizon : ℕ) :
    cumulativeExpectedScheduledCost law cost horizon ≤
      completedAndCurrentEpochBudget
        (supportedMovingKernelEpochBill
          law cost potential startEpoch) horizon := by
  apply cumulativeExpectedScheduledCost_le_budget_of_epochPrefix
  exact expected_epochCost_le_supportedBill_of_expectedDrift
    law cost potential startEpoch expected_drift

private theorem supportedMovingKernelEpochBill_nonneg
    (law : ℕ → PMF S) (cost potential : ℕ → S → ℝ)
    (startEpoch epoch : ℕ) :
    0 ≤ supportedMovingKernelEpochBill
      law cost potential startEpoch epoch := by
  unfold supportedMovingKernelEpochBill
  split_ifs
  · unfold earlyEpochExpectedCostBill
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · unfold epochPotentialBill finiteStatePotentialBound
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun state _ =>
        abs_nonneg (potential epoch state))

private theorem tendsto_supportedMovingKernelEpochBill_ratio
    (law : ℕ → PMF S) (cost potential : ℕ → S → ℝ)
    (startEpoch : ℕ)
    (bill_ratio :
      Tendsto
        (fun epoch =>
          epochPotentialBill potential epoch /
            (anytimeEpochLength epoch : ℝ))
        atTop (nhds 0)) :
    Tendsto
      (fun epoch =>
        supportedMovingKernelEpochBill
            law cost potential startEpoch epoch /
          (anytimeEpochLength epoch : ℝ))
      atTop (nhds 0) := by
  refine Filter.Tendsto.congr' ?_ bill_ratio
  filter_upwards [eventually_ge_atTop startEpoch] with epoch epoch_ge
  unfold supportedMovingKernelEpochBill
  rw [if_neg (Nat.not_lt.mpr epoch_ge)]

/-- The expected one-step drift premise by itself yields a sublinear
all-horizon account.  This is the most general form of the construction; it
does not mention a kernel or a pointwise state inequality. -/
theorem exists_sublinearExpectedDriftMovingKernelCostAccount
    (law : ℕ → PMF S)
    (cost potential : ℕ → S → ℝ)
    (startEpoch : ℕ)
    (expected_drift :
      ∀ epoch, startEpoch ≤ epoch →
        ∀ offset, offset < anytimeEpochLength epoch →
          expect
              (law (epochStart anytimeEpochLength epoch + offset))
              (cost epoch) ≤
            expect
                (law
                  (epochStart anytimeEpochLength epoch + offset + 1))
                (potential epoch) -
              expect
                (law
                  (epochStart anytimeEpochLength epoch + offset))
                (potential epoch))
    (bill_ratio :
      Tendsto
        (fun epoch =>
          epochPotentialBill potential epoch /
            (anytimeEpochLength epoch : ℝ))
        atTop (nhds 0)) :
    (∀ horizon,
      cumulativeExpectedScheduledCost law cost horizon ≤
        completedAndCurrentEpochBudget
          (supportedMovingKernelEpochBill
            law cost potential startEpoch) horizon) ∧
      IsAsymptoticallySublinear
        (completedAndCurrentEpochBudget
          (supportedMovingKernelEpochBill
            law cost potential startEpoch)) := by
  constructor
  · exact cumulativeExpectedScheduledCost_le_supportedBudget
      law cost potential startEpoch expected_drift
  · apply completedAndCurrentEpochBudget_sublinear
    · exact supportedMovingKernelEpochBill_nonneg
        law cost potential startEpoch
    · exact tendsto_supportedMovingKernelEpochBill_ratio
        law cost potential startEpoch bill_ratio

/-- Support-sensitive moving-kernel costs admit a sublinear all-horizon
account once the eventual potential bill is negligible relative to epoch
length.  The finitely many early explicit bills do not affect the rate. -/
theorem exists_sublinearSupportedMovingKernelCostAccount
    (law : ℕ → PMF S)
    (kernel : ℕ → S → PMF S)
    (cost potential : ℕ → S → ℝ)
    (law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind
            (kernel (anytimeEpochIndex stage)))
    (startEpoch : ℕ)
    (cost_le_drift_on_support :
      ∀ epoch, startEpoch ≤ epoch →
        ∀ offset, offset < anytimeEpochLength epoch →
          ∀ state,
            state ∈
                (law
                  (epochStart anytimeEpochLength epoch + offset)).support →
              cost epoch state ≤
                expect (kernel epoch state) (potential epoch) -
                  potential epoch state)
    (bill_ratio :
      Tendsto
        (fun epoch =>
          epochPotentialBill potential epoch /
            (anytimeEpochLength epoch : ℝ))
        atTop (nhds 0)) :
    (∀ horizon,
      cumulativeExpectedScheduledCost law cost horizon ≤
        completedAndCurrentEpochBudget
          (supportedMovingKernelEpochBill
            law cost potential startEpoch) horizon) ∧
      IsAsymptoticallySublinear
        (completedAndCurrentEpochBudget
          (supportedMovingKernelEpochBill
            law cost potential startEpoch)) := by
  have expected_drift :=
    expectedDrift_of_drift_on_marginalSupport
      law kernel cost potential law_step startEpoch
      cost_le_drift_on_support
  exact exists_sublinearExpectedDriftMovingKernelCostAccount
    law cost potential startEpoch expected_drift bill_ratio

end Probability
end Math
