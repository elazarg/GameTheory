/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerNeutralPuncturedPotentialCalendarAccount

/-!
# Potential accounts for a piecewise-frozen moving kernel

This file factors the marginal-law core of punctured-potential calendar
accounting.  A state law follows one kernel throughout each quadratic epoch.
If an epoch cost is bounded pointwise by the drift of one epoch potential,
then its cumulative expected cost is bounded by one endpoint bill per
completed epoch and one bill for the current epoch.

No game, behavior strategy, recurrence class, or payoff target occurs here.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter Math.OnlineLearning

variable {S : Type*} [Fintype S]

/-- Expected cost accumulated under a calendar state law. -/
def cumulativeExpectedScheduledCost
    (law : ℕ → PMF S) (cost : ℕ → S → ℝ) (horizon : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range horizon,
    expect (law stage) (cost (anytimeEpochIndex stage))

/-- The endpoint bill associated with one finite-state potential. -/
def epochPotentialBill (potential : ℕ → S → ℝ) (epoch : ℕ) : ℝ :=
  2 * finiteStatePotentialBound (potential epoch)

omit [Fintype S] in
private theorem expected_cost_le_potential_increment
    [Finite S]
    (current next : PMF S)
    (kernel : S → PMF S)
    (cost potential : S → ℝ)
    (next_eq : next = current.bind kernel)
    (cost_le_drift :
      ∀ state,
        cost state ≤
          expect (kernel state) potential - potential state) :
    expect current cost ≤
      expect next potential - expect current potential := by
  calc
    expect current cost ≤
        expect current
          (fun state =>
            expect (kernel state) potential - potential state) := by
      apply expect_mono
      exact cost_le_drift
    _ =
        expect (current.bind kernel) potential -
          expect current potential := by
      rw [expect_sub, expect_bind]
    _ = expect next potential - expect current potential := by
      rw [next_eq]

omit [Fintype S] in
private theorem sum_expected_cost_le_potential_telescope
    [Finite S]
    (law : ℕ → PMF S)
    (kernel : S → PMF S)
    (cost potential : S → ℝ)
    (start horizon : ℕ)
    (step :
      ∀ offset, offset < horizon →
        law (start + offset + 1) =
          (law (start + offset)).bind kernel)
    (cost_le_drift :
      ∀ state,
        cost state ≤
          expect (kernel state) potential - potential state) :
    (∑ offset ∈ Finset.range horizon,
      expect (law (start + offset)) cost) ≤
        expect (law (start + horizon)) potential -
          expect (law start) potential := by
  induction horizon with
  | zero =>
      simp
  | succ horizon inductionHypothesis =>
      have step_initial :
          ∀ offset, offset < horizon →
            law (start + offset + 1) =
              (law (start + offset)).bind kernel :=
        fun offset offset_lt =>
          step offset (offset_lt.trans (Nat.lt_succ_self horizon))
      have previous :=
        inductionHypothesis step_initial
      have finalStep :=
        expected_cost_le_potential_increment
          (law (start + horizon))
          (law (start + horizon + 1))
          kernel cost potential
          (step horizon (Nat.lt_succ_self horizon))
          cost_le_drift
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

private theorem expected_potential_sub_le_bill
    (first last : PMF S) (potential : S → ℝ) :
    expect last potential - expect first potential ≤
      2 * finiteStatePotentialBound potential := by
  have pointwise_abs (state : S) :
      |potential state| ≤ finiteStatePotentialBound potential := by
    simpa [statePotentialAccount] using
      abs_statePotentialAccount_le_finiteStatePotentialBound
        potential (fun _ => state) 0
  have last_le :
      expect last potential ≤ finiteStatePotentialBound potential := by
    calc
      expect last potential ≤
          expect last (fun _ => finiteStatePotentialBound potential) := by
        apply expect_mono
        intro state
        exact (le_abs_self _).trans (pointwise_abs state)
      _ = finiteStatePotentialBound potential := expect_const _ _
  have first_ge :
      -finiteStatePotentialBound potential ≤ expect first potential := by
    calc
      -finiteStatePotentialBound potential =
          expect first
            (fun _ => -finiteStatePotentialBound potential) := by
        rw [expect_const]
      _ ≤ expect first potential := by
        apply expect_mono
        intro state
        exact
          (neg_le_of_abs_le (pointwise_abs state))
  linarith

/-- One prefix of an epoch is paid by one finite-state potential bill. -/
theorem expected_epochCost_le_bill
    (law : ℕ → PMF S)
    (kernel : ℕ → S → PMF S)
    (cost potential : ℕ → S → ℝ)
    (law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind
            (kernel (anytimeEpochIndex stage)))
    (cost_le_drift :
      ∀ epoch state,
        cost epoch state ≤
          expect (kernel epoch state) (potential epoch) -
            potential epoch state)
    (epoch horizon : ℕ)
    (horizon_le : horizon ≤ anytimeEpochLength epoch) :
    (∑ offset ∈ Finset.range horizon,
      expect
        (law (epochStart anytimeEpochLength epoch + offset))
        (cost epoch)) ≤
      epochPotentialBill potential epoch := by
  have localStep :
      ∀ offset, offset < horizon →
        law
              (epochStart anytimeEpochLength epoch + offset + 1) =
          (law
              (epochStart anytimeEpochLength epoch + offset)).bind
            (kernel epoch) := by
    intro offset offset_lt
    have index_eq :
        anytimeEpochIndex
            (epochStart anytimeEpochLength epoch + offset) =
          epoch := by
      apply anytimeEpochIndex_eq
      · omega
      · rw [epochStart_succ]
        omega
    simpa only [index_eq] using
      law_step
        (epochStart anytimeEpochLength epoch + offset)
  have telescope :=
    sum_expected_cost_le_potential_telescope
      law (kernel epoch) (cost epoch) (potential epoch)
      (epochStart anytimeEpochLength epoch) horizon
      localStep (cost_le_drift epoch)
  exact telescope.trans
    (expected_potential_sub_le_bill
      (law (epochStart anytimeEpochLength epoch))
      (law (epochStart anytimeEpochLength epoch + horizon))
      (potential epoch))

/-- Completed epochs satisfy the sum of their endpoint bills. -/
theorem expected_completedEpochCost_le_bills
    (law : ℕ → PMF S)
    (kernel : ℕ → S → PMF S)
    (cost potential : ℕ → S → ℝ)
    (law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind
            (kernel (anytimeEpochIndex stage)))
    (cost_le_drift :
      ∀ epoch state,
        cost epoch state ≤
          expect (kernel epoch state) (potential epoch) -
            potential epoch state)
    (epochs : ℕ) :
    cumulativeExpectedScheduledCost law cost
        (epochStart anytimeEpochLength epochs) ≤
      ∑ epoch ∈ Finset.range epochs,
        epochPotentialBill potential epoch := by
  induction epochs with
  | zero =>
      simp [cumulativeExpectedScheduledCost, epochStart]
  | succ epochs inductionHypothesis =>
      rw [epochStart_succ,
        Finset.sum_range_succ]
      unfold cumulativeExpectedScheduledCost at inductionHypothesis ⊢
      rw [Finset.sum_range_add]
      apply add_le_add inductionHypothesis
      have epochBound :=
        expected_epochCost_le_bill
          law kernel cost potential law_step cost_le_drift
          epochs (anytimeEpochLength epochs) le_rfl
      have scheduledCost_eq :
          (∑ offset ∈ Finset.range (anytimeEpochLength epochs),
            expect
              (law (epochStart anytimeEpochLength epochs + offset))
              (cost
                (anytimeEpochIndex
                  (epochStart anytimeEpochLength epochs + offset)))) =
            ∑ offset ∈ Finset.range (anytimeEpochLength epochs),
              expect
                (law (epochStart anytimeEpochLength epochs + offset))
                (cost epochs) := by
        apply Finset.sum_congr rfl
        intro offset offset_mem
        have offset_lt :
            offset < anytimeEpochLength epochs :=
          Finset.mem_range.mp offset_mem
        have index_eq :
            anytimeEpochIndex
                (epochStart anytimeEpochLength epochs + offset) =
              epochs := by
          apply anytimeEpochIndex_eq
          · omega
          · rw [epochStart_succ]
            omega
        rw [index_eq]
      rw [scheduledCost_eq]
      exact epochBound

/-- The entire moving-law cost is bounded by completed bills plus the bill
of the current epoch. -/
theorem cumulativeExpectedScheduledCost_le_budget
    (law : ℕ → PMF S)
    (kernel : ℕ → S → PMF S)
    (cost potential : ℕ → S → ℝ)
    (law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind
            (kernel (anytimeEpochIndex stage)))
    (cost_le_drift :
      ∀ epoch state,
        cost epoch state ≤
          expect (kernel epoch state) (potential epoch) -
            potential epoch state)
    (horizon : ℕ) :
    cumulativeExpectedScheduledCost law cost horizon ≤
      completedAndCurrentEpochBudget
        (epochPotentialBill potential) horizon := by
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
        (∑ k ∈ Finset.range epoch,
          epochPotentialBill potential k) +
          epochPotentialBill potential epoch
  rw [← time_eq, Finset.sum_range_add]
  apply add_le_add
  · exact expected_completedEpochCost_le_bills
      law kernel cost potential law_step cost_le_drift epoch
  · have epochBound :=
      expected_epochCost_le_bill
        law kernel cost potential law_step cost_le_drift
        epoch offset (anytimeEpochOffset_le horizon)
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
      have index_eq :
          anytimeEpochIndex
              (epochStart anytimeEpochLength epoch + stepIndex) =
            epoch := by
        apply anytimeEpochIndex_eq
        · omega
        · have offset_lt :=
            anytimeEpochOffset_lt horizon
          change offset < anytimeEpochLength epoch at offset_lt
          rw [epochStart_succ]
          omega
      rw [index_eq]
    rw [scheduledCost_eq]
    exact epochBound

/-- A vanishing bill-to-epoch-length ratio turns the potential estimate into
a sublinear all-horizon account. -/
theorem exists_sublinearMovingKernelCostAccount
    (law : ℕ → PMF S)
    (kernel : ℕ → S → PMF S)
    (cost potential : ℕ → S → ℝ)
    (law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind
            (kernel (anytimeEpochIndex stage)))
    (cost_le_drift :
      ∀ epoch state,
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
          (epochPotentialBill potential) horizon) ∧
      IsAsymptoticallySublinear
        (completedAndCurrentEpochBudget
          (epochPotentialBill potential)) := by
  constructor
  · exact cumulativeExpectedScheduledCost_le_budget
      law kernel cost potential law_step cost_le_drift
  · apply completedAndCurrentEpochBudget_sublinear
    · intro epoch
      unfold epochPotentialBill finiteStatePotentialBound
      exact mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun state _ =>
          abs_nonneg (potential epoch state))
    · exact bill_ratio

end Probability
end Math
