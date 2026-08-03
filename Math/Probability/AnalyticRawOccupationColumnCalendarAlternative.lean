/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.MovingKernelEpochPotentialAccount
import Math.Probability.AnalyticMarkovChargeAlternative

/-!
# Calendar accounts from analytic real occupation columns

The analytic occupation-flow alternative is naturally stated for a
two-sided real column germ.  In applications, the stochastic kernel may
exist only at the valid positive parameters selected by the calendar, so
there need not be a globally defined analytic map into `PMF`.

This file separates those two roles.  The analytic alternative is applied
only to the real column and charge germs.  In the potential branch, an
epoch-indexed semantic kernel is introduced through the exact coordinate
identity saying that the real column is arrival probability minus the
source atom.  The generic moving-kernel telescope then gives a sublinear
one-sided account.

The burn-in theorem accepts an arbitrary lower bound on the first epoch.
This permits independently obtained alternatives, including opposite
charge orientations, to be synchronized by taking a later common start.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter Math.OnlineLearning Set Topology

variable {S : Type*}

/-- The semantic kernel at epoch `epoch` realizes the analytic real
occupation column at the corresponding shifted positive parameter. -/
def RealizesShiftedRawOccupationColumn
    [DecidableEq S]
    (column : ℝ → S → S → ℝ) (startEpoch : ℕ)
    (kernel : ℕ → S → PMF S) : Prop :=
  ∀ epoch source destination,
    column (shiftedUniversalEpochScale startEpoch epoch)
        source destination =
      (kernel epoch source destination).toReal -
        if destination = source then 1 else 0

/-- An analytic charge frozen at the shifted positive parameter of one
calendar epoch. -/
def shiftedRawColumnCharge
    (charge : ℝ → S → ℝ) (startEpoch epoch : ℕ) : S → ℝ :=
  charge (shiftedUniversalEpochScale startEpoch epoch)

namespace AnalyticScaledChargedOccupationPotential

/-- The punctured potential frozen at the shifted positive parameter of one
calendar epoch. -/
def shiftedRawColumnPotential
    [Fintype S]
    {column : ℝ → S → S → ℝ} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    (startEpoch epoch : ℕ) : S → ℝ :=
  P.puncturedPotentialAt
    (shiftedUniversalEpochScale startEpoch epoch)

/-- At one positive parameter, a semantic kernel which realizes the raw
occupation column turns the scaled Farkas inequality into the ordinary
charge-to-drift inequality. -/
theorem charge_le_semanticKernel_puncturedDrift
    [Fintype S] [DecidableEq S]
    {column : ℝ → S → S → ℝ} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    {t : ℝ} (ht : 0 < t)
    (kernel : S → PMF S)
    (realizes :
      ∀ source destination,
        column t source destination =
          (kernel source destination).toReal -
            if destination = source then 1 else 0)
    (scaled :
      ∀ source,
        t ^ P.poleOrder * charge t source ≤
          ∑ destination,
            P.potential t destination *
              column t source destination)
    (source : S) :
    charge t source ≤
      expect (kernel source) (P.puncturedPotentialAt t) -
        P.puncturedPotentialAt t source := by
  have hcolumn :
      column t source =
        actualOccupationColumn kernel id source := by
    funext destination
    rw [realizes source destination]
    rfl
  have hpair :
      (∑ destination,
          P.potential t destination *
            column t source destination) =
        expect (kernel source) (P.potential t) -
          P.potential t source := by
    rw [hcolumn]
    simpa using
      potential_pair_actualOccupationColumn
        kernel id (P.potential t) source
  have hpow : 0 < t ^ P.poleOrder :=
    pow_pos ht _
  have hexpect :
      expect (kernel source) (P.puncturedPotentialAt t) =
        expect (kernel source) (P.potential t) /
          t ^ P.poleOrder := by
    calc
      expect (kernel source) (P.puncturedPotentialAt t) =
          expect (kernel source)
            (fun destination =>
              (t ^ P.poleOrder)⁻¹ *
                P.potential t destination) := by
            congr 1
            funext destination
            rw [puncturedPotentialAt, div_eq_inv_mul]
      _ =
          (t ^ P.poleOrder)⁻¹ *
            expect (kernel source) (P.potential t) := by
            rw [expect_const_mul]
      _ =
          expect (kernel source) (P.potential t) /
            t ^ P.poleOrder := by
            rw [div_eq_mul_inv, mul_comm]
  rw [hexpect, puncturedPotentialAt, ← sub_div]
  apply (le_div_iff₀ hpow).2
  rw [mul_comm]
  exact (scaled source).trans_eq hpair

/-- A scaled analytic potential admits an arbitrarily late burn-in after
which every realizing epoch kernel satisfies the unscaled charge-to-drift
inequality. -/
theorem exists_startEpoch_ge_charge_le_semanticKernel_puncturedDrift
    [Fintype S] [DecidableEq S]
    {column : ℝ → S → S → ℝ} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    (minimumStart : ℕ) :
    ∃ startEpoch : ℕ,
      minimumStart ≤ startEpoch ∧
        ∀ (kernel : ℕ → S → PMF S),
          RealizesShiftedRawOccupationColumn
              column startEpoch kernel →
            ∀ epoch source,
              shiftedRawColumnCharge charge startEpoch epoch source ≤
                expect (kernel epoch source)
                    (P.shiftedRawColumnPotential
                      startEpoch epoch) -
                  P.shiftedRawColumnPotential
                    startEpoch epoch source := by
  have hscale :
      Tendsto (shiftedUniversalEpochScale minimumStart)
        atTop (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact
      ⟨tendsto_shiftedUniversalEpochScale minimumStart,
        Filter.Eventually.of_forall fun epoch =>
          shiftedUniversalEpochScale_pos minimumStart epoch⟩
  have heventual :
      ∀ᶠ epoch : ℕ in atTop,
        ∀ source,
          shiftedUniversalEpochScale minimumStart epoch ^
                P.poleOrder *
              charge
                (shiftedUniversalEpochScale minimumStart epoch)
                source ≤
            ∑ destination,
              P.potential
                    (shiftedUniversalEpochScale minimumStart epoch)
                    destination *
                column
                  (shiftedUniversalEpochScale minimumStart epoch)
                  source destination := by
    exact hscale.eventually P.eventual
  obtain ⟨burnIn, hburnIn⟩ := eventually_atTop.1 heventual
  let startEpoch := minimumStart + burnIn
  refine ⟨startEpoch, by simp [startEpoch], ?_⟩
  intro kernel realizes epoch source
  apply P.charge_le_semanticKernel_puncturedDrift
    (shiftedUniversalEpochScale_pos startEpoch epoch)
    (kernel epoch)
    (fun state destination =>
      realizes epoch state destination)
  · intro state
    have h :=
      hburnIn (burnIn + epoch) (by omega) state
    simpa only [startEpoch, shiftedUniversalEpochScale,
      add_assoc] using h

/-- The punctured endpoint bill remains negligible compared with the
quadratic epoch length after any fixed burn-in. -/
theorem tendsto_shiftedRawColumnPotential_bill_div_length
    [Fintype S]
    {column : ℝ → S → S → ℝ} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    (startEpoch : ℕ) :
    Tendsto
      (fun epoch =>
        epochPotentialBill
              (P.shiftedRawColumnPotential startEpoch) epoch /
          (anytimeEpochLength epoch : ℝ))
      atTop (𝓝 0) := by
  simpa only [epochPotentialBill, shiftedRawColumnPotential,
    shiftedUniversalEpochScale,
    shiftedPuncturedPotentialEpochBudget] using
      P.tendsto_shiftedPuncturedPotentialEpochBudget_div_length
        startEpoch

end AnalyticScaledChargedOccupationPotential

/-- An explicit bill for a fixed-start calendar whose drift inequality starts
only at `firstGoodEpoch`.  The finitely many earlier epochs are paid by a
uniform absolute charge bound; later epochs use the potential endpoint
bill. -/
def eventualMovingKernelEpochBill
    [Fintype S]
    (cost potential : ℕ → S → ℝ)
    (firstGoodEpoch epoch : ℕ) : ℝ :=
  if epoch < firstGoodEpoch then
    (anytimeEpochLength epoch : ℝ) *
      finiteStatePotentialBound (cost epoch)
  else
    epochPotentialBill potential epoch

theorem eventualMovingKernelEpochBill_nonneg
    [Fintype S]
    (cost potential : ℕ → S → ℝ)
    (firstGoodEpoch epoch : ℕ) :
    0 ≤ eventualMovingKernelEpochBill
      cost potential firstGoodEpoch epoch := by
  unfold eventualMovingKernelEpochBill
  split
  · exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun state _ => abs_nonneg _)
  · unfold epochPotentialBill finiteStatePotentialBound
    positivity

private theorem expected_cost_le_finiteStatePotentialBound
    [Fintype S]
    (law : PMF S) (cost : S → ℝ) :
    expect law cost ≤ finiteStatePotentialBound cost := by
  calc
    expect law cost ≤
        expect law
          (fun _ => finiteStatePotentialBound cost) := by
      apply expect_mono
      intro state
      exact
        (le_abs_self (cost state)).trans
          (Finset.single_le_sum
            (fun destination _ => abs_nonneg (cost destination))
            (Finset.mem_univ state))
    _ = finiteStatePotentialBound cost := expect_const _ _

/-- One epoch prefix is bounded either by its explicit finite-prefix bill or,
after stabilization, by its potential endpoint bill. -/
theorem expected_epochCost_le_eventualBill
    [Fintype S]
    (law : ℕ → PMF S)
    (kernel : ℕ → S → PMF S)
    (cost potential : ℕ → S → ℝ)
    (law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind
            (kernel (anytimeEpochIndex stage)))
    (firstGoodEpoch : ℕ)
    (cost_le_drift :
      ∀ epoch, firstGoodEpoch ≤ epoch → ∀ state,
        cost epoch state ≤
          expect (kernel epoch state) (potential epoch) -
            potential epoch state)
    (epoch horizon : ℕ)
    (horizon_le : horizon ≤ anytimeEpochLength epoch) :
    (∑ offset ∈ Finset.range horizon,
      expect
        (law (epochStart anytimeEpochLength epoch + offset))
        (cost epoch)) ≤
      eventualMovingKernelEpochBill
        cost potential firstGoodEpoch epoch := by
  by_cases hearly : epoch < firstGoodEpoch
  · rw [eventualMovingKernelEpochBill, if_pos hearly]
    calc
      (∑ offset ∈ Finset.range horizon,
          expect
            (law
              (epochStart anytimeEpochLength epoch + offset))
            (cost epoch)) ≤
          ∑ _offset ∈ Finset.range horizon,
            finiteStatePotentialBound (cost epoch) := by
        apply Finset.sum_le_sum
        intro offset _
        exact expected_cost_le_finiteStatePotentialBound
          (law (epochStart anytimeEpochLength epoch + offset))
          (cost epoch)
      _ =
          (horizon : ℝ) *
            finiteStatePotentialBound (cost epoch) := by
        simp
      _ ≤
          (anytimeEpochLength epoch : ℝ) *
            finiteStatePotentialBound (cost epoch) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast horizon_le
        · unfold finiteStatePotentialBound
          positivity
  · rw [eventualMovingKernelEpochBill, if_neg hearly]
    let lateCost : ℕ → S → ℝ :=
      fun other =>
        if firstGoodEpoch ≤ other then cost other else fun _ => 0
    let latePotential : ℕ → S → ℝ :=
      fun other =>
        if firstGoodEpoch ≤ other then
          potential other
        else fun _ => 0
    have lateCost_le_drift :
        ∀ other state,
          lateCost other state ≤
            expect (kernel other state) (latePotential other) -
              latePotential other state := by
      intro other state
      by_cases hother : firstGoodEpoch ≤ other
      · simp only [lateCost, latePotential, if_pos hother]
        exact cost_le_drift other hother state
      · simp only [lateCost, latePotential, if_neg hother,
          expect_const, sub_self]
        exact le_rfl
    have hbound :=
      expected_epochCost_le_bill
        law kernel lateCost latePotential law_step
        lateCost_le_drift epoch horizon horizon_le
    simpa only [lateCost, latePotential,
      if_pos (Nat.le_of_not_gt hearly),
      epochPotentialBill] using hbound

/-- Completed epochs obey the sum of their eventual epoch bills. -/
theorem expected_completedEpochCost_le_eventualBills
    [Fintype S]
    (law : ℕ → PMF S)
    (kernel : ℕ → S → PMF S)
    (cost potential : ℕ → S → ℝ)
    (law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind
            (kernel (anytimeEpochIndex stage)))
    (firstGoodEpoch : ℕ)
    (cost_le_drift :
      ∀ epoch, firstGoodEpoch ≤ epoch → ∀ state,
        cost epoch state ≤
          expect (kernel epoch state) (potential epoch) -
            potential epoch state)
    (epochs : ℕ) :
    cumulativeExpectedScheduledCost law cost
        (epochStart anytimeEpochLength epochs) ≤
      ∑ epoch ∈ Finset.range epochs,
        eventualMovingKernelEpochBill
          cost potential firstGoodEpoch epoch := by
  induction epochs with
  | zero =>
      simp [cumulativeExpectedScheduledCost, epochStart]
  | succ epochs inductionHypothesis =>
      rw [epochStart_succ, Finset.sum_range_succ]
      unfold cumulativeExpectedScheduledCost at inductionHypothesis ⊢
      rw [Finset.sum_range_add]
      apply add_le_add inductionHypothesis
      have epochBound :=
        expected_epochCost_le_eventualBill
          law kernel cost potential law_step firstGoodEpoch
          cost_le_drift epochs (anytimeEpochLength epochs) le_rfl
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

/-- The whole fixed-start moving calendar is bounded by completed bills plus
the current epoch bill, including the finite analytic stabilization prefix. -/
theorem cumulativeExpectedScheduledCost_le_eventualBudget
    [Fintype S]
    (law : ℕ → PMF S)
    (kernel : ℕ → S → PMF S)
    (cost potential : ℕ → S → ℝ)
    (law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind
            (kernel (anytimeEpochIndex stage)))
    (firstGoodEpoch : ℕ)
    (cost_le_drift :
      ∀ epoch, firstGoodEpoch ≤ epoch → ∀ state,
        cost epoch state ≤
          expect (kernel epoch state) (potential epoch) -
            potential epoch state)
    (horizon : ℕ) :
    cumulativeExpectedScheduledCost law cost horizon ≤
      completedAndCurrentEpochBudget
        (eventualMovingKernelEpochBill
          cost potential firstGoodEpoch) horizon := by
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
          eventualMovingKernelEpochBill
            cost potential firstGoodEpoch k) +
          eventualMovingKernelEpochBill
            cost potential firstGoodEpoch epoch
  rw [← time_eq, Finset.sum_range_add]
  apply add_le_add
  · exact expected_completedEpochCost_le_eventualBills
      law kernel cost potential law_step firstGoodEpoch
      cost_le_drift epoch
  · have epochBound :=
      expected_epochCost_le_eventualBill
        law kernel cost potential law_step firstGoodEpoch
        cost_le_drift epoch offset
        (anytimeEpochOffset_le horizon)
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
        · have offset_lt := anytimeEpochOffset_lt horizon
          change offset < anytimeEpochLength epoch at offset_lt
          rw [epochStart_succ]
          omega
      rw [index_eq]
    rw [scheduledCost_eq]
    exact epochBound

/-- Replacing finitely many potential bills by explicit finite-prefix bills
does not affect the asymptotic bill-to-epoch-length ratio. -/
theorem tendsto_eventualMovingKernelEpochBill_div_length
    [Fintype S]
    (cost potential : ℕ → S → ℝ)
    (firstGoodEpoch : ℕ)
    (potential_ratio :
      Tendsto
        (fun epoch =>
          epochPotentialBill potential epoch /
            (anytimeEpochLength epoch : ℝ))
        atTop (𝓝 0)) :
    Tendsto
      (fun epoch =>
        eventualMovingKernelEpochBill
              cost potential firstGoodEpoch epoch /
          (anytimeEpochLength epoch : ℝ))
      atTop (𝓝 0) := by
  apply potential_ratio.congr'
  filter_upwards [eventually_ge_atTop firstGoodEpoch] with epoch hepoch
  simp only [eventualMovingKernelEpochBill,
    if_neg (Nat.not_lt.mpr hepoch)]

/-- Eventual drift control on one fixed calendar yields an all-horizon
sublinear account; the finitely many pre-stabilization epochs are explicit
in the budget. -/
theorem exists_sublinearEventualMovingKernelCostAccount
    [Fintype S]
    (law : ℕ → PMF S)
    (kernel : ℕ → S → PMF S)
    (cost potential : ℕ → S → ℝ)
    (law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind
            (kernel (anytimeEpochIndex stage)))
    (firstGoodEpoch : ℕ)
    (cost_le_drift :
      ∀ epoch, firstGoodEpoch ≤ epoch → ∀ state,
        cost epoch state ≤
          expect (kernel epoch state) (potential epoch) -
            potential epoch state)
    (potential_ratio :
      Tendsto
        (fun epoch =>
          epochPotentialBill potential epoch /
            (anytimeEpochLength epoch : ℝ))
        atTop (𝓝 0)) :
    (∀ horizon,
      cumulativeExpectedScheduledCost law cost horizon ≤
        completedAndCurrentEpochBudget
          (eventualMovingKernelEpochBill
            cost potential firstGoodEpoch) horizon) ∧
      IsAsymptoticallySublinear
        (completedAndCurrentEpochBudget
          (eventualMovingKernelEpochBill
            cost potential firstGoodEpoch)) := by
  constructor
  · exact cumulativeExpectedScheduledCost_le_eventualBudget
      law kernel cost potential law_step firstGoodEpoch
      cost_le_drift
  · apply completedAndCurrentEpochBudget_sublinear
    · exact eventualMovingKernelEpochBill_nonneg
        cost potential firstGoodEpoch
    · exact tendsto_eventualMovingKernelEpochBill_div_length
        cost potential firstGoodEpoch potential_ratio

namespace AnalyticScaledChargedOccupationPotential

/-- On a fixed shifted calendar, the raw-column drift inequality holds after
some relative epoch.  The calendar's analytic start is not changed. -/
theorem exists_firstGoodEpoch_charge_le_semanticKernel_puncturedDrift
    [Fintype S] [DecidableEq S]
    {column : ℝ → S → S → ℝ} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    (startEpoch : ℕ) :
    ∃ firstGoodEpoch : ℕ,
      ∀ (kernel : ℕ → S → PMF S),
        RealizesShiftedRawOccupationColumn
            column startEpoch kernel →
          ∀ epoch, firstGoodEpoch ≤ epoch → ∀ source,
            shiftedRawColumnCharge charge startEpoch epoch source ≤
              expect (kernel epoch source)
                  (P.shiftedRawColumnPotential
                    startEpoch epoch) -
                P.shiftedRawColumnPotential
                  startEpoch epoch source := by
  have hscale :
      Tendsto (shiftedUniversalEpochScale startEpoch)
        atTop (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact
      ⟨tendsto_shiftedUniversalEpochScale startEpoch,
        Filter.Eventually.of_forall fun epoch =>
          shiftedUniversalEpochScale_pos startEpoch epoch⟩
  have heventual :
      ∀ᶠ epoch : ℕ in atTop,
        ∀ source,
          shiftedUniversalEpochScale startEpoch epoch ^
                P.poleOrder *
              charge
                (shiftedUniversalEpochScale startEpoch epoch)
                source ≤
            ∑ destination,
              P.potential
                    (shiftedUniversalEpochScale startEpoch epoch)
                    destination *
                column
                  (shiftedUniversalEpochScale startEpoch epoch)
                  source destination :=
    hscale.eventually P.eventual
  obtain ⟨firstGoodEpoch, hgood⟩ :=
    eventually_atTop.1 heventual
  refine ⟨firstGoodEpoch, ?_⟩
  intro kernel realizes epoch hepoch source
  apply P.charge_le_semanticKernel_puncturedDrift
    (shiftedUniversalEpochScale_pos startEpoch epoch)
    (kernel epoch)
    (fun state destination =>
      realizes epoch state destination)
  exact hgood epoch hepoch

end AnalyticScaledChargedOccupationPotential

/-- A sublinear raw-charge account on one fixed analytic calendar.  The
finite prefix before the analytic inequality stabilizes is part of the
explicit budget, so the given `startEpoch` is preserved. -/
def HasFixedStartRawColumnCalendarChargeAccount
    [Fintype S] [DecidableEq S]
    (column : ℝ → S → S → ℝ)
    (charge : ℝ → S → ℝ) (startEpoch : ℕ) : Prop :=
  ∃ (P : AnalyticScaledChargedOccupationPotential column charge)
      (firstGoodEpoch : ℕ),
    ∀ (kernel : ℕ → S → PMF S),
      RealizesShiftedRawOccupationColumn
          column startEpoch kernel →
        ∀ (law : ℕ → PMF S),
          (∀ stage,
            law (stage + 1) =
              (law stage).bind
                (kernel (anytimeEpochIndex stage))) →
            (∀ horizon,
              cumulativeExpectedScheduledCost law
                  (shiftedRawColumnCharge charge startEpoch)
                  horizon ≤
                completedAndCurrentEpochBudget
                  (eventualMovingKernelEpochBill
                    (shiftedRawColumnCharge charge startEpoch)
                    (P.shiftedRawColumnPotential startEpoch)
                    firstGoodEpoch) horizon) ∧
              IsAsymptoticallySublinear
                (completedAndCurrentEpochBudget
                  (eventualMovingKernelEpochBill
                    (shiftedRawColumnCharge charge startEpoch)
                    (P.shiftedRawColumnPotential startEpoch)
                    firstGoodEpoch))

namespace AnalyticScaledChargedOccupationPotential

/-- A scaled potential supplies the fixed-start account without rebasing the
calendar. -/
theorem hasFixedStartRawColumnCalendarChargeAccount
    [Fintype S] [DecidableEq S]
    {column : ℝ → S → S → ℝ} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge)
    (startEpoch : ℕ) :
    HasFixedStartRawColumnCalendarChargeAccount
      column charge startEpoch := by
  obtain ⟨firstGoodEpoch, hcost⟩ :=
    P.exists_firstGoodEpoch_charge_le_semanticKernel_puncturedDrift
      startEpoch
  refine ⟨P, firstGoodEpoch, ?_⟩
  intro kernel realizes law law_step
  apply exists_sublinearEventualMovingKernelCostAccount
    law kernel
    (shiftedRawColumnCharge charge startEpoch)
    (P.shiftedRawColumnPotential startEpoch)
    law_step firstGoodEpoch
  · exact hcost kernel realizes
  · exact
      P.tendsto_shiftedRawColumnPotential_bill_div_length
        startEpoch

end AnalyticScaledChargedOccupationPotential

/-- The potential branch supplies, after every prescribed minimum burn-in,
a one-sided sublinear charge account for every epoch-indexed semantic kernel
realizing the analytic raw occupation column. -/
def HasArbitrarilyLateRawColumnCalendarChargeAccount
    [Fintype S] [DecidableEq S]
    (column : ℝ → S → S → ℝ)
    (charge : ℝ → S → ℝ) : Prop :=
  ∃ P : AnalyticScaledChargedOccupationPotential column charge,
    ∀ minimumStart : ℕ,
      ∃ startEpoch : ℕ,
        minimumStart ≤ startEpoch ∧
          ∀ (kernel : ℕ → S → PMF S),
            RealizesShiftedRawOccupationColumn
                column startEpoch kernel →
              ∀ (law : ℕ → PMF S),
                (∀ stage,
                  law (stage + 1) =
                    (law stage).bind
                      (kernel (anytimeEpochIndex stage))) →
                  (∀ horizon,
                    cumulativeExpectedScheduledCost law
                        (shiftedRawColumnCharge
                          charge startEpoch) horizon ≤
                      completedAndCurrentEpochBudget
                        (epochPotentialBill
                          (P.shiftedRawColumnPotential
                            startEpoch)) horizon) ∧
                    IsAsymptoticallySublinear
                      (completedAndCurrentEpochBudget
                        (epochPotentialBill
                          (P.shiftedRawColumnPotential
                            startEpoch)))

namespace AnalyticScaledChargedOccupationPotential

/-- A scaled raw-column potential gives the arbitrarily late semantic
calendar account. -/
theorem hasArbitrarilyLateRawColumnCalendarChargeAccount
    [Fintype S] [DecidableEq S]
    {column : ℝ → S → S → ℝ} {charge : ℝ → S → ℝ}
    (P : AnalyticScaledChargedOccupationPotential column charge) :
    HasArbitrarilyLateRawColumnCalendarChargeAccount
      column charge := by
  refine ⟨P, fun minimumStart => ?_⟩
  obtain ⟨startEpoch, hstart, hcost⟩ :=
    P.exists_startEpoch_ge_charge_le_semanticKernel_puncturedDrift
      minimumStart
  refine ⟨startEpoch, hstart, ?_⟩
  intro kernel realizes law law_step
  apply exists_sublinearMovingKernelCostAccount
    law kernel
    (shiftedRawColumnCharge charge startEpoch)
    (P.shiftedRawColumnPotential startEpoch)
    law_step
  · exact hcost kernel realizes
  · exact
      P.tendsto_shiftedRawColumnPotential_bill_div_length
        startEpoch

end AnalyticScaledChargedOccupationPotential

/-- **Raw-column analytic calendar alternative.**

For an analytic real occupation column and analytic signed charge, exactly
one branch holds:

* a pole-cleared analytic positive circulation has positive total charge;
* after every requested burn-in, any epoch-indexed PMF kernel realizing the
  raw column at the shifted positive calendar points gives a sublinear
  one-sided account for the charge.

No map `ℝ → S → PMF S` is assumed or constructed. -/
theorem
    analyticPositiveChargedRawOccupationCirculation_xor_calendarChargeAccount
    [Fintype S] [DecidableEq S]
    (column : ℝ → S → S → ℝ)
    (charge : ℝ → S → ℝ)
    (hcolumn :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t => column t source destination) 0)
    (hcharge :
      ∀ source,
        AnalyticAt ℝ (fun t => charge t source) 0) :
    Xor
      (Nonempty
        (AnalyticPositiveChargedCirculation column charge))
      (HasArbitrarilyLateRawColumnCalendarChargeAccount
        column charge) := by
  have halternative :=
    analyticPositiveChargedCirculation_xor_scaledPotential
      column charge hcolumn hcharge
  rw [xor_def] at halternative ⊢
  rcases halternative with
      ⟨hcirculation, hnotPotential⟩ |
      ⟨hpotential, hnotCirculation⟩
  · refine Or.inl ⟨hcirculation, ?_⟩
    rintro ⟨P, -⟩
    exact hnotPotential ⟨P⟩
  · refine Or.inr ⟨?_, hnotCirculation⟩
    obtain ⟨P⟩ := hpotential
    exact P.hasArbitrarilyLateRawColumnCalendarChargeAccount

/-- Fixed-calendar form of the raw-column analytic alternative.  This is the
integration theorem for a calendar start already selected by another part
of the construction. -/
theorem
    analyticPositiveChargedRawOccupationCirculation_xor_fixedCalendarChargeAccount
    [Fintype S] [DecidableEq S]
    (column : ℝ → S → S → ℝ)
    (charge : ℝ → S → ℝ)
    (startEpoch : ℕ)
    (hcolumn :
      ∀ source destination,
        AnalyticAt ℝ
          (fun t => column t source destination) 0)
    (hcharge :
      ∀ source,
        AnalyticAt ℝ (fun t => charge t source) 0) :
    Xor
      (Nonempty
        (AnalyticPositiveChargedCirculation column charge))
      (HasFixedStartRawColumnCalendarChargeAccount
        column charge startEpoch) := by
  have halternative :=
    analyticPositiveChargedCirculation_xor_scaledPotential
      column charge hcolumn hcharge
  rw [xor_def] at halternative ⊢
  rcases halternative with
      ⟨hcirculation, hnotPotential⟩ |
      ⟨hpotential, hnotCirculation⟩
  · refine Or.inl ⟨hcirculation, ?_⟩
    rintro ⟨P, -⟩
    exact hnotPotential ⟨P⟩
  · refine Or.inr ⟨?_, hnotCirculation⟩
    obtain ⟨P⟩ := hpotential
    exact P.hasFixedStartRawColumnCalendarChargeAccount
      startEpoch

end Probability
end Math
