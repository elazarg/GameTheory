/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticFinkBaselineChargedClass
import GameTheory.Concepts.Stochastic.AnalyticRawOccupationColumnCalendarAlternative
import GameTheory.Concepts.Stochastic.MovingEndpointOccupationEvidence
import GameTheory.Concepts.Stochastic.ScheduledFinkMarginalRecurrence

/-!
# Prescribed endpoint transport produces an analytic circulation

The prescribed shifted Fink calendar has an exact state-marginal recurrence,
and its epoch kernel realizes the raw analytic baseline occupation column.
Applying the fixed-calendar raw-column alternative to both orientations of
one player's endpoint displacement gives:

* a positive analytic baseline circulation in one orientation; or
* two one-sided sublinear accounts on the exact prescribed calendar.

The second case makes the absolute prescribed endpoint transport sublinear.
Thus failure of that named boundary forces the circulation case.  Evaluating
the circulation at one valid positive parameter also gives a communicating
class of the punctured Fink kernel with positive aggregate oriented charge.

The result does not assert reachability from the prescribed entry, legal
implementation of the class, preservation of the whole payoff target, or
descent of a game-theoretic recursion rank.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Filter Math Math.OnlineLearning Math.Probability Set
open AnalyticBellmanGerm.FiniteBiasSeed

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

omit [DecidableEq G.State] in
/-- The state law named by the endpoint-transport development is the state
law named by the scheduled-kernel recurrence bridge. -/
theorem prescribedCalendarStateLaw_eq_scheduledFinkStateLaw
    (germ : G.AnalyticBellmanGerm)
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (stage : ℕ) :
    MovingEndpointOccupationEvidence.prescribedCalendarStateLaw
        germ entry startEpoch valid stage =
      germ.scheduledFinkStateLaw startEpoch valid entry stage := by
  rfl

omit [DecidableEq G.State] in
/-- Exact prescribed-law recurrence under the epoch-frozen Fink state
kernel. -/
theorem prescribedCalendarStateLaw_succ
    (germ : G.AnalyticBellmanGerm)
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (stage : ℕ) :
    MovingEndpointOccupationEvidence.prescribedCalendarStateLaw
          germ entry startEpoch valid (stage + 1) =
      (MovingEndpointOccupationEvidence.prescribedCalendarStateLaw
          germ entry startEpoch valid stage).bind
        (germ.scheduledFinkEpochStateKernel startEpoch valid
          (anytimeEpochIndex stage)) := by
  simpa only [prescribedCalendarStateLaw_eq_scheduledFinkStateLaw] using
    germ.scheduledFinkStateLaw_succ startEpoch valid entry stage

/-- Every scheduled Fink epoch kernel realizes the raw analytic baseline
occupation column at that epoch's shifted parameter. -/
theorem scheduledFinkEpochStateKernel_realizes_rawBaselineOccupationColumn
    (germ : G.AnalyticBellmanGerm)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius) :
    RealizesShiftedRawOccupationColumn
      germ.rawBaselineOccupationColumn startEpoch
      (germ.scheduledFinkEpochStateKernel startEpoch valid) := by
  intro epoch source destination
  have hcolumn :=
    congrFun
      (congrFun
        (germ.rawBaselineOccupationColumn_eq_actual
          (valid epoch)) source)
      destination
  simpa only [scheduledFinkEpochStateKernel,
    actualOccupationColumn, id_eq] using hcolumn

omit [DecidableEq G.State] in
/-- The forward raw-column calendar cost is exactly the prescribed endpoint
transport sum. -/
theorem cumulativeExpectedScheduledCost_endpointTransportCharge_true
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (horizon : ℕ) :
    cumulativeExpectedScheduledCost
        (MovingEndpointOccupationEvidence.prescribedCalendarStateLaw
          germ entry startEpoch valid)
        (shiftedRawColumnCharge
          (germ.endpointTransportCharge who entry true)
          startEpoch)
        horizon =
      expectedPrescribedCalendarEndpointTargetTransport
        germ who entry startEpoch valid horizon := by
  rw [← MovingEndpointOccupationEvidence.cumulativeEndpointTransport_prescribedCalendarStateLaw
      germ who entry startEpoch valid horizon]
  unfold cumulativeExpectedScheduledCost
    MovingEndpointOccupationEvidence.cumulativeEndpointTransport
  apply Finset.sum_congr rfl
  intro stage _
  congr 1

omit [DecidableEq G.State] in
/-- The reverse raw-column calendar cost is the negative prescribed endpoint
transport sum. -/
theorem cumulativeExpectedScheduledCost_endpointTransportCharge_false
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (horizon : ℕ) :
    cumulativeExpectedScheduledCost
        (MovingEndpointOccupationEvidence.prescribedCalendarStateLaw
          germ entry startEpoch valid)
        (shiftedRawColumnCharge
          (germ.endpointTransportCharge who entry false)
          startEpoch)
        horizon =
      -expectedPrescribedCalendarEndpointTargetTransport
        germ who entry startEpoch valid horizon := by
  rw [← MovingEndpointOccupationEvidence.cumulativeEndpointTransport_prescribedCalendarStateLaw
      germ who entry startEpoch valid horizon]
  unfold cumulativeExpectedScheduledCost
    MovingEndpointOccupationEvidence.cumulativeEndpointTransport
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro stage _
  change
    expect
        (MovingEndpointOccupationEvidence.prescribedCalendarStateLaw
          germ entry startEpoch valid stage)
        (fun state =>
          germ.endpointValue entry who -
            germ.endpointValue state who) =
      -expect
        (MovingEndpointOccupationEvidence.prescribedCalendarStateLaw
          germ entry startEpoch valid stage)
        (fun state =>
          germ.endpointValue state who -
            germ.endpointValue entry who)
  rw [expect_sub, expect_sub, expect_const]
  ring

/-- Two fixed-start raw-column accounts, one for each endpoint-transport
orientation, imply the exact prescribed two-sided transport boundary. -/
theorem hasSublinear_prescribedEndpointTransport_of_two_fixedAccounts
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (forwardAccount :
      HasFixedStartRawColumnCalendarChargeAccount
        germ.rawBaselineOccupationColumn
        (germ.endpointTransportCharge who entry true)
        startEpoch)
    (reverseAccount :
      HasFixedStartRawColumnCalendarChargeAccount
        germ.rawBaselineOccupationColumn
        (germ.endpointTransportCharge who entry false)
        startEpoch) :
    IsAsymptoticallySublinear fun horizon =>
      |expectedPrescribedCalendarEndpointTargetTransport
        germ who entry startEpoch valid horizon| := by
  let law : ℕ → PMF G.State :=
    MovingEndpointOccupationEvidence.prescribedCalendarStateLaw
      germ entry startEpoch valid
  let kernel : ℕ → G.State → PMF G.State :=
    germ.scheduledFinkEpochStateKernel startEpoch valid
  have realizes :
      RealizesShiftedRawOccupationColumn
        germ.rawBaselineOccupationColumn startEpoch kernel := by
    exact
      germ.scheduledFinkEpochStateKernel_realizes_rawBaselineOccupationColumn
        startEpoch valid
  have law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind
            (kernel (anytimeEpochIndex stage)) := by
    intro stage
    exact germ.prescribedCalendarStateLaw_succ
      entry startEpoch valid stage
  obtain ⟨forwardPotential, forwardFirstGood, forwardAt⟩ :=
    forwardAccount
  obtain ⟨reversePotential, reverseFirstGood, reverseAt⟩ :=
    reverseAccount
  obtain ⟨forwardBound, forwardSublinear⟩ :=
    forwardAt kernel realizes law law_step
  obtain ⟨reverseBound, reverseSublinear⟩ :=
    reverseAt kernel realizes law law_step
  let forwardBill : ℕ → ℝ :=
    eventualMovingKernelEpochBill
      (shiftedRawColumnCharge
        (germ.endpointTransportCharge who entry true)
        startEpoch)
      (forwardPotential.shiftedRawColumnPotential startEpoch)
      forwardFirstGood
  let reverseBill : ℕ → ℝ :=
    eventualMovingKernelEpochBill
      (shiftedRawColumnCharge
        (germ.endpointTransportCharge who entry false)
        startEpoch)
      (reversePotential.shiftedRawColumnPotential startEpoch)
      reverseFirstGood
  let forwardBudget : ℕ → ℝ :=
    completedAndCurrentEpochBudget forwardBill
  let reverseBudget : ℕ → ℝ :=
    completedAndCurrentEpochBudget reverseBill
  have forwardBudget_nonneg :
      ∀ horizon, 0 ≤ forwardBudget horizon := by
    intro horizon
    unfold forwardBudget completedAndCurrentEpochBudget
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro epoch _
      simpa only [forwardBill] using
        eventualMovingKernelEpochBill_nonneg
          (shiftedRawColumnCharge
            (germ.endpointTransportCharge who entry true)
            startEpoch)
          (forwardPotential.shiftedRawColumnPotential startEpoch)
          forwardFirstGood epoch
    · simpa only [forwardBill] using
        eventualMovingKernelEpochBill_nonneg
          (shiftedRawColumnCharge
            (germ.endpointTransportCharge who entry true)
            startEpoch)
          (forwardPotential.shiftedRawColumnPotential startEpoch)
          forwardFirstGood (anytimeEpochIndex horizon)
  have reverseBudget_nonneg :
      ∀ horizon, 0 ≤ reverseBudget horizon := by
    intro horizon
    unfold reverseBudget completedAndCurrentEpochBudget
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro epoch _
      simpa only [reverseBill] using
        eventualMovingKernelEpochBill_nonneg
          (shiftedRawColumnCharge
            (germ.endpointTransportCharge who entry false)
            startEpoch)
          (reversePotential.shiftedRawColumnPotential startEpoch)
          reverseFirstGood epoch
    · simpa only [reverseBill] using
        eventualMovingKernelEpochBill_nonneg
          (shiftedRawColumnCharge
            (germ.endpointTransportCharge who entry false)
            startEpoch)
          (reversePotential.shiftedRawColumnPotential startEpoch)
          reverseFirstGood (anytimeEpochIndex horizon)
  have absolute_le :
      ∀ horizon,
        |expectedPrescribedCalendarEndpointTargetTransport
            germ who entry startEpoch valid horizon| ≤
          forwardBudget horizon + reverseBudget horizon := by
    intro horizon
    have hforward := forwardBound horizon
    have hreverse := reverseBound horizon
    change
      cumulativeExpectedScheduledCost law
          (shiftedRawColumnCharge
            (germ.endpointTransportCharge who entry true)
            startEpoch)
          horizon ≤
        forwardBudget horizon at hforward
    change
      cumulativeExpectedScheduledCost law
          (shiftedRawColumnCharge
            (germ.endpointTransportCharge who entry false)
            startEpoch)
          horizon ≤
        reverseBudget horizon at hreverse
    rw [cumulativeExpectedScheduledCost_endpointTransportCharge_true]
      at hforward
    rw [cumulativeExpectedScheduledCost_endpointTransportCharge_false]
      at hreverse
    rw [abs_le]
    constructor <;>
      linarith [forwardBudget_nonneg horizon,
        reverseBudget_nonneg horizon]
  apply IsAsymptoticallySublinear.of_nonneg_le
  · exact fun _ => abs_nonneg _
  · exact absolute_le
  · exact forwardSublinear.add reverseSublinear

/-- The circulation and its punctured positive-charge class selected from a
failure of prescribed endpoint transport. -/
structure PrescribedEndpointTransportCirculationEvidence
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State) where
  forward : Bool
  circulation :
    AnalyticPositiveChargedCirculation
      germ.rawBaselineOccupationColumn
      (germ.endpointTransportCharge who entry forward)
  chargedClass :
    PuncturedBaselinePositiveChargedClass germ
      (germ.endpointTransportCharge who entry forward)

/-- Failure of the exact prescribed-calendar endpoint-transport boundary
for one player forces a positive analytic baseline circulation in one fixed
orientation.  The same witness yields a punctured communicating class with
positive aggregate oriented endpoint charge. -/
theorem
    exists_prescribedEndpointTransportCirculation_of_not_sublinear
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (failure :
      ¬IsAsymptoticallySublinear fun horizon =>
        |expectedPrescribedCalendarEndpointTargetTransport
          germ who entry startEpoch valid horizon|) :
    Nonempty
      (PrescribedEndpointTransportCirculationEvidence
        germ who entry) := by
  have forwardAlternative :=
    analyticPositiveChargedRawOccupationCirculation_xor_fixedCalendarChargeAccount
      germ.rawBaselineOccupationColumn
      (germ.endpointTransportCharge who entry true)
      startEpoch
      germ.analytic_rawBaselineOccupationColumn
      (germ.analytic_endpointTransportCharge who entry true)
  rw [xor_def] at forwardAlternative
  rcases forwardAlternative with
      ⟨forwardCirculation, -⟩ |
      ⟨forwardAccount, -⟩
  · obtain ⟨circulation⟩ := forwardCirculation
    obtain ⟨chargedClass⟩ :=
      germ.exists_puncturedEndpointTransportChargedClass
        who entry true circulation
    exact ⟨{
      forward := true
      circulation := circulation
      chargedClass := chargedClass
    }⟩
  · have reverseAlternative :=
      analyticPositiveChargedRawOccupationCirculation_xor_fixedCalendarChargeAccount
        germ.rawBaselineOccupationColumn
        (germ.endpointTransportCharge who entry false)
        startEpoch
        germ.analytic_rawBaselineOccupationColumn
        (germ.analytic_endpointTransportCharge who entry false)
    rw [xor_def] at reverseAlternative
    rcases reverseAlternative with
        ⟨reverseCirculation, -⟩ |
        ⟨reverseAccount, -⟩
    · obtain ⟨circulation⟩ := reverseCirculation
      obtain ⟨chargedClass⟩ :=
        germ.exists_puncturedEndpointTransportChargedClass
          who entry false circulation
      exact ⟨{
        forward := false
        circulation := circulation
        chargedClass := chargedClass
      }⟩
    · exact
        (failure
          (germ.hasSublinear_prescribedEndpointTransport_of_two_fixedAccounts
            who entry startEpoch valid
            forwardAccount reverseAccount)).elim

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
