/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Endpoint.AnalyticPrescribedEndpointTailChargedClass
import UniformEquilibrium.VanishingDiscount.Analytic.Endpoint.AnalyticPrescribedEndpointTransportCirculation
import Math.Probability.AnalyticRestrictedSourceCalendarAccount

/-!
# Tail-reachable alternative for prescribed endpoint transport

The unrestricted endpoint-transport alternative can select a circulation in
a component unrelated to the actual prescribed state law.  This file applies
the analytic charged-flow alternative only after restricting source rows to
the stabilized tail support of that law.

For either orientation of one player's endpoint displacement, the resulting
branch is:

* a positive analytic circulation on the tail source subtype, together with
  a positive aggregate-charge class reachable in support from some
  positive-mass tail state; or
* a one-sided sublinear account on the exact original prescribed calendar.

Applying both orientations shows that failure of absolute prescribed
endpoint transport forces the first branch.  The finite prefix before
support and potential stabilization is paid explicitly by the account.

The selected class is still not a legal recursive child.  Whole-vector
target transport, a strategic entry/continuation interface, and strict rank
descent remain separate obligations.
-/

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

/-- One-sided sublinear budget for one orientation of the exact prescribed
endpoint-transport sum. -/
structure PrescribedEndpointTailChargeAccount
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (forward : Bool) where
  budget : ℕ → ℝ
  budget_nonneg : ∀ horizon, 0 ≤ budget horizon
  charge_le_budget :
    ∀ horizon,
      cumulativeExpectedScheduledCost
          (MovingEndpointOccupationEvidence.prescribedCalendarStateLaw
            germ entry startEpoch valid)
          (shiftedRawColumnCharge
            (germ.endpointTransportCharge who entry forward)
            startEpoch)
          horizon ≤
        budget horizon
  budget_sublinear : IsAsymptoticallySublinear budget

/-- Scheduled Fink rows restricted to the fixed tail source subtype realize
the restricted raw occupation column on the unchanged shifted calendar. -/
theorem tailRestrictedScheduledKernel_realizes
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid) :
    RealizesShiftedRestrictedRawOccupationColumn
      (tailRestrictedBaselineOccupationColumn tail)
      (fun state : PrescribedFinkTailState tail => state.1)
      startEpoch
      (fun epoch state =>
        germ.scheduledFinkEpochStateKernel
          startEpoch valid epoch state.1) := by
  intro epoch source destination
  exact
    germ.scheduledFinkEpochStateKernel_realizes_rawBaselineOccupationColumn
      startEpoch valid epoch source.1 destination

omit [DecidableEq G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
private theorem prescribedEndpointTailChargeAccount_budget_nonneg
    (law : ℕ → PMF G.State)
    (cost potential : ℕ → G.State → ℝ)
    (accountStart horizon : ℕ) :
    0 ≤
      completedAndCurrentEpochBudget
        (supportedMovingKernelEpochBill
          law cost potential accountStart)
        horizon := by
  unfold completedAndCurrentEpochBudget
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro epoch _
    unfold supportedMovingKernelEpochBill
    split
    · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · unfold epochPotentialBill finiteStatePotentialBound
      positivity
  · unfold supportedMovingKernelEpochBill
    split
    · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · unfold epochPotentialBill finiteStatePotentialBound
      positivity

/-- The scaled-potential branch on the tail source subtype supplies a
one-sided sublinear account for the original ambient-state charge. -/
theorem exists_prescribedEndpointTailChargeAccount_of_scaledPotential
    {germ : G.AnalyticBellmanGerm}
    {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (tail :
      PrescribedFinkTailReachableSupport
        germ entry startEpoch valid)
    (who : ι) (forward : Bool)
    (P :
      AnalyticScaledChargedOccupationPotential
        (tailRestrictedBaselineOccupationColumn tail)
        (tailRestrictedEndpointTransportCharge tail who forward)) :
    Nonempty
      (PrescribedEndpointTailChargeAccount
        germ who entry startEpoch valid forward) := by
  let law : ℕ → PMF G.State :=
    MovingEndpointOccupationEvidence.prescribedCalendarStateLaw
      germ entry startEpoch valid
  let kernel : ℕ → G.State → PMF G.State :=
    germ.scheduledFinkEpochStateKernel startEpoch valid
  let restrictedKernel :
      ℕ → PrescribedFinkTailState tail → PMF G.State :=
    fun epoch state => kernel epoch state.1
  let cost : ℕ → G.State → ℝ :=
    shiftedRawColumnCharge
      (germ.endpointTransportCharge who entry forward)
      startEpoch
  let potential : ℕ → G.State → ℝ :=
    P.shiftedRestrictedPuncturedPotential startEpoch
  have realizes :
      RealizesShiftedRestrictedRawOccupationColumn
        (tailRestrictedBaselineOccupationColumn tail)
        (fun state : PrescribedFinkTailState tail => state.1)
        startEpoch restrictedKernel := by
    exact tailRestrictedScheduledKernel_realizes tail
  obtain ⟨firstGoodEpoch, charge_le_drift⟩ :=
    P.exists_firstGoodEpoch_charge_le_semanticKernel_drift
      (fun state : PrescribedFinkTailState tail => state.1)
      startEpoch restrictedKernel realizes
  let accountStart := max tail.supportEpoch firstGoodEpoch
  have law_step :
      ∀ stage,
        law (stage + 1) =
          (law stage).bind
            (kernel (anytimeEpochIndex stage)) := by
    intro stage
    exact germ.prescribedCalendarStateLaw_succ
      entry startEpoch valid stage
  have cost_le_drift_on_support :
      ∀ epoch, accountStart ≤ epoch →
        ∀ offset, offset < anytimeEpochLength epoch →
          ∀ state,
            state ∈
                (law
                  (epochStart anytimeEpochLength epoch + offset)).support →
              cost epoch state ≤
                expect (kernel epoch state) (potential epoch) -
                  potential epoch state := by
    intro epoch accountStart_le offset offset_lt state state_mem
    have supportEpoch_le : tail.supportEpoch ≤ epoch :=
      (le_max_left tail.supportEpoch firstGoodEpoch).trans
        accountStart_le
    have firstGood_le : firstGoodEpoch ≤ epoch :=
      (le_max_right tail.supportEpoch firstGoodEpoch).trans
        accountStart_le
    have supportStart_le :
        tail.supportStart ≤
          epochStart anytimeEpochLength epoch + offset := by
      exact
        (monotone_anytimeEpochStart supportEpoch_le).trans
          (Nat.le_add_right
            (epochStart anytimeEpochLength epoch) offset)
    have state_ne :
        germ.scheduledFinkStateLaw
            startEpoch valid entry
            (epochStart anytimeEpochLength epoch + offset)
            state ≠ 0 := by
      have state_mem' := state_mem
      change
        state ∈
          (MovingEndpointOccupationEvidence.prescribedCalendarStateLaw
            germ entry startEpoch valid
            (epochStart anytimeEpochLength epoch + offset)).support
        at state_mem'
      rw [germ.prescribedCalendarStateLaw_eq_scheduledFinkStateLaw
        entry startEpoch valid
        (epochStart anytimeEpochLength epoch + offset)] at state_mem'
      simpa only [PMF.mem_support_iff] using state_mem'
    have state_tail : state ∈ tail.states :=
      tail.scheduledFinkStateLaw_ne_zero_imp_mem_states
        supportStart_le state_ne
    have drift :=
      charge_le_drift epoch firstGood_le
        ⟨state, state_tail⟩
    simpa only [cost, potential, restrictedKernel,
      tailRestrictedEndpointTransportCharge,
      shiftedRawColumnCharge] using drift
  obtain ⟨bound, budget_sublinear⟩ :=
    exists_sublinearSupportedMovingKernelCostAccount
      law kernel cost potential law_step accountStart
      cost_le_drift_on_support
      (P.tendsto_shiftedRestrictedPotential_bill_div_length
        startEpoch)
  let budget : ℕ → ℝ :=
    completedAndCurrentEpochBudget
      (supportedMovingKernelEpochBill
        law cost potential accountStart)
  refine ⟨{
    budget := budget
    budget_nonneg := ?_
    charge_le_budget := ?_
    budget_sublinear := ?_
  }⟩
  · intro horizon
    exact prescribedEndpointTailChargeAccount_budget_nonneg
      law cost potential accountStart horizon
  · intro horizon
    exact bound horizon
  · exact budget_sublinear

omit [DecidableEq G.State] in
/-- Accounts in both charge orientations force the absolute prescribed
endpoint-transport sum to be sublinear. -/
theorem hasSublinear_prescribedEndpointTransport_of_two_tailAccounts
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (forwardAccount :
      PrescribedEndpointTailChargeAccount
        germ who entry startEpoch valid true)
    (reverseAccount :
      PrescribedEndpointTailChargeAccount
        germ who entry startEpoch valid false) :
    IsAsymptoticallySublinear fun horizon =>
      |expectedPrescribedCalendarEndpointTargetTransport
        germ who entry startEpoch valid horizon| := by
  have absolute_le :
      ∀ horizon,
        |expectedPrescribedCalendarEndpointTargetTransport
            germ who entry startEpoch valid horizon| ≤
          forwardAccount.budget horizon +
            reverseAccount.budget horizon := by
    intro horizon
    have forward := forwardAccount.charge_le_budget horizon
    have reverse := reverseAccount.charge_le_budget horizon
    rw [cumulativeExpectedScheduledCost_endpointTransportCharge_true]
      at forward
    rw [cumulativeExpectedScheduledCost_endpointTransportCharge_false]
      at reverse
    rw [abs_le]
    constructor <;>
      linarith [forwardAccount.budget_nonneg horizon,
        reverseAccount.budget_nonneg horizon]
  apply IsAsymptoticallySublinear.of_nonneg_le
  · exact fun _ => abs_nonneg _
  · exact absolute_le
  · exact forwardAccount.budget_sublinear.add
      reverseAccount.budget_sublinear

/-- Concrete tail-reachable evidence selected from failed prescribed
endpoint transport. -/
structure TailReachableEndpointTransportCirculationEvidence
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius) where
  tail :
    PrescribedFinkTailReachableSupport
      germ entry startEpoch valid
  forward : Bool
  circulation :
    AnalyticPositiveChargedCirculation
      (tailRestrictedBaselineOccupationColumn tail)
      (tailRestrictedEndpointTransportCharge tail who forward)
  chargedClass :
    PuncturedLawSupportedRestrictedPositiveChargedClass
      (tailRestrictedBaselineOccupationColumn tail)
      (tailRestrictedEndpointTransportCharge tail who forward)
      (fun state : PrescribedFinkTailState tail => state.1)
      (fun parameter =>
        parameter ∈ Ioo (0 : ℝ) germ.radius)
      tail.tailLaw

namespace TailReachableEndpointTransportCirculationEvidence

/-- The selected aggregate-positive class is rooted in the actual
tail-boundary law: some positive-mass state support-reaches its
representative under the selected semantic row family. -/
theorem exists_tailLaw_seed_reaching_representative
    {germ : G.AnalyticBellmanGerm}
    {who : ι} {entry : G.State}
    {startEpoch : ℕ}
    {valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius}
    (data :
      TailReachableEndpointTransportCirculationEvidence
        germ who entry startEpoch valid) :
    ∃ seed, data.tail.tailLaw seed ≠ 0 ∧
      AvailableReachable
        data.chargedClass.semantic.kernel
        (fun state : PrescribedFinkTailState data.tail => state.1)
        seed data.chargedClass.positiveClass.representative.1 :=
  data.chargedClass.exists_tailLaw_seed_reaching_representative

end TailReachableEndpointTransportCirculationEvidence

/-- Failure of the exact prescribed-calendar endpoint-transport boundary
forces a positive circulation after restricting rows to the actual
tail-reachable support.  Its positive aggregate-charge class has a
representative reachable in support from some positive-mass state of the
tail-boundary law. -/
theorem
    exists_tailReachableEndpointTransportCirculation_of_not_sublinear
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
      (TailReachableEndpointTransportCirculationEvidence
        germ who entry startEpoch valid) := by
  obtain ⟨tail⟩ :=
    germ.exists_prescribedFinkTailReachableSupport
      entry startEpoch valid
  have forwardAlternative :=
    analyticRestrictedSourcePositiveCirculation_xor_scaledPotential
      (tailRestrictedBaselineOccupationColumn tail)
      (tailRestrictedEndpointTransportCharge tail who true)
      (analytic_tailRestrictedBaselineOccupationColumn tail)
      (analytic_tailRestrictedEndpointTransportCharge tail who true)
  rw [xor_def] at forwardAlternative
  rcases forwardAlternative with
      ⟨forwardCirculation, -⟩ |
      ⟨forwardPotential, -⟩
  · obtain ⟨circulation⟩ := forwardCirculation
    obtain ⟨chargedClass⟩ :=
      exists_tailReachableEndpointTransportChargedClass
        tail who true circulation
    exact ⟨{
      tail := tail
      forward := true
      circulation := circulation
      chargedClass := chargedClass
    }⟩
  · obtain ⟨forwardAccount⟩ :=
      exists_prescribedEndpointTailChargeAccount_of_scaledPotential
        tail who true (Classical.choice forwardPotential)
    have reverseAlternative :=
      analyticRestrictedSourcePositiveCirculation_xor_scaledPotential
        (tailRestrictedBaselineOccupationColumn tail)
        (tailRestrictedEndpointTransportCharge tail who false)
        (analytic_tailRestrictedBaselineOccupationColumn tail)
        (analytic_tailRestrictedEndpointTransportCharge tail who false)
    rw [xor_def] at reverseAlternative
    rcases reverseAlternative with
        ⟨reverseCirculation, -⟩ |
        ⟨reversePotential, -⟩
    · obtain ⟨circulation⟩ := reverseCirculation
      obtain ⟨chargedClass⟩ :=
        exists_tailReachableEndpointTransportChargedClass
          tail who false circulation
      exact ⟨{
        tail := tail
        forward := false
        circulation := circulation
        chargedClass := chargedClass
      }⟩
    · obtain ⟨reverseAccount⟩ :=
        exists_prescribedEndpointTailChargeAccount_of_scaledPotential
          tail who false (Classical.choice reversePotential)
      exact False.elim <| failure <|
        hasSublinear_prescribedEndpointTransport_of_two_tailAccounts
          germ who entry startEpoch valid
          forwardAccount reverseAccount

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
