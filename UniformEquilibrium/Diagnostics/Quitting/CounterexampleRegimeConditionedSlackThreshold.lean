/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedFloorViability
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedNegativeTangent

/-!
# The punishment-slack threshold for conditioned negative tangents

Removing a positive phantom boundary exposes two distinct obstructions.  A
conditioned state can cross the punishment floor, and a negative ordinary
tangent can remain a genuine negative delivery gap.  The exact dividing line
between them is the phantom boundary's punishment slack.

At one edge, if both the conditioned continuation and the absorbing delivery
are punishment-rational, then the magnitude of a negative ordinary tangent is
at most

`surviving phantom mass * (boundary - punishment)`.

For a tangent packet this becomes an exact limiting threshold.  A negative
tangent is either covered by the limiting punishment slack, or the selected
period-one absorbing deliveries eventually lie strictly below punishment.  If
the coordinate also carries positive owner mass, the latter deliveries are
simultaneously strictly phase-exploitable.  Thus the uncovered branch cannot
be repaired while retaining its limiting delivery; the covered branch still
requires a genuine phase or support repair.

The second result closes a tempting finite-reset shortcut.  An affine shrink
toward the phantom boundary which preserves the exact conditioned Bellman
coefficients cannot start nontrivially and then rejoin the unshrunk tail at a
finite date.  Any finite repair must change absorbing deliveries or support,
not merely transport a scalar boundary share.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## A finite affine reset is impossible -/

omit [Fintype ι] [DecidableEq ι] in
/-- **No finite affine return.**  If exact coefficient transport is preserved
through a finite block and the terminal scale is the unshrunk scale `1`, then
the initial scale was already `1`.  No positivity assumptions are needed: this
is the exact telescoping boundary-share invariant. -/
theorem quittingConditionedAffineShrink_initialScale_eq_one_of_finiteReturn
    (alpha scale : ℕ → ℝ)
    (htransport : ∀ time,
      (1 - scale time * alpha time) * (1 - scale (time + 1)) =
        1 - scale time)
    (fuel : ℕ) (hreturn : scale fuel = 1) :
    scale 0 = 1 := by
  have hinvariant :=
    quittingConditionedAffineShrink_survival_mul_complement
      alpha scale htransport fuel
  rw [hreturn, sub_self, mul_zero] at hinvariant
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Strict initial shrinking and an exact finite return to the unshrunk tail
are incompatible. -/
theorem not_quittingConditionedAffineShrink_finiteReturn_of_initial_lt_one
    (alpha scale : ℕ → ℝ)
    (htransport : ∀ time,
      (1 - scale time * alpha time) * (1 - scale (time + 1)) =
        1 - scale time)
    (fuel : ℕ) (hinitial : scale 0 < 1) :
    scale fuel ≠ 1 := by
  intro hreturn
  have := quittingConditionedAffineShrink_initialScale_eq_one_of_finiteReturn
    alpha scale htransport fuel hreturn
  linarith

/-! ## The pointwise punishment-slack threshold -/

omit [DecidableEq ι] in
/-- A negative ordinary tangent has three possible readings.  It is a genuine
negative conditioned delivery gap; the conditioned continuation is below its
floor; or its whole magnitude is paid by the surviving phantom share of the
boundary's floor slack. -/
theorem conditionedGap_neg_or_conditionedFloorViolation_or_tangentFunding
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary floor : Payoff ι) (time : ℕ) (who : ι)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (htangent :
      quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        value (time + 1) who < 0) :
    (quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        quittingTailConditionedValue roots value boundary (time + 1) who < 0) ∨
      (quittingTailConditionedValue roots value boundary (time + 1) who <
        floor who) ∨
      -(quittingRootConditionalAbsorbingDelivery reward (roots time) who -
          value (time + 1) who) ≤
        quittingJointSurvivalLimit roots (time + 1) *
          (boundary who - floor who) := by
  rcases conditionedGap_neg_or_strictPhantomFunding_of_tangent_neg
      (reward := reward) roots value boundary time who hnext htangent with
    hgap | ⟨-, hbelowBoundary, hfunding⟩
  · exact Or.inl hgap
  · by_cases hfloor :
      quittingTailConditionedValue roots value boundary (time + 1) who <
        floor who
    · exact Or.inr (Or.inl hfloor)
    · right
      right
      have hfloorSafe : floor who ≤
          quittingTailConditionedValue roots value boundary (time + 1) who :=
        le_of_not_gt hfloor
      have hgapLe :
          boundary who -
              quittingTailConditionedValue roots value boundary
                (time + 1) who ≤
            boundary who - floor who := by
        linarith
      exact hfunding.trans <| mul_le_mul_of_nonneg_left hgapLe
        (quittingJointSurvivalLimit_nonneg roots (time + 1))

omit [DecidableEq ι] in
/-- If the tangent magnitude exceeds the available phantom punishment budget,
then either the negative gap survives conditioning or the conditioned state
violates punishment rationality. -/
theorem conditionedGap_neg_or_conditionedFloorViolation_of_tangent_gt_funding
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary floor : Payoff ι) (time : ℕ) (who : ι)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (htangent :
      quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        value (time + 1) who < 0)
    (huncovered :
      quittingJointSurvivalLimit roots (time + 1) *
          (boundary who - floor who) <
        -(quittingRootConditionalAbsorbingDelivery reward (roots time) who -
          value (time + 1) who)) :
    (quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        quittingTailConditionedValue roots value boundary (time + 1) who < 0) ∨
      quittingTailConditionedValue roots value boundary (time + 1) who <
        floor who := by
  rcases conditionedGap_neg_or_conditionedFloorViolation_or_tangentFunding
      (reward := reward) roots value boundary floor time who hnext htangent with
    hgap | hfloor | hfunding
  · exact Or.inl hgap
  · exact Or.inr hfloor
  · linarith

/-! ## The limiting packet threshold -/

namespace QuittingChargeTangentData

/-- The packet's punishment admissibility threshold is exactly its boundary
slack.  The singleton mixture is the boundary plus the tangent, so a negative
tangent is individually rational precisely when its magnitude fits inside
`boundary - punishment`. -/
theorem punishmentValue_le_singletonMixture_iff_neg_tangent_le_slack
    (data : QuittingChargeTangentData reward) (who : ι) :
    quittingPunishmentValue reward who ≤
        quittingSingletonMixture reward data.mass who ↔
      -data.tangent who ≤
        data.boundary who - quittingPunishmentValue reward who := by
  rw [data.tangent_eq who]
  constructor <;> intro h <;> linarith

end QuittingChargeTangentData

variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

namespace CounterexampleRegimePeriodOneTangentReadout

variable (readout : CounterexampleRegimePeriodOneTangentReadout seam)

/-- The selected root's honest period-one absorbing delivery converges to the
phantom boundary plus the extracted tangent.  This statement deliberately
uses the seam boundary: the abstract readout structure need not identify its
packet's stored boundary field definitionally with the seam limit. -/
theorem periodOneReadoutDelivery_tendsto_boundary_add_tangent (who : ι) :
    Tendsto (fun index ↦
      quittingWindowRestartDelivery reward
        (quittingPeriodOneRootSequence
          (seam.periodOneReadoutRoot readout.start index)) who 0 1)
      atTop (nhds (seam.limit.value who + readout.packet.tangent who)) := by
  have hstartSucc : Tendsto (fun index ↦ readout.start index + 1)
      atTop atTop :=
    Filter.tendsto_atTop_mono
      (fun index ↦ Nat.le_add_right (readout.start index) 1)
      readout.start_tendsto
  have hboundary : Tendsto
      (fun index ↦ (seam.tail (readout.start index + 1)).1.1 who)
      atTop (nhds (seam.limit.value who)) :=
    (seam.value_tendsto who).comp hstartSucc
  have hsum := (readout.tangent_tendsto who).add hboundary
  simpa [QuittingCounterexampleSeamWitness.periodOneReadoutTangent,
    add_comm] using hsum

/-- The limiting delivery is punishment-rational exactly when the negative
tangent magnitude fits in the seam boundary's punishment slack. -/
theorem punishmentValue_le_boundary_add_tangent_iff_neg_tangent_le_slack
    (who : ι) :
    quittingPunishmentValue reward who ≤
        seam.limit.value who + readout.packet.tangent who ↔
      -readout.packet.tangent who ≤
        seam.limit.value who - quittingPunishmentValue reward who := by
  constructor <;> intro h <;> linarith

/-- **Limiting punishment threshold.**  A negative tangent is either covered
by the phantom boundary's punishment slack, or the selected repeated-root
deliveries eventually lie strictly below the punishment value. -/
theorem neg_tangent_le_punishmentSlack_or_eventually_delivery_lt_punishment
    (who : ι) (_hnegative : readout.packet.tangent who < 0) :
    -readout.packet.tangent who ≤
        seam.limit.value who - quittingPunishmentValue reward who ∨
      ∀ᶠ index in atTop,
        quittingWindowRestartDelivery reward
            (quittingPeriodOneRootSequence
              (seam.periodOneReadoutRoot readout.start index)) who 0 1 <
          quittingPunishmentValue reward who := by
  by_cases hcovered : -readout.packet.tangent who ≤
      seam.limit.value who - quittingPunishmentValue reward who
  · exact Or.inl hcovered
  · right
    have hunderfloor :
        seam.limit.value who + readout.packet.tangent who <
          quittingPunishmentValue reward who := by
      linarith
    exact (readout.periodOneReadoutDelivery_tendsto_boundary_add_tangent
      seam who).eventually_lt_const hunderfloor

/-- On an active negative coordinate, insufficient punishment slack produces
the full double obstruction eventually: the repeated root is phase-
exploitable and its honest absorbing delivery is below punishment.  Repairing
this branch must therefore change the limiting delivery or the active support.
-/
theorem neg_tangent_le_punishmentSlack_or_eventually_phaseGain_and_underfloor
    (player : ι) (hmass : 0 < readout.packet.mass player)
    (hnegative : readout.packet.tangent player < 0) :
    -readout.packet.tangent player ≤
        seam.limit.value player - quittingPunishmentValue reward player ∨
      ∀ᶠ index in atTop,
        0 < quittingPeriodicWindowBestPhaseStop reward
              (quittingPeriodOneRootSequence
                (seam.periodOneReadoutRoot readout.start index)) player 1 -
            quittingWindowRestartDelivery reward
              (quittingPeriodOneRootSequence
                (seam.periodOneReadoutRoot readout.start index)) player 0 1 ∧
          quittingWindowRestartDelivery reward
              (quittingPeriodOneRootSequence
                (seam.periodOneReadoutRoot readout.start index)) player 0 1 <
            quittingPunishmentValue reward player := by
  rcases readout.neg_tangent_le_punishmentSlack_or_eventually_delivery_lt_punishment
      seam player hnegative with hcovered | hunderfloor
  · exact Or.inl hcovered
  · right
    exact (readout.eventually_phaseGain_of_mass_pos_of_tangent_neg
      seam player hmass hnegative).and hunderfloor

end CounterexampleRegimePeriodOneTangentReadout

end QuittingCounterexampleSeamWitness

end GameTheory
