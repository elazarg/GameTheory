/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentProjectiveGauge

/-!
# The scalar defect left by deleting an active mixing row

The sum-one projective gauge removes the exceptional-divisor scale line, but
it does not make an active mixing equation redundant.  For one player `who`,
the exact scalar left after combining that player's Bellman and mixing rows is

`B_who + (1 - t * a_who) * M_who`.

When the Bellman row vanishes and the player's continue probability is
nonzero, the omitted mixing row is recoverable exactly when this scalar
vanishes.  On the exceptional divisor, after Bellman elimination, the scalar
is the pair-join row.  Packet compatibility kills it only in the packet mass
direction; it does not kill arbitrary zero-sum gauge variations.

An exact finite regression family makes the failure local.  Starting from a
full-support compatible packet, move the normalized leading mass in any
zero-sum direction and choose the uniquely Bellman-forced continuation drift.
Every Bellman row remains exactly zero, while each active mixing row is the
scale parameter times its pair-join matrix row.  If all retained rows kill the
variation and the deleted row does not, every nonzero point of this family is
a reduced zero but not a full zero, and the family passes through the packet
base at parameter zero.

Thus deleting one row is honest only with an additional scalar-defect
identity.  No strategic realization, global return, or automatic recovery
from first-order packet compatibility is asserted.
-/

noncomputable section

open Finset Filter Set Topology

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Exact omitted-row defect -/

/-- Scalar obstruction left after eliminating one active mixing row with its
Bellman row.  The coefficient is the player's own continue probability. -/
def quittingOmittedMixingDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (boundary : Payoff ι) (t : ℝ) (leading drift : ι → ℝ)
    (who : ι) : ℝ :=
  quittingBellmanBlowupResidual reward boundary t leading drift who +
    (1 - t * leading who) *
      quittingMixingBlowupResidual reward t leading drift who

/-- With a zero Bellman row and nonzero own continue probability, the omitted
mixing row vanishes exactly when its scalar defect vanishes. -/
theorem quittingMixingBlowupResidual_eq_zero_iff_omittedDefect_eq_zero
    (boundary : Payoff ι) (t : ℝ) (leading drift : ι → ℝ) (who : ι)
    (hbellman :
      quittingBellmanBlowupResidual reward boundary t leading drift who = 0)
    (hcontinue : 1 - t * leading who ≠ 0) :
    quittingMixingBlowupResidual reward t leading drift who = 0 ↔
      quittingOmittedMixingDefect reward boundary t leading drift who = 0 := by
  rw [quittingOmittedMixingDefect, hbellman, zero_add, mul_eq_zero]
  simp [hcontinue]

/-- On the exceptional divisor, the Bellman-forced omitted-row defect is
exactly the finite pair-join row. -/
theorem quittingOmittedMixingDefect_zero_forced_eq_pairJoinRow
    (boundary : Payoff ι) (leadingVariation : ι → ℝ) (who : ι)
    (hpin : boundary who = reward (quittingSingletonTerminal who) who) :
    quittingOmittedMixingDefect reward boundary 0 leadingVariation
        (quittingBellmanForcedLeadingDrift reward boundary leadingVariation)
        who =
      ∑ owner ∈ Finset.univ.erase who,
        leadingVariation owner *
          quittingActiveMixingPairJoinEffect reward who owner := by
  rw [quittingOmittedMixingDefect, zero_mul, sub_zero, one_mul,
    quittingBellmanBlowupResidual_zero,
    quittingMixingBlowupResidual_zero,
    quittingBellmanFirstOrderResidual_forcedLeadingDrift_eq_zero,
    zero_add,
    quittingMixingFirstOrderResidual_forcedLeadingDrift_eq_pairJoinRow
      boundary leadingVariation who hpin]

/-! ## Exact normalized regression through a compatible packet -/

namespace QuittingChargeTangentPacket

/-- Exceptional-divisor normalized family in a supplied leading variation.
The continuation drift is chosen by the Bellman rows, not by an omitted
mixing equation. -/
def deletedMixingRegressionPoint
    (packet : QuittingChargeTangentPacket reward)
    (leadingVariation : ι → ℝ) (scale : ℝ) : QuittingBlowupPoint ι :=
  let leading := packet.mass + scale • leadingVariation
  (0, leading,
    quittingBellmanForcedLeadingDrift reward packet.boundary leading)

/-- The Bellman-forced drift of the packet mass is its canonical unit-scale
continuation drift. -/
theorem bellmanForcedLeadingDrift_mass_eq
    (packet : QuittingChargeTangentPacket reward) :
    quittingBellmanForcedLeadingDrift reward packet.boundary packet.mass =
      packet.blowupContinuationDrift 1 := by
  funext who
  have hrow := packet.bellmanFirstOrderResidual_eq_zero 1 who
  simp only [quittingBellmanFirstOrderResidual, blowupLeading,
    blowupContinuationDrift, one_mul, neg_mul] at hrow
  simp only [quittingBellmanForcedLeadingDrift,
    blowupContinuationDrift, neg_one_mul]
  linarith

/-- The normalized regression family passes through the unit-scale packet
base. -/
@[simp]
theorem deletedMixingRegressionPoint_zero
    (packet : QuittingChargeTangentPacket reward)
    (leadingVariation : ι → ℝ) :
    packet.deletedMixingRegressionPoint leadingVariation 0 =
      packet.blowupBasePoint 1 := by
  rw [deletedMixingRegressionPoint, zero_smul, add_zero,
    packet.bellmanForcedLeadingDrift_mass_eq]
  ext owner <;> simp [blowupBasePoint, blowupLeading]

/-- A zero-sum leading variation stays in the global sum-one projective
slice for every regression parameter. -/
theorem deletedMixingRegressionPoint_leadingTotal
    (packet : QuittingChargeTangentPacket reward)
    (leadingVariation : ι → ℝ)
    (hvariation : ∑ owner, leadingVariation owner = 0) (scale : ℝ) :
    quittingBlowupLeadingTotal
      (packet.deletedMixingRegressionPoint leadingVariation scale).2.1 = 1 := by
  change quittingBlowupLeadingTotal
    (packet.mass + scale • leadingVariation) = 1
  rw [map_add, map_smul, quittingBlowupLeadingTotal_apply,
    packet.mass_sum, quittingBlowupLeadingTotal_apply, hvariation,
    smul_zero, add_zero]

/-- Every Bellman row of the regression family vanishes exactly. -/
theorem deletedMixingRegressionPoint_bellman_eq_zero
    (packet : QuittingChargeTangentPacket reward)
    (leadingVariation : ι → ℝ) (scale : ℝ) (who : ι) :
    quittingBellmanBlowupResidual reward packet.boundary
        (packet.deletedMixingRegressionPoint leadingVariation scale).1
        (packet.deletedMixingRegressionPoint leadingVariation scale).2.1
        (packet.deletedMixingRegressionPoint leadingVariation scale).2.2
        who = 0 := by
  rw [deletedMixingRegressionPoint, quittingBellmanBlowupResidual_zero]
  exact quittingBellmanFirstOrderResidual_forcedLeadingDrift_eq_zero
    packet.boundary _ who

/-- Under full support and packet compatibility, each mixing row of the exact
regression family is the regression parameter times the pair-join row of the
supplied zero-sum variation. -/
theorem deletedMixingRegressionPoint_mixing_eq_scale_mul_pairJoinRow
    (packet : QuittingChargeTangentPacket reward)
    (hfullSupport : ∀ who, 0 < packet.mass who)
    (hcompat : ∀ who,
      quittingActivePairCompatibilityResidual packet who = 0)
    (leadingVariation : ι → ℝ) (scale : ℝ) (who : ι) :
    quittingMixingBlowupResidual reward
        (packet.deletedMixingRegressionPoint leadingVariation scale).1
        (packet.deletedMixingRegressionPoint leadingVariation scale).2.1
        (packet.deletedMixingRegressionPoint leadingVariation scale).2.2
        who =
      scale * ∑ owner ∈ Finset.univ.erase who,
        leadingVariation owner *
          quittingActiveMixingPairJoinEffect reward who owner := by
  have hpin : packet.boundary who =
      reward (quittingSingletonTerminal who) who :=
    packet.positive_mass_pins_boundary who (hfullSupport who)
  change quittingMixingBlowupResidual reward 0
    (packet.mass + scale • leadingVariation)
    (quittingBellmanForcedLeadingDrift reward packet.boundary
      (packet.mass + scale • leadingVariation)) who = _
  rw [quittingMixingBlowupResidual_zero,
    quittingMixingFirstOrderResidual_forcedLeadingDrift_eq_pairJoinRow
      packet.boundary _ who hpin]
  have hmassRow :
      (∑ owner ∈ Finset.univ.erase who,
        packet.mass owner *
          quittingActiveMixingPairJoinEffect reward who owner) = 0 := by
    rw [← packet.activePairCompatibilityResidual_eq_sum_pairJoinEffect
      who (hfullSupport who), hcompat who]
  calc
    (∑ owner ∈ Finset.univ.erase who,
        (packet.mass + scale • leadingVariation) owner *
          quittingActiveMixingPairJoinEffect reward who owner) =
        (∑ owner ∈ Finset.univ.erase who,
          packet.mass owner *
            quittingActiveMixingPairJoinEffect reward who owner) +
          scale * ∑ owner ∈ Finset.univ.erase who,
            leadingVariation owner *
              quittingActiveMixingPairJoinEffect reward who owner := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro owner _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    _ = scale * ∑ owner ∈ Finset.univ.erase who,
        leadingVariation owner *
          quittingActiveMixingPairJoinEffect reward who owner := by
      rw [hmassRow, zero_add]

/-- **Finite deleted-row regression.**  If a zero-sum variation lies in all
retained pair-join rows but not in the omitted row, then every nonzero member
of the exact normalized family satisfies all Bellman rows and all retained
mixing rows, while violating the omitted mixing row.  The family meets the
packet base at parameter zero by `deletedMixingRegressionPoint_zero`.

This is the precise finite obstruction to local exact recovery after deleting
one active mixing equation. -/
theorem deletedMixingRegression_of_pairJoinVariation
    (packet : QuittingChargeTangentPacket reward)
    (hfullSupport : ∀ who, 0 < packet.mass who)
    (hcompat : ∀ who,
      quittingActivePairCompatibilityResidual packet who = 0)
    (omitted : ι) (leadingVariation : ι → ℝ)
    (hvariation : ∑ owner, leadingVariation owner = 0)
    (hretained : ∀ who, who ≠ omitted →
      (∑ owner ∈ Finset.univ.erase who,
        leadingVariation owner *
          quittingActiveMixingPairJoinEffect reward who owner) = 0)
    (homitted :
      (∑ owner ∈ Finset.univ.erase omitted,
        leadingVariation owner *
          quittingActiveMixingPairJoinEffect reward omitted owner) ≠ 0) :
    ∀ scale : ℝ, scale ≠ 0 →
      quittingBlowupLeadingTotal
          (packet.deletedMixingRegressionPoint leadingVariation scale).2.1 = 1 ∧
        (∀ who,
          quittingBellmanBlowupResidual reward packet.boundary
            (packet.deletedMixingRegressionPoint leadingVariation scale).1
            (packet.deletedMixingRegressionPoint leadingVariation scale).2.1
            (packet.deletedMixingRegressionPoint leadingVariation scale).2.2
            who = 0) ∧
        (∀ who, who ≠ omitted →
          quittingMixingBlowupResidual reward
            (packet.deletedMixingRegressionPoint leadingVariation scale).1
            (packet.deletedMixingRegressionPoint leadingVariation scale).2.1
            (packet.deletedMixingRegressionPoint leadingVariation scale).2.2
            who = 0) ∧
        quittingMixingBlowupResidual reward
          (packet.deletedMixingRegressionPoint leadingVariation scale).1
          (packet.deletedMixingRegressionPoint leadingVariation scale).2.1
          (packet.deletedMixingRegressionPoint leadingVariation scale).2.2
          omitted ≠ 0 := by
  intro scale hscale
  refine ⟨packet.deletedMixingRegressionPoint_leadingTotal
      leadingVariation hvariation scale,
    packet.deletedMixingRegressionPoint_bellman_eq_zero
      leadingVariation scale, ?_, ?_⟩
  · intro who hwho
    rw [packet.deletedMixingRegressionPoint_mixing_eq_scale_mul_pairJoinRow
      hfullSupport hcompat leadingVariation scale who,
      hretained who hwho, mul_zero]
  · rw [packet.deletedMixingRegressionPoint_mixing_eq_scale_mul_pairJoinRow
      hfullSupport hcompat leadingVariation scale omitted]
    exact mul_ne_zero hscale homitted

end QuittingChargeTangentPacket

end GameTheory
