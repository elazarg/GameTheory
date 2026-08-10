/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseProductRescaling
import UniformEquilibrium.Quitting.Boundary.Exceptional.BellmanTail

/-!
# Strategic bounds for diffuse product rescaling

This file begins the strategic half of diffuse product rescaling.  The
immediate-Quit channel needs no delicate complementarity calculation on a
singleton-tight boundary coordinate.  The conditioned value stays above the
singleton floor, while forcing the player to Quit differs from the singleton
payoff only when an opponent also quits.  The latter event is bounded by the
rescaled opponent absorption, hence by `card(I)` times the conditioned mesh.

The Continue channel is genuinely subtler.  Its useful estimate must retain
an opponent-absorption factor and uses the exact source mixing equation; no
such assertion is made here.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Immediate Quit differs from the player's singleton payoff by at most
twice the reward bound times opponent absorption. -/
theorem abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
    (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingStationaryFixedOpponentsQuitValue reward root who -
        reward (quittingSingletonTerminal who) who| ≤
      2 * M * quittingRootOpponentAbsorptionMass root who := by
  let roots : ℕ → ι → PMF Bool := fun _ ↦ root
  let continueMass :=
    quittingStationaryFixedOpponentsContinueMass root who
  let solo := reward (quittingSingletonTerminal who) who
  have hanchored :=
    abs_quittingFixedOpponentsQuitValue_sub_continueMass_mul_solo_le
      reward roots who 0 M hM (fun terminal ↦ hreward terminal who)
  change |quittingStationaryFixedOpponentsQuitValue reward root who -
      quittingStationaryFixedOpponentsContinueMass root who *
        reward (quittingSingletonTerminal who) who| ≤
    M * (1 - quittingStationaryFixedOpponentsContinueMass root who) at hanchored
  have hsolo : |solo| ≤ M := hreward (quittingSingletonTerminal who) who
  have hmass0 : 0 ≤ continueMass :=
    quittingStationaryFixedOpponentsContinueMass_nonneg root who
  have hmass1 : continueMass ≤ 1 :=
    quittingStationaryContinueMass_le_one
      (Function.update root who (PMF.pure false))
  have hopen : quittingRootOpponentAbsorptionMass root who =
      1 - continueMass := rfl
  have hsplit :
      quittingStationaryFixedOpponentsQuitValue reward root who - solo =
        (quittingStationaryFixedOpponentsQuitValue reward root who -
            continueMass * solo) +
          (continueMass - 1) * solo := by ring
  rw [hsplit]
  calc
    |(quittingStationaryFixedOpponentsQuitValue reward root who -
          continueMass * solo) + (continueMass - 1) * solo| ≤
        |quittingStationaryFixedOpponentsQuitValue reward root who -
          continueMass * solo| + |(continueMass - 1) * solo| :=
      abs_add_le _ _
    _ ≤ M * (1 - continueMass) +
          (1 - continueMass) * M := by
      apply add_le_add
      · simpa [roots, continueMass, solo] using hanchored
      · rw [abs_mul, abs_of_nonpos (by linarith : continueMass - 1 ≤ 0),
          neg_sub]
        exact mul_le_mul_of_nonneg_left hsolo
          (sub_nonneg.mpr hmass1)
    _ = 2 * M * quittingRootOpponentAbsorptionMass root who := by
      rw [hopen]
      ring

/-- The full absorbing contribution is anchored at the selected player's
singleton payoff up to twice the reward bound times opponent absorption.
The event where the player quits alone cancels exactly. -/
theorem abs_quittingRootAbsorbingContribution_sub_absorption_mul_singleton_le
    (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootAbsorbingContribution reward root who -
        quittingRootAbsorptionMass root *
          reward (quittingSingletonTerminal who) who| ≤
      2 * M * quittingRootOpponentAbsorptionMass root who := by
  let ownQuit := (root who true).toReal
  let ownContinue := (root who false).toReal
  let opponentAbsorption := quittingRootOpponentAbsorptionMass root who
  let quitValue :=
    quittingStationaryFixedOpponentsQuitValue reward root who
  let continueReward :=
    quittingStationaryFixedOpponentsContinueReward reward root who
  let solo := reward (quittingSingletonTerminal who) who
  have hownQuit0 : 0 ≤ ownQuit := ENNReal.toReal_nonneg
  have hownContinue0 : 0 ≤ ownContinue := ENNReal.toReal_nonneg
  have hownSum : ownQuit + ownContinue = 1 := by
    dsimp only [ownQuit, ownContinue]
    linarith [quittingRoot_continueProbability_add_quitProbability root who]
  have hopponentAbsorption0 : 0 ≤ opponentAbsorption := by
    dsimp only [opponentAbsorption]
    exact quittingRootAbsorptionMass_nonneg _
  have hsolo : |solo| ≤ M := hreward (quittingSingletonTerminal who) who
  have hquit :=
    abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
      (reward := reward) root who hM hreward
  change |quitValue - solo| ≤ 2 * M * opponentAbsorption at hquit
  have hcontinue :=
    abs_quittingFixedOpponentsContinueReward_le_hazard
      reward (fun _ => root) who 0 M hM (fun terminal => hreward terminal who)
  change |continueReward| ≤ M * opponentAbsorption at hcontinue
  have hcontinueAnchored :
      |continueReward - opponentAbsorption * solo| ≤
        2 * M * opponentAbsorption := by
    calc
      |continueReward - opponentAbsorption * solo| ≤
          |continueReward| + |opponentAbsorption * solo| := abs_sub _ _
      _ ≤ M * opponentAbsorption + opponentAbsorption * M := by
        apply add_le_add hcontinue
        rw [abs_mul, abs_of_nonneg hopponentAbsorption0]
        exact mul_le_mul_of_nonneg_left hsolo hopponentAbsorption0
      _ = 2 * M * opponentAbsorption := by ring
  have hmix : quittingRootAbsorbingContribution reward root who =
      ownQuit * quitValue + ownContinue * continueReward := by
    have h := quittingRootSuccessorPayoff_eq_endpointMix
      reward (0 : Payoff ι) root who
    simpa only [quittingRootSuccessorPayoff,
      quittingRootAbsorbingContribution,
      quittingRootQuitPayoff, quittingRootContinuePayoff,
      quittingStationaryFixedOpponentsQuitValue,
      quittingStationaryFixedOpponentsContinueReward,
      quittingFixedOpponentsQuitValue,
      quittingFixedOpponentsContinueReward, ownQuit, ownContinue,
      quitValue, continueReward] using h
  have habsorption :=
    quittingRootAbsorptionMass_eq_opponentAbsorption_add root who
  have hsplit :
      quittingRootAbsorbingContribution reward root who -
          quittingRootAbsorptionMass root * solo =
        ownQuit * (quitValue - solo) +
          ownContinue * (continueReward - opponentAbsorption * solo) := by
    rw [hmix, habsorption]
    rw [show ownContinue = 1 - ownQuit by linarith [hownSum]]
    dsimp only [ownQuit, opponentAbsorption]
    ring
  rw [hsplit]
  calc
    |ownQuit * (quitValue - solo) +
        ownContinue * (continueReward - opponentAbsorption * solo)| ≤
      ownQuit * |quitValue - solo| +
        ownContinue * |continueReward - opponentAbsorption * solo| := by
      calc
        |ownQuit * (quitValue - solo) +
            ownContinue * (continueReward - opponentAbsorption * solo)| ≤
          |ownQuit * (quitValue - solo)| +
            |ownContinue * (continueReward - opponentAbsorption * solo)| :=
          abs_add_le _ _
        _ = ownQuit * |quitValue - solo| +
            ownContinue * |continueReward - opponentAbsorption * solo| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hownQuit0,
            abs_of_nonneg hownContinue0]
    _ ≤ ownQuit * (2 * M * opponentAbsorption) +
        ownContinue * (2 * M * opponentAbsorption) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hquit hownQuit0)
        (mul_le_mul_of_nonneg_left hcontinueAnchored hownContinue0)
    _ ≤ 2 * M * opponentAbsorption := by
      rw [← add_mul, hownSum, one_mul]

/-- Conditioned absorbing delivery is anchored at the singleton payoff after
multiplication by its conditioned absorption coefficient. -/
theorem abs_conditionedWeight_mul_delivery_sub_singleton_le
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hrootAbsorption : 0 < quittingRootAbsorptionMass (roots time))
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    |quittingTailConditionedAbsorptionWeight roots time *
        (quittingRootConditionalAbsorbingDelivery reward (roots time) who -
          reward (quittingSingletonTerminal who) who)| ≤
      2 * M * quittingTailConditionedOpponentWeight roots time who := by
  have hanchored :=
    abs_quittingRootAbsorbingContribution_sub_absorption_mul_singleton_le
      (reward := reward) (roots time) who hM hreward
  unfold quittingTailConditionedAbsorptionWeight
    quittingRootConditionalAbsorbingDelivery
    quittingTailConditionedOpponentWeight
  rw [show quittingRootAbsorptionMass (roots time) /
        quittingTailEventualAbsorption roots time *
          (quittingRootAbsorbingContribution reward (roots time) who /
              quittingRootAbsorptionMass (roots time) -
            reward (quittingSingletonTerminal who) who) =
      (quittingRootAbsorbingContribution reward (roots time) who -
        quittingRootAbsorptionMass (roots time) *
          reward (quittingSingletonTerminal who) who) /
        quittingTailEventualAbsorption roots time by
      field_simp [hrootAbsorption.ne', hpositive.ne']]
  rw [abs_div, abs_of_pos hpositive]
  calc
    |quittingRootAbsorbingContribution reward (roots time) who -
          quittingRootAbsorptionMass (roots time) *
            reward (quittingSingletonTerminal who) who| /
        quittingTailEventualAbsorption roots time ≤
      (2 * M * quittingRootOpponentAbsorptionMass (roots time) who) /
        quittingTailEventualAbsorption roots time :=
      div_le_div_of_nonneg_right hanchored hpositive.le
    _ = 2 * M *
        (quittingRootOpponentAbsorptionMass (roots time) who /
          quittingTailEventualAbsorption roots time) := by ring

/-- An active tight coordinate also pins the next conditioned state.  The
current state and the absorption delivery are both anchored at the singleton;
the exact conditioned recursion then transports this control across a row
whose conditioned absorption weight is at most one half. -/
theorem abs_quittingTailConditionedValue_succ_sub_singleton_le
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (time : ℕ) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (hactive : 0 < (roots time who true).toReal)
    (htight : boundary who = quittingSoloBaseline reward who)
    (hsmall : quittingTailConditionedAbsorptionWeight roots time ≤ 1 / 2) :
    |quittingTailConditionedValue roots value boundary (time + 1) who -
        reward (quittingSingletonTerminal who) who| ≤
      8 * M * quittingTailConditionedOpponentWeight roots time who := by
  let alpha := quittingTailConditionedAbsorptionWeight roots time
  let nextValue :=
    quittingTailConditionedValue roots value boundary (time + 1) who
  let currentValue :=
    quittingTailConditionedValue roots value boundary time who
  let delivery :=
    quittingRootConditionalAbsorbingDelivery reward (roots time) who
  let solo := reward (quittingSingletonTerminal who) who
  have habsorption : 0 < quittingRootAbsorptionMass (roots time) :=
    lt_of_lt_of_le hactive
      (quittingRoot_quitProbability_le_absorptionMass (roots time) who)
  have hpin : boundary who = solo := by
    simpa [solo, quittingSoloBaseline, quittingSoloReward,
      quittingSingletonTerminal] using htight
  have hcurrentGapRaw :=
    abs_quittingTailConditionedValue_sub_singleton_le
      roots value boundary hpolicy hnash hreward time who hcurrent
        hactive hpin
  have hcurrentGap : |currentValue - solo| ≤
      2 * M * quittingTailConditionedOpponentWeight roots time who := by
    calc
      |currentValue - solo| ≤
          (2 * M * quittingRootOpponentAbsorptionMass (roots time) who) /
            quittingTailEventualAbsorption roots time := by
        simpa only [currentValue, solo] using hcurrentGapRaw
      _ = 2 * M * quittingTailConditionedOpponentWeight roots time who := by
        unfold quittingTailConditionedOpponentWeight
        ring
  have hdeliveryGap :=
    abs_conditionedWeight_mul_delivery_sub_singleton_le
      (reward := reward) roots time who hM hreward habsorption hcurrent
  have hstep := congrFun
    (quittingTailConditionedValue_step roots value boundary hpolicy time
      habsorption hcurrent hnext) who
  have hweights :=
    quittingTailConditionedWeights_add roots time hcurrent
  have hidentity :
      (1 - alpha) * (nextValue - solo) =
        (currentValue - solo) - alpha * (delivery - solo) := by
    dsimp only [alpha, nextValue, currentValue, delivery, solo]
    rw [hstep]
    rw [show quittingTailConditionedContinuationWeight roots time =
        1 - quittingTailConditionedAbsorptionWeight roots time by linarith]
    ring
  have hweighted : |(1 - alpha) * (nextValue - solo)| ≤
      4 * M * quittingTailConditionedOpponentWeight roots time who := by
    rw [hidentity]
    calc
      |(currentValue - solo) - alpha * (delivery - solo)| ≤
          |currentValue - solo| + |alpha * (delivery - solo)| :=
        abs_sub _ _
      _ ≤ 2 * M * quittingTailConditionedOpponentWeight roots time who +
          2 * M * quittingTailConditionedOpponentWeight roots time who := by
        exact add_le_add hcurrentGap hdeliveryGap
      _ = 4 * M * quittingTailConditionedOpponentWeight roots time who := by
        ring
  have halpha0 : 0 ≤ alpha :=
    quittingTailConditionedAbsorptionWeight_nonneg roots time hcurrent
  have hcoefficient : 1 / 2 ≤ 1 - alpha := by
    dsimp only [alpha] at hsmall ⊢
    linarith
  have hfactorAbs : |1 - alpha| = 1 - alpha :=
    abs_of_nonneg (by linarith)
  rw [abs_mul, hfactorAbs] at hweighted
  have hgap0 : 0 ≤ |nextValue - solo| := abs_nonneg _
  have hcharge0 : 0 ≤ quittingTailConditionedOpponentWeight
      roots time who :=
    quittingTailConditionedOpponentWeight_nonneg roots time who hcurrent
  nlinarith [mul_nonneg hM hcharge0]

/-- The rescaled product root's opponent absorption is at most
`card(I) * alpha`. -/
theorem quittingTailDiffuseRescaledRoot_opponentAbsorption_le_card_mul_weight
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingRootOpponentAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) who ≤
      Fintype.card ι *
        quittingTailConditionedAbsorptionWeight roots time := by
  exact (quittingRootOpponentAbsorptionMass_le_absorptionMass
      (quittingTailDiffuseRescaledRoot roots time hpositive) who).trans <|
    (quittingTailDiffuseRescaledRoot_absorptionMass_le_total
      roots time hpositive).trans <|
    quittingTailDiffuseRescaledTotal_le_card_mul_conditionedWeight
      roots time hpositive

/-- **Uniform immediate-Quit error after diffuse rescaling.**  On a boundary
coordinate tight at the player's singleton payoff, source floor viability
makes the conditioned value dominate that singleton payoff.  Immediate Quit
at the rescaled root can therefore improve it by at most
`2 M * card(I) * alpha`.

Strict boundary slack is intentionally excluded: it can subsidize an `O(1)`
conditioned Quit gain and is governed by the separate source-slack gate. -/
theorem quittingStationaryFixedOpponentsQuitValue_rescaledRoot_le_conditionedValue_add
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (time : ℕ) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (htight : boundary who = quittingSoloBaseline reward who)
    (hsourceFloor : quittingSoloBaseline reward who ≤ value time who) :
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingTailDiffuseRescaledRoot roots time hpositive) who ≤
      quittingTailConditionedValue roots value boundary time who +
        2 * M * Fintype.card ι *
          quittingTailConditionedAbsorptionWeight roots time := by
  have hconditionedFloor :=
    quittingSoloBaseline_le_conditionedValue_of_tightBoundary
      roots value boundary time who hpositive htight hsourceFloor
  have hquit :=
    abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
      (reward := reward)
      (quittingTailDiffuseRescaledRoot roots time hpositive) who hM hreward
  have hopponent :=
    quittingTailDiffuseRescaledRoot_opponentAbsorption_le_card_mul_weight
      roots time who hpositive
  rw [abs_le] at hquit
  rw [quittingSoloBaseline_apply] at hconditionedFloor
  change reward (quittingSingletonTerminal who) who ≤
    quittingTailConditionedValue roots value boundary time who at hconditionedFloor
  have hscaled :
      2 * M * quittingRootOpponentAbsorptionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive) who ≤
        2 * M * (Fintype.card ι *
          quittingTailConditionedAbsorptionWeight roots time) :=
    mul_le_mul_of_nonneg_left hopponent
      (mul_nonneg (by norm_num) hM)
  calc
    quittingStationaryFixedOpponentsQuitValue reward
          (quittingTailDiffuseRescaledRoot roots time hpositive) who ≤
        reward (quittingSingletonTerminal who) who +
          2 * M * quittingRootOpponentAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hpositive) who := by
      linarith
    _ ≤ reward (quittingSingletonTerminal who) who +
          2 * M * (Fintype.card ι *
            quittingTailConditionedAbsorptionWeight roots time) := by
      exact add_le_add (le_refl _) hscaled
    _ ≤ quittingTailConditionedValue roots value boundary time who +
          2 * M * Fintype.card ι *
            quittingTailConditionedAbsorptionWeight roots time := by
      calc
        _ ≤ quittingTailConditionedValue roots value boundary time who +
            2 * M * (Fintype.card ι *
              quittingTailConditionedAbsorptionWeight roots time) :=
          add_le_add hconditionedFloor (le_refl _)
        _ = _ := by ring

/-- **Active immediate-Quit comparison on the tight stratum.**  At a source
row where `who` actually mixes toward Quit, both the conditioned source
value and the rescaled pure-Quit endpoint are anchored at the same singleton
payoff.  Their distance is controlled by the sum of the normalized source
and target opponent clocks.  Unlike the preceding uniform estimate, this
retains the deleted-player factor needed after multiplication by the
rescaled own hazard. -/
theorem abs_quittingStationaryFixedOpponentsQuitValue_rescaledRoot_sub_conditionedValue_le
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (time : ℕ) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (hactive : 0 < (roots time who true).toReal)
    (htight : boundary who = quittingSoloBaseline reward who) :
    |quittingStationaryFixedOpponentsQuitValue reward
          (quittingTailDiffuseRescaledRoot roots time hpositive) who -
        quittingTailConditionedValue roots value boundary time who| ≤
      2 * M *
        (quittingRootOpponentAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hpositive) who +
          quittingTailConditionedOpponentWeight roots time who) := by
  let solo := reward (quittingSingletonTerminal who) who
  have htarget :=
    abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
      (reward := reward)
      (quittingTailDiffuseRescaledRoot roots time hpositive) who hM hreward
  have hpin : boundary who = solo := by
    simpa [solo, quittingSoloBaseline, quittingSoloReward,
      quittingSingletonTerminal] using htight
  have hsource :=
    abs_quittingTailConditionedValue_sub_singleton_le
      roots value boundary hpolicy hnash hreward time who hpositive hactive hpin
  have hsource' :
      |quittingTailConditionedValue roots value boundary time who - solo| ≤
        2 * M * quittingTailConditionedOpponentWeight roots time who := by
    calc
      |quittingTailConditionedValue roots value boundary time who - solo| ≤
          (2 * M * quittingRootOpponentAbsorptionMass (roots time) who) /
            quittingTailEventualAbsorption roots time := by
        simpa only [solo] using hsource
      _ = 2 * M * quittingTailConditionedOpponentWeight roots time who := by
        unfold quittingTailConditionedOpponentWeight
        ring
  calc
    |quittingStationaryFixedOpponentsQuitValue reward
          (quittingTailDiffuseRescaledRoot roots time hpositive) who -
        quittingTailConditionedValue roots value boundary time who| ≤
      |quittingStationaryFixedOpponentsQuitValue reward
          (quittingTailDiffuseRescaledRoot roots time hpositive) who - solo| +
        |quittingTailConditionedValue roots value boundary time who - solo| := by
      simpa only [abs_sub_comm solo
        (quittingTailConditionedValue roots value boundary time who)] using
        abs_sub_le
          (quittingStationaryFixedOpponentsQuitValue reward
            (quittingTailDiffuseRescaledRoot roots time hpositive) who)
          solo
          (quittingTailConditionedValue roots value boundary time who)
    _ ≤ 2 * M *
        quittingRootOpponentAbsorptionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive) who +
        2 * M * quittingTailConditionedOpponentWeight roots time who :=
      add_le_add htarget hsource'
    _ = _ := by ring

/-- In the late diffuse range, the active immediate-Quit discrepancy is at
most six reward bounds times the target deleted absorption.  Thus multiplying
this discrepancy by the rescaled own hazard produces exactly the
`alpha * opponentAbsorption` scale required by a refusal-error telescope. -/
theorem abs_rescaledQuitValue_sub_conditionedValue_le_six_mul_opponent
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (time : ℕ) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (hactive : 0 < (roots time who true).toReal)
    (htight : boundary who = quittingSoloBaseline reward who)
    (hsmall : Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1) :
    |quittingStationaryFixedOpponentsQuitValue reward
          (quittingTailDiffuseRescaledRoot roots time hpositive) who -
        quittingTailConditionedValue roots value boundary time who| ≤
      6 * M * quittingRootOpponentAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) who := by
  have hlocal :=
    abs_quittingStationaryFixedOpponentsQuitValue_rescaledRoot_sub_conditionedValue_le
      roots value boundary hpolicy hnash time who hM hreward hpositive
        hactive htight
  have hclock :=
    half_conditionedOpponentWeight_le_rescaledRoot_opponentAbsorption
      roots time who hpositive hsmall
  have hcoefficient : 0 ≤ 2 * M := mul_nonneg (by norm_num) hM
  calc
    |_ - _| ≤ 2 * M *
        (quittingRootOpponentAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hpositive) who +
          quittingTailConditionedOpponentWeight roots time who) := hlocal
    _ ≤ 2 * M *
        (quittingRootOpponentAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hpositive) who +
          2 * quittingRootOpponentAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hpositive) who) := by
      apply mul_le_mul_of_nonneg_left _ hcoefficient
      linarith
    _ = 6 * M * quittingRootOpponentAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) who := by ring

end GameTheory
