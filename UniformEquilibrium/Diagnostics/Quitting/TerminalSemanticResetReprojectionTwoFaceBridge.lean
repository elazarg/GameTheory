/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionFixedLabel
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPartialResetTransfer

/-!
# A same-profile partial-reset bridge at a concentrated row

A positive other-player defect on a concentrated marked row can be consumed
without changing profiles or laws behind the scenes.  The target is the
literal behavioral profile obtained by moving that player's reached marginal
a strict fraction toward its better Boolean endpoint.  Both semantic/law
points are therefore jointly realized.  The selected debt decrease and the
opposite-coordinate transfer account are exact, while the original marked
stage cylinder retains its `1 - lambda` fraction.

Every strict move stays off the selected player's zero-debt face: the full
one-row gain is at most the player's source debt, so the remaining debt is at
least its `1 - lambda` fraction.  Exact landing forces a unit move whose full
gain exhausts the source debt.  Nor does the move preserve a pre-existing
zero-debt coordinate of another player.  These are the two precise fences on
iterating the bridge as a reset-face path.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- The actual reached root of a stagewise partial best-endpoint deviation is
the corresponding partial endpoint root. -/
theorem quittingProfileLiveRoot_stagePartialBestEndpoint_self
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingProfileLiveRoot reward
        (Function.update profile who
          (quittingStagePartialBestEndpointBehaviorDeviation
            reward profile who stage lambda hlambda0 hlambda1)) stage =
      quittingPartialEndpointRoot
        (quittingProfileLiveRoot reward profile stage) who
        (quittingRootBestEndpointAction reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (stage + 1))).1
          (quittingProfileLiveRoot reward profile stage) who)
        lambda hlambda0 hlambda1 := by
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
  dsimp only [quittingStagePartialBestEndpointBehaviorDeviation]
  rw [quittingBehaviorLiveHazard_stageMarginalBehaviorDeviation,
    quittingRootSequenceUpdate_stageDeviationHazard_self]
  rfl

/-- A stagewise endpoint move does not change the probability of reaching its
own stage. -/
theorem quittingLiveMass_stagePartialBestEndpoint_eq
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingLiveMass reward
        (Function.update profile who
          (quittingStagePartialBestEndpointBehaviorDeviation
            reward profile who stage lambda hlambda0 hlambda1)) stage =
      quittingLiveMass reward profile stage := by
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
  apply quittingJointSurvivalWeight_congr _ _ 0 stage
  intro offset hoffset
  rw [Nat.zero_add, quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
  dsimp only [quittingStagePartialBestEndpointBehaviorDeviation]
  rw [quittingBehaviorLiveHazard_stageMarginalBehaviorDeviation]
  exact quittingRootSequenceUpdate_stageDeviationHazard_of_lt
    (quittingProfileLiveRoot reward profile) who
    (quittingPartialEndpointMarginal
      (quittingProfileLiveRoot reward profile stage) who
      (quittingRootBestEndpointAction reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (stage + 1))).1
        (quittingProfileLiveRoot reward profile stage) who)
      lambda hlambda0 hlambda1)
    (fun later ↦
      quittingProfileLiveRoot reward profile (stage + 1 + later) who)
    hoffset

/-- The original marked cylinder survives a strict fractional endpoint move
at the same actual row. -/
theorem one_sub_mul_stageCoalitionMass_le_stagePartialBestEndpoint
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ)
    (terminal : {S : Finset iota // S.Nonempty})
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (1 - lambda) * quittingStageCoalitionMass reward profile stage terminal ≤
      quittingStageCoalitionMass reward
        (Function.update profile who
          (quittingStagePartialBestEndpointBehaviorDeviation
            reward profile who stage lambda hlambda0 hlambda1))
        stage terminal := by
  let root := quittingProfileLiveRoot reward profile stage
  let action := quittingRootBestEndpointAction reward
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))).1 root who
  have hroot := one_sub_mul_quittingRootCoalitionMass_le_partialEndpointRoot
    root who action lambda hlambda0 hlambda1 terminal.val
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_stagePartialBestEndpoint_eq,
    quittingProfileLiveRoot_stagePartialBestEndpoint_self]
  calc
    (1 - lambda) *
          (quittingLiveMass reward profile stage *
            quittingRootCoalitionMass root terminal.val) =
        quittingLiveMass reward profile stage *
          ((1 - lambda) *
            quittingRootCoalitionMass root terminal.val) := by ring
    _ ≤ quittingLiveMass reward profile stage *
          quittingRootCoalitionMass
            (quittingPartialEndpointRoot root who action lambda
              hlambda0 hlambda1) terminal.val :=
      mul_le_mul_of_nonneg_left hroot
        (quittingLiveMass_nonneg reward profile stage)

/-! ## The semantic-debt face barrier -/

/-- A strict partial move cannot consume a larger fraction of the mover's
global semantic debt than its interpolation weight.  This is the debt-side
counterpart of marked-cylinder retention. -/
theorem one_sub_mul_terminalSemanticDebt_le_stagePartialBestEndpoint
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    (1 - lambda) * quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile who
            (quittingStagePartialBestEndpointBehaviorDeviation
              reward profile who stage lambda hlambda0 hlambda1))) who := by
  let gain := quittingLiveMass reward profile stage *
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))).1
      (quittingProfileLiveRoot reward profile stage) who
  have hgainLe : gain ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who := by
    exact quittingLiveMass_mul_coordinateNashDefect_le_initialDebt
      (reward := reward) profile who stage hM hreward
  have hscaled : lambda * gain ≤ lambda *
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who :=
    mul_le_mul_of_nonneg_left hgainLe hlambda0
  have hdecrease := quittingTerminalSemanticDebt_stagePartialBestEndpoint_eq
    reward profile who stage lambda hlambda0 hlambda1
  dsimp only at hdecrease
  rw [hdecrease]
  dsimp only [gain] at hscaled
  nlinarith

/-- Positive source debt remains positive after every strict fractional
reached-row best-endpoint move. -/
theorem terminalSemanticDebt_stagePartialBestEndpoint_pos
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who) :
    0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile who
          (quittingStagePartialBestEndpointBehaviorDeviation
            reward profile who stage lambda hlambda0 hlambda1.le))) who := by
  have hbarrier :=
    one_sub_mul_terminalSemanticDebt_le_stagePartialBestEndpoint
      (reward := reward) profile who stage lambda hlambda0 hlambda1.le
        hM hreward
  exact (mul_pos (sub_pos.mpr hlambda1) hsource).trans_le hbarrier

/-- **Exact zero-face landing forces the incidence-drop seam.**

If a reached-row partial best-endpoint move starts with positive semantic debt
and lands exactly on the mover's zero-debt face, its weight is `1`; moreover
the full one-row gain exhausts the entire source debt.  Thus no strict
fractional move can realize the tempting two-face landing while retaining a
positive `1 - lambda` share of the marked atom. -/
theorem eq_one_and_fullGain_of_stagePartialBestEndpoint_hits_zeroDebt
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who)
    (htarget : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile who
          (quittingStagePartialBestEndpointBehaviorDeviation
            reward profile who stage lambda hlambda0 hlambda1))) who = 0) :
    lambda = 1 ∧
      quittingLiveMass reward profile stage *
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (stage + 1))).1
            (quittingProfileLiveRoot reward profile stage) who =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who := by
  have hbarrier :=
    one_sub_mul_terminalSemanticDebt_le_stagePartialBestEndpoint
      (reward := reward) profile who stage lambda hlambda0 hlambda1 hM hreward
  rw [htarget] at hbarrier
  have hfactor : 0 ≤ 1 - lambda := sub_nonneg.mpr hlambda1
  have hproduct : (1 - lambda) * quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who = 0 := by
    exact le_antisymm hbarrier (mul_nonneg hfactor hsource.le)
  have hlambda : lambda = 1 := by
    rcases mul_eq_zero.mp hproduct with hzero | hzero
    · linarith
    · exact (hsource.ne' hzero).elim
  refine ⟨hlambda, ?_⟩
  have hdecrease := quittingTerminalSemanticDebt_stagePartialBestEndpoint_eq
    reward profile who stage lambda hlambda0 hlambda1
  dsimp only at hdecrease
  rw [htarget, hlambda] at hdecrease
  norm_num at hdecrease
  linarith

/-- **Same-profile two-face bridge.**  A concentrated marked row whose
non-owner defect sum is positive supplies one actual fractional reset.

The semantic pair and complete terminal law on both sides come from the two
displayed literal profiles.  The selected player's debt decreases by the
legal reached-row gain; the changes on all other debt coordinates satisfy an
exact balance identity and the minimum-reference lower bound; and the same
marked stage cylinder remains positive.  The selected player's target debt
also remains strictly positive.  Thus this state-preserving move cannot itself
produce a second zero-debt face. -/
theorem exists_concentrated_partialReset_sameProfile_twoFaceBridge
    (minimum : QuittingTerminalSemanticPair iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : iota) (stage : ℕ)
    (terminal : {S : Finset iota // S.Nonempty})
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hstage : 0 < quittingStageCoalitionMass reward profile stage terminal)
    (hdefect : 0 < ∑ other ∈ Finset.univ.erase owner,
      quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (stage + 1))).1
        (quittingProfileLiveRoot reward profile stage) other)
    (lambda : ℝ) (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1) :
    ∃ other, other ≠ owner ∧
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))
      let root := quittingProfileLiveRoot reward profile stage
      let action := quittingRootBestEndpointAction reward tail.1 root other
      let targetProfile := Function.update profile other
        (quittingStageMarginalBehaviorDeviation reward profile other stage
          (quittingPartialEndpointMarginal root other action lambda
            hlambda0.le hlambda1.le))
      let source := quittingTerminalSemanticPair reward profile
      let target := quittingTerminalSemanticPair reward targetProfile
      let sourcePoint : QuittingTerminalSemanticLawPoint iota :=
        (source, quittingTerminalOutcomeMass reward profile)
      let targetPoint : QuittingTerminalSemanticLawPoint iota :=
        (target, quittingTerminalOutcomeMass reward targetProfile)
      let gain := lambda * quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward tail.1 root other
      sourcePoint ∈ quittingTerminalSemanticLawCarrier reward ∧
        targetPoint ∈ quittingTerminalSemanticLawCarrier reward ∧
        0 < gain ∧
        quittingTerminalSemanticDebt target other =
          quittingTerminalSemanticDebt source other - gain ∧
        (∑ recipient ∈ Finset.univ.erase other,
            quittingTerminalSemanticDebtChange source target recipient) =
          (quittingTerminalSemanticDebtSum target -
            quittingTerminalSemanticDebtSum source) + gain ∧
        gain ≤
          (quittingTerminalSemanticDebtSum source -
            quittingTerminalSemanticDebtSum minimum) +
          ∑ recipient ∈ Finset.univ.erase other,
            quittingTerminalSemanticDebtChange source target recipient ∧
        (1 - lambda) *
            quittingStageCoalitionMass reward profile stage terminal ≤
          quittingStageCoalitionMass reward targetProfile stage terminal ∧
        0 < quittingStageCoalitionMass reward targetProfile stage terminal ∧
        0 < quittingTerminalSemanticDebt target other ∧
        (quittingTerminalSemanticDebt target other = 0 ↔
          quittingTerminalSemanticDebt source other = gain) := by
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  have hnonneg : ∀ other ∈ Finset.univ.erase owner,
      0 ≤ quittingRootCoordinateNashDefect reward tail.1 root other := by
    intro other _
    exact quittingRootCoordinateNashDefect_nonneg reward _ _ other
  obtain ⟨other, hotherMem, hotherDefect⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonneg).mp hdefect
  have hotherNe : other ≠ owner := (Finset.mem_erase.mp hotherMem).1
  refine ⟨other, hotherNe, ?_⟩
  dsimp only
  let action := quittingRootBestEndpointAction reward tail.1 root other
  let targetProfile := Function.update profile other
    (quittingStageMarginalBehaviorDeviation reward profile other stage
      (quittingPartialEndpointMarginal root other action lambda
        hlambda0.le hlambda1.le))
  let source := quittingTerminalSemanticPair reward profile
  let target := quittingTerminalSemanticPair reward targetProfile
  let gain := lambda * quittingLiveMass reward profile stage *
    quittingRootCoordinateNashDefect reward tail.1 root other
  have hlive : 0 < quittingLiveMass reward profile stage :=
    hstage.trans_le
      (quittingStageCoalitionMass_le_liveMass reward profile stage terminal)
  have hgain : 0 < gain := by
    exact mul_pos (mul_pos hlambda0 hlive) hotherDefect
  have hsourceDebt : 0 < quittingTerminalSemanticDebt source other := by
    have hcollectable := quittingLiveMass_mul_coordinateNashDefect_le_initialDebt
      (reward := reward) profile other stage hM hreward
    exact (mul_pos hlive hotherDefect).trans_le hcollectable
  have hsourcePoint :
      (source, quittingTerminalOutcomeMass reward profile) ∈
        quittingTerminalSemanticLawCarrier reward := by
    exact quittingTerminalSemanticLawPoint_mem_carrier reward profile
  have htargetPoint :
      (target, quittingTerminalOutcomeMass reward targetProfile) ∈
        quittingTerminalSemanticLawCarrier reward := by
    exact quittingTerminalSemanticLawPoint_mem_carrier reward targetProfile
  have hdecrease : quittingTerminalSemanticDebt target other =
      quittingTerminalSemanticDebt source other - gain := by
    exact quittingTerminalSemanticDebt_stagePartialBestEndpoint_eq
      reward profile other stage lambda hlambda0.le hlambda1.le
  have htransferExact :
      (∑ recipient ∈ Finset.univ.erase other,
          quittingTerminalSemanticDebtChange source target recipient) =
        (quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum source) + gain := by
    have hsum := Finset.sum_erase_add Finset.univ
      (fun player ↦ quittingTerminalSemanticDebtChange source target player)
      (Finset.mem_univ other)
    have htotal : (∑ player,
        quittingTerminalSemanticDebtChange source target player) =
        quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum source := by
      unfold quittingTerminalSemanticDebtChange
        quittingTerminalSemanticDebtSum
      rw [Finset.sum_sub_distrib]
    have hother : quittingTerminalSemanticDebtChange source target other =
        -gain := by
      unfold quittingTerminalSemanticDebtChange
      rw [hdecrease]
      ring
    rw [htotal, hother] at hsum
    linarith
  have htargetCarrier : target ∈
      quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward targetProfile
  have htransfer := minimumReference_opponentTransfer_of_coordinateDecrease
    reward minimum source target other gain hminimum htargetCarrier hdecrease
  have hretention :=
    one_sub_mul_stageCoalitionMass_le_stagePartialBestEndpoint
      (reward := reward) profile other stage terminal lambda
        hlambda0.le hlambda1.le
  have htargetStage : 0 <
      quittingStageCoalitionMass reward targetProfile stage terminal := by
    have hpositive : 0 < (1 - lambda) *
        quittingStageCoalitionMass reward profile stage terminal :=
      mul_pos (sub_pos.mpr hlambda1) hstage
    exact hpositive.trans_le hretention
  have htargetDebt : 0 < quittingTerminalSemanticDebt target other := by
    exact terminalSemanticDebt_stagePartialBestEndpoint_pos
      (reward := reward) profile other stage lambda hlambda0.le hlambda1
        hM hreward hsourceDebt
  refine ⟨hsourcePoint, htargetPoint, hgain, hdecrease, htransferExact,
    htransfer, hretention, htargetStage, htargetDebt, ?_⟩
  constructor <;> intro h
  · linarith
  · linarith

end GameTheory
