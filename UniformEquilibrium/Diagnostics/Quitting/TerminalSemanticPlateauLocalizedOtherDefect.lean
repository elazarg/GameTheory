/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMarkedTailLocalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNashDefectMobiusDeviation
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding

/-!
# Legal consumption of a localized other-player defect

The minimum-fiber branch of marked-tail localization leaves positive local
Nash defect on players other than the marked reset player.  This module turns
that local charge into an ordinary unilateral behavioral deviation on the
same profile and the same live row.

At a reached row, replace one player's marginal by its better pure endpoint
and then resume the original live-path marginals.  The global payoff gain is
exactly

`live mass * coordinate Nash defect`.

Thus the localized defect is not merely an incidence label: it is a legal
deviation.  The exact identity below is the game-facing interface needed to
bound that gain by the initial best-response debt of the same profile.  The
remaining finite step is to thin the marked minimum-fiber rows to one fixed
other player and one fixed best-action orientation, while retaining the
fixed collision coalition's action marginal.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The better pure endpoint -/

/-- Deterministic choice of a better pure endpoint.  Ties are resolved in
favor of Continue. -/
def quittingRootBestEndpointAction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) : Bool :=
  if quittingRootQuitPayoff reward tail root who ≤
      quittingRootContinuePayoff reward tail root who then false else true

/-- Playing the selected pure endpoint gains exactly the coordinate Nash
defect over the prescribed root mixture. -/
theorem quittingRootSuccessorPayoff_bestEndpoint_sub_eq_coordinateNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward tail
          (Function.update root who
            (PMF.pure (quittingRootBestEndpointAction reward tail root who))) who -
        quittingRootSuccessorPayoff reward tail root who =
      quittingRootCoordinateNashDefect reward tail root who := by
  unfold quittingRootBestEndpointAction quittingRootCoordinateNashDefect
  split_ifs with hle
  · rw [max_eq_right hle]
    rfl
  · rw [max_eq_left (le_of_not_ge hle)]
    rfl

/-- Positive defect forces positive probability on the action opposite the
selected best endpoint.  The local charge therefore records a genuine
played-action mistake. -/
theorem quittingRoot_oppositeBestEndpointProbability_pos_of_defect_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hdefect : 0 < quittingRootCoordinateNashDefect reward tail root who) :
    0 < (root who (!(quittingRootBestEndpointAction reward tail root who))).toReal := by
  let quitValue := quittingRootQuitPayoff reward tail root who
  let continueValue := quittingRootContinuePayoff reward tail root who
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix
    reward tail root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  unfold quittingRootBestEndpointAction
  split_ifs with hle
  · simp only [Bool.not_false]
    have hquitNonneg : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
    have hcontinueNonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
    unfold quittingRootCoordinateNashDefect at hdefect
    rw [max_eq_right hle, hmix] at hdefect
    change quitValue ≤ continueValue at hle
    change 0 < continueValue -
      ((root who true).toReal * quitValue +
        (root who false).toReal * continueValue) at hdefect
    by_contra hnot
    have hquitZero : (root who true).toReal = 0 :=
      le_antisymm (le_of_not_gt hnot) hquitNonneg
    have hcontinueOne : (root who false).toReal = 1 := by linarith
    rw [hquitZero, hcontinueOne] at hdefect
    norm_num at hdefect
  · simp only [Bool.not_true]
    have hquitNonneg : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
    have hcontinueNonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
    have hcontinueLe : continueValue ≤ quitValue := le_of_not_ge hle
    unfold quittingRootCoordinateNashDefect at hdefect
    rw [max_eq_left hcontinueLe, hmix] at hdefect
    change 0 < quitValue -
      ((root who true).toReal * quitValue +
        (root who false).toReal * continueValue) at hdefect
    by_contra hnot
    have hcontinueZero : (root who false).toReal = 0 :=
      le_antisymm (le_of_not_gt hnot) hcontinueNonneg
    have hquitOne : (root who true).toReal = 1 := by linarith
    rw [hcontinueZero, hquitOne] at hdefect
    norm_num at hdefect

/-! ## A one-live-row behavioral deviation -/

/-- Follow the profile's own live marginals, replace one reached row by a
pure action, and resume the same live marginals afterwards. -/
def quittingStagePureEndpointBehaviorDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    (quittingGame reward).BehaviorStrategy who :=
  fun time _history =>
    quittingStageDeviationHazard
      (quittingProfileLiveRoot reward profile) who stage (PMF.pure action)
      (fun offset =>
        quittingProfileLiveRoot reward profile (stage + 1 + offset) who) time

omit [DecidableEq ι] in
@[simp] theorem quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingBehaviorLiveHazard reward
        (quittingStagePureEndpointBehaviorDeviation
          reward profile who stage action) =
      quittingStageDeviationHazard
        (quittingProfileLiveRoot reward profile) who stage (PMF.pure action)
        (fun offset =>
          quittingProfileLiveRoot reward profile (stage + 1 + offset) who) := by
  rfl

omit [DecidableEq ι] in
/-- The live probability of an arbitrary profile is the joint survival of
the root word read on its canonical live histories. -/
theorem quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∀ stage,
      quittingLiveMass reward profile stage =
        quittingJointSurvivalWeight
          (quittingProfileLiveRoot reward profile) 0 stage := by
  classical
  intro stage
  induction stage with
  | zero => simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  | succ stage ih =>
      rw [quittingLiveMass_succ, quittingJointSurvivalWeight_succ, ih]
      congr 1
      rw [quittingJointContinueMass_eq_product,
        quittingStationaryContinueMass_eq_prod_continueProbability]
      apply Finset.prod_congr rfl
      intro player _
      unfold quittingProfileLiveRoot
      rw [Nat.zero_add]
      rfl

omit [DecidableEq ι] in
/-- The literal payoff of the shifted profile is the root-word terminal value
from the corresponding global live date. -/
theorem quittingTerminalPayoff_allContinueSpine_eq_rootSequenceTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) :
    quittingTerminalPayoff reward
        (quittingAllContinueProfileSpine reward profile stage) who =
      quittingRootSequenceTerminalValue reward
        (quittingProfileLiveRoot reward profile) who stage := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  let roots := quittingProfileLiveRoot reward profile
  have hshift : quittingProfileLiveRoot reward
      (quittingAllContinueProfileSpine reward profile stage) =
        fun offset => roots (stage + offset) := by
    funext offset player
    unfold quittingProfileLiveRoot roots
    exact quittingAllContinueProfileSpine_apply_liveHist
      reward profile stage player offset
  rw [hshift]
  exact (quittingRootSequenceTerminalValue_eq_shift
    reward roots who stage).symm

/-- **Exact reached-row gain.**  Replacing one reached marginal by a pure
action and resuming the same live word changes the global terminal payoff by
the row's live mass times the corresponding conditional successor gain. -/
theorem quittingTerminalPayoff_stagePureEndpointDeviation_sub_eq_liveMass_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    quittingTerminalPayoff reward
          (Function.update profile who
            (quittingStagePureEndpointBehaviorDeviation
              reward profile who stage action)) who -
        quittingTerminalPayoff reward profile who =
      quittingLiveMass reward profile stage *
        (quittingRootSuccessorPayoff reward tail.1
              (Function.update root who (PMF.pure action)) who -
          quittingRootSuccessorPayoff reward tail.1 root who) := by
  dsimp only
  let roots := quittingProfileLiveRoot reward profile
  let hazard := quittingStageDeviationHazard roots who stage (PMF.pure action)
    (fun offset => roots (stage + 1 + offset) who)
  let deviated := quittingRootSequenceUpdate roots who hazard
  have hdeviation : quittingTerminalPayoff reward
        (Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)) who =
      quittingRootSequenceTerminalValue reward deviated who 0 := by
    rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue]
    simp only [quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation]
    rfl
  have hprofile : quittingTerminalPayoff reward profile who =
      quittingRootSequenceTerminalValue reward roots who 0 :=
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot reward profile who
  have hagree : ∀ time, time < stage → deviated time = roots time := by
    intro time htime
    exact quittingRootSequenceUpdate_stageDeviationHazard_of_lt
      roots who (PMF.pure action)
        (fun offset => roots (stage + 1 + offset) who) htime
  have hscaling := quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul
    reward deviated roots who stage hagree
  have hdeviatedStage : quittingRootSequenceTerminalValue reward deviated who stage =
      quittingRootSuccessorPayoff reward
        (fun _ => quittingRootSequenceTerminalValue reward roots who (stage + 1))
        (Function.update (roots stage) who (PMF.pure action)) who := by
    have htailValue : quittingRootSequenceTerminalValue reward deviated who (stage + 1) =
        quittingRootSequenceTerminalValue reward roots who (stage + 1) := by
      rw [quittingRootSequenceTerminalValue_eq_shift reward deviated who (stage + 1)]
      change quittingRootSequenceTerminalValue reward
        (fun offset => deviated (stage + 1 + offset)) who 0 = _
      rw [show (fun offset => deviated (stage + 1 + offset)) =
          fun offset => roots (stage + 1 + offset) by
        funext offset
        unfold deviated hazard
        rw [quittingRootSequenceUpdate, quittingStageDeviationHazard_add]
        exact Function.update_eq_self who (roots (stage + 1 + offset))]
      exact (quittingRootSequenceTerminalValue_eq_shift
        reward roots who (stage + 1)).symm
    rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff
      reward deviated who stage, htailValue]
    unfold deviated hazard
    rw [quittingRootSequenceUpdate_stageDeviationHazard_self]
  have hrootStage : quittingRootSequenceTerminalValue reward roots who stage =
      quittingRootSuccessorPayoff reward
        (fun _ => quittingRootSequenceTerminalValue reward roots who (stage + 1))
        (roots stage) who :=
    quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff reward roots who stage
  rw [hdeviatedStage, hrootStage] at hscaling
  rw [hdeviation, hprofile]
  have htail : (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))).1 who =
      quittingRootSequenceTerminalValue reward roots who (stage + 1) :=
    quittingTerminalPayoff_allContinueSpine_eq_rootSequenceTerminalValue
      reward profile who (stage + 1)
  have hpureCongr := quittingRootSuccessorPayoff_congr_apply reward
    (fun _ => quittingRootSequenceTerminalValue reward roots who (stage + 1))
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))).1
    (Function.update (roots stage) who (PMF.pure action)) who htail.symm
  have hrootCongr := quittingRootSuccessorPayoff_congr_apply reward
    (fun _ => quittingRootSequenceTerminalValue reward roots who (stage + 1))
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))).1
    (roots stage) who htail.symm
  rw [← hpureCongr, ← hrootCongr]
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
  exact hscaling

/-- Choosing the better endpoint makes the exact reached-row gain equal live
mass times coordinate defect. -/
theorem quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let action := quittingRootBestEndpointAction reward tail.1 root who
    quittingTerminalPayoff reward
          (Function.update profile who
            (quittingStagePureEndpointBehaviorDeviation
              reward profile who stage action)) who -
        quittingTerminalPayoff reward profile who =
      quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward tail.1 root who := by
  dsimp only
  rw [quittingTerminalPayoff_stagePureEndpointDeviation_sub_eq_liveMass_mul,
    quittingRootSuccessorPayoff_bestEndpoint_sub_eq_coordinateNashDefect]

end GameTheory
