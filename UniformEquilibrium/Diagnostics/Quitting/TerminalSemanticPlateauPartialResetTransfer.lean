/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn

/-!
# Fractional reached-row resets and co-realized transfer

A pure reached-row best-endpoint reset consumes the whole local Nash defect,
but can destroy a collision/incidence atom.  This file records the exact
fractional alternative.  At one live row, move a fraction `lambda` of one
player's Boolean marginal toward its better pure endpoint and then resume the
same live word.

The player's payoff gain and best-response-debt reduction are exactly

`lambda * liveMass * localDefect`.

At a minimum-total-debt semantic source, the same amount is transferred in
aggregate to the other coordinates.  At a first-stage row, every terminal-law
coordinate is an affine function of this move.  Hence at least the
`1 - lambda` fraction of every old nonnegative incidence survives.  This is a
co-realized transfer/incidence step for every `0 < lambda < 1`.

The final theorem also isolates the remaining obstruction: these exact facts
give a path of co-realized positive-incidence transfers, but no recurrence of
the semantic state or of the recipient label.  Fractional steps prevent the
one-step loss of incidence; they do not by themselves compile a cycle.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## A fractional Boolean endpoint move -/

/-- Quit probability after moving a fraction `lambda` of `who`'s marginal
toward the displayed pure Boolean endpoint. -/
def quittingPartialEndpointQuitProbability
    (root : ι → PMF Bool) (who : ι) (action : Bool) (lambda : ℝ) : ℝ :=
  (1 - lambda) * (root who true).toReal + lambda * (if action then 1 else 0)

/-- The Boolean marginal implementing a fractional endpoint move. -/
def quittingPartialEndpointMarginal
    (root : ι → PMF Bool) (who : ι) (action : Bool)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) : PMF Bool :=
  quittingHazardCoin
    (quittingPartialEndpointQuitProbability root who action lambda)
    (by
      unfold quittingPartialEndpointQuitProbability
      split_ifs <;> positivity)
    (by
      have hq0 : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
      have hq1 : (root who true).toReal ≤ 1 := by
        rw [← ENNReal.toReal_one,
          ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by simp)]
        exact PMF.coe_le_one _ _
      unfold quittingPartialEndpointQuitProbability
      split_ifs <;> nlinarith)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingPartialEndpointMarginal_true_toReal
    (root : ι → PMF Bool) (who : ι) (action : Bool)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (quittingPartialEndpointMarginal root who action lambda
        hlambda0 hlambda1 true).toReal =
      (1 - lambda) * (root who true).toReal +
        lambda * (PMF.pure action true).toReal := by
  rw [quittingPartialEndpointMarginal,
    quittingHazardCoin_true_toReal]
  unfold quittingPartialEndpointQuitProbability
  cases action <;> simp

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingPartialEndpointMarginal_false_toReal
    (root : ι → PMF Bool) (who : ι) (action : Bool)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (quittingPartialEndpointMarginal root who action lambda
        hlambda0 hlambda1 false).toReal =
      (1 - lambda) * (root who false).toReal +
        lambda * (PMF.pure action false).toReal := by
  rw [quittingPartialEndpointMarginal,
    quittingHazardCoin_false_toReal]
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  unfold quittingPartialEndpointQuitProbability
  cases action <;> simp_all <;> nlinarith

/-- Product root after the fractional endpoint move. -/
def quittingPartialEndpointRoot
    (root : ι → PMF Bool) (who : ι) (action : Bool)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    ι → PMF Bool :=
  Function.update root who
    (quittingPartialEndpointMarginal root who action lambda
      hlambda0 hlambda1)

/-! ## The exact reached-row payoff and debt action -/

/-- Replace one reached marginal by an arbitrary Boolean marginal and resume
the profile's own live marginals afterwards. -/
def quittingStageMarginalBehaviorDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (marginal : PMF Bool) :
    (quittingGame reward).BehaviorStrategy who :=
  fun time _history =>
    quittingStageDeviationHazard
      (quittingProfileLiveRoot reward profile) who stage marginal
      (fun offset =>
        quittingProfileLiveRoot reward profile (stage + 1 + offset) who) time

omit [DecidableEq ι] in
@[simp] theorem quittingBehaviorLiveHazard_stageMarginalBehaviorDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (marginal : PMF Bool) :
    quittingBehaviorLiveHazard reward
        (quittingStageMarginalBehaviorDeviation
          reward profile who stage marginal) =
      quittingStageDeviationHazard
        (quittingProfileLiveRoot reward profile) who stage marginal
        (fun offset =>
          quittingProfileLiveRoot reward profile (stage + 1 + offset) who) := by
  rfl

/-- Exact reached-row payoff action for an arbitrary replacement marginal. -/
theorem quittingTerminalPayoff_stageMarginalDeviation_sub_eq_liveMass_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (marginal : PMF Bool) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    quittingTerminalPayoff reward
          (Function.update profile who
            (quittingStageMarginalBehaviorDeviation
              reward profile who stage marginal)) who -
        quittingTerminalPayoff reward profile who =
      quittingLiveMass reward profile stage *
        (quittingRootSuccessorPayoff reward tail.1
              (Function.update root who marginal) who -
          quittingRootSuccessorPayoff reward tail.1 root who) := by
  dsimp only
  let roots := quittingProfileLiveRoot reward profile
  let hazard := quittingStageDeviationHazard roots who stage marginal
    (fun offset => roots (stage + 1 + offset) who)
  let deviated := quittingRootSequenceUpdate roots who hazard
  have hdeviation : quittingTerminalPayoff reward
        (Function.update profile who
          (quittingStageMarginalBehaviorDeviation
            reward profile who stage marginal)) who =
      quittingRootSequenceTerminalValue reward deviated who 0 := by
    rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue]
    simp only [quittingBehaviorLiveHazard_stageMarginalBehaviorDeviation]
    rfl
  have hprofile : quittingTerminalPayoff reward profile who =
      quittingRootSequenceTerminalValue reward roots who 0 :=
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot reward profile who
  have hagree : ∀ time, time < stage → deviated time = roots time := by
    intro time htime
    exact quittingRootSequenceUpdate_stageDeviationHazard_of_lt
      roots who marginal
        (fun offset => roots (stage + 1 + offset) who) htime
  have hscaling := quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul
    reward deviated roots who stage hagree
  have hdeviatedStage : quittingRootSequenceTerminalValue reward deviated who stage =
      quittingRootSuccessorPayoff reward
        (fun _ => quittingRootSequenceTerminalValue reward roots who (stage + 1))
        (Function.update (roots stage) who marginal) who := by
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
  have hmarginalCongr := quittingRootSuccessorPayoff_congr_apply reward
    (fun _ => quittingRootSequenceTerminalValue reward roots who (stage + 1))
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))).1
    (Function.update (roots stage) who marginal) who htail.symm
  have hrootCongr := quittingRootSuccessorPayoff_congr_apply reward
    (fun _ => quittingRootSequenceTerminalValue reward roots who (stage + 1))
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))).1
    (roots stage) who htail.symm
  rw [← hmarginalCongr, ← hrootCongr]
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
  exact hscaling

/-- Root payoff is affine along a fractional move of one marginal. -/
theorem quittingRootSuccessorPayoff_partialEndpointRoot_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (action : Bool)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingRootSuccessorPayoff reward tail
          (quittingPartialEndpointRoot root who action lambda
            hlambda0 hlambda1) who -
        quittingRootSuccessorPayoff reward tail root who =
      lambda *
        (quittingRootSuccessorPayoff reward tail
              (Function.update root who (PMF.pure action)) who -
          quittingRootSuccessorPayoff reward tail root who) := by
  unfold quittingPartialEndpointRoot quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_update_eq_endpointMix,
    quittingRootExpectedPayoff_update_eq_endpointMix]
  have hrootMix := quittingRootSuccessorPayoff_eq_endpointMix
    reward tail root who
  change _ - quittingRootSuccessorPayoff reward tail root who =
    lambda * (_ - quittingRootSuccessorPayoff reward tail root who)
  rw [hrootMix]
  simp only [quittingPartialEndpointMarginal_true_toReal,
    quittingPartialEndpointMarginal_false_toReal]
  ring

/-- Fractionally moving toward the selected better endpoint consumes exactly
the same fraction of the coordinate Nash defect at that root. -/
theorem quittingRootSuccessorPayoff_partialBestEndpoint_sub_eq_mul_defect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    let action := quittingRootBestEndpointAction reward tail root who
    quittingRootSuccessorPayoff reward tail
          (quittingPartialEndpointRoot root who action lambda
            hlambda0 hlambda1) who -
        quittingRootSuccessorPayoff reward tail root who =
      lambda * quittingRootCoordinateNashDefect reward tail root who := by
  dsimp only
  rw [quittingRootSuccessorPayoff_partialEndpointRoot_sub_eq,
    quittingRootSuccessorPayoff_bestEndpoint_sub_eq_coordinateNashDefect]

/-- The behavioral strategy implementing a fractional move toward the better
endpoint at one reached live row. -/
def quittingStagePartialBestEndpointBehaviorDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (quittingGame reward).BehaviorStrategy who :=
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  let action := quittingRootBestEndpointAction reward tail.1 root who
  quittingStageMarginalBehaviorDeviation reward profile who stage
    (quittingPartialEndpointMarginal root who action lambda
      hlambda0 hlambda1)

/-- **Exact fractional reached-row gain.**  The global payoff gain is the
fractional step size times live mass times the reached row's local defect. -/
theorem quittingTerminalPayoff_stagePartialBestEndpointDeviation_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    quittingTerminalPayoff reward
          (Function.update profile who
            (quittingStagePartialBestEndpointBehaviorDeviation
              reward profile who stage lambda hlambda0 hlambda1)) who -
        quittingTerminalPayoff reward profile who =
      lambda * quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward tail.1 root who := by
  dsimp only [quittingStagePartialBestEndpointBehaviorDeviation]
  rw [quittingTerminalPayoff_stageMarginalDeviation_sub_eq_liveMass_mul,
    show Function.update (quittingProfileLiveRoot reward profile stage) who
        (quittingPartialEndpointMarginal
          (quittingProfileLiveRoot reward profile stage) who
          (quittingRootBestEndpointAction reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (stage + 1))).1
            (quittingProfileLiveRoot reward profile stage) who)
          lambda hlambda0 hlambda1) =
      quittingPartialEndpointRoot
        (quittingProfileLiveRoot reward profile stage) who
        (quittingRootBestEndpointAction reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (stage + 1))).1
          (quittingProfileLiveRoot reward profile stage) who)
        lambda hlambda0 hlambda1 by rfl,
    quittingRootSuccessorPayoff_partialBestEndpoint_sub_eq_mul_defect]
  ring

/-- The all-behavior envelope is unchanged by the fractional reset because
the opponents are literally unchanged. -/
theorem quittingContinuationBestResponseValue_stagePartialBestEndpoint_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingContinuationBestResponseValue reward
        (Function.update profile who
          (quittingStagePartialBestEndpointBehaviorDeviation
            reward profile who stage lambda hlambda0 hlambda1)) who =
      quittingContinuationBestResponseValue reward profile who := by
  exact quittingContinuationBestResponseValue_update_self
    reward profile who _

/-- **Exact fractional debt action.**  A fractional reached-row reset lowers
the resetting player's literal best-response debt by exactly its payoff
gain. -/
theorem quittingTerminalSemanticDebt_stagePartialBestEndpoint_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile who
            (quittingStagePartialBestEndpointBehaviorDeviation
              reward profile who stage lambda hlambda0 hlambda1))) who =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who -
        lambda * quittingLiveMass reward profile stage *
          quittingRootCoordinateNashDefect reward tail.1 root who := by
  dsimp only [quittingTerminalSemanticDebt, quittingTerminalSemanticPair]
  rw [quittingContinuationBestResponseValue_stagePartialBestEndpoint_eq]
  have hgain := quittingTerminalPayoff_stagePartialBestEndpointDeviation_sub_eq
    reward profile who stage lambda hlambda0 hlambda1
  dsimp only [quittingTerminalSemanticPair] at hgain ⊢
  rw [show quittingTerminalPayoff reward
        (Function.update profile who
          (quittingStagePartialBestEndpointBehaviorDeviation
            reward profile who stage lambda hlambda0 hlambda1)) who =
      quittingTerminalPayoff reward profile who +
        lambda * quittingLiveMass reward profile stage *
          quittingRootCoordinateNashDefect reward
            (fun player => quittingTerminalPayoff reward
              (quittingAllContinueProfileSpine reward profile (stage + 1)) player)
            (quittingProfileLiveRoot reward profile stage) who by linarith]
  ring

/-! ## Exact retention of terminal-law incidence -/

/-- Coalition mass is affine when one coordinate is moved affinely.  No
membership assumption on the displayed coalition is needed. -/
theorem quittingCoalitionMass_update_affine
    (x : ι → ℝ) (who : ι) (oldEndpoint newEndpoint lambda : ℝ)
    (hnew : newEndpoint =
      (1 - lambda) * x who + lambda * oldEndpoint)
    (coalition : Finset ι) :
    coalitionMass (Function.update x who newEndpoint) coalition =
      (1 - lambda) * coalitionMass x coalition +
        lambda *
          coalitionMass (Function.update x who oldEndpoint) coalition := by
  classical
  by_cases hwho : who ∈ coalition
  · have hnotComplement : who ∉ coalitionᶜ := by
      simp [hwho]
    have hformula : ∀ endpoint : ℝ,
        coalitionMass (Function.update x who endpoint) coalition =
          (endpoint * ∏ player ∈ coalition \ {who}, x player) *
            ∏ player ∈ coalitionᶜ, (1 - x player) := by
      intro endpoint
      unfold coalitionMass
      rw [Finset.prod_update_of_mem hwho]
      congr 1
      apply Finset.prod_congr rfl
      intro player hplayer
      rw [Function.update_of_ne]
      intro hplayerWho
      subst player
      exact hnotComplement hplayer
    rw [hformula newEndpoint, hformula oldEndpoint,
      show coalitionMass x coalition =
          ((x who * ∏ player ∈ coalition \ {who}, x player) *
            ∏ player ∈ coalitionᶜ, (1 - x player)) by
        simpa using hformula (x who)]
    rw [hnew]
    ring
  · have hcomplement : who ∈ coalitionᶜ := by
      simp [hwho]
    have hformula : ∀ endpoint : ℝ,
        coalitionMass (Function.update x who endpoint) coalition =
          (∏ player ∈ coalition, x player) *
            ((1 - endpoint) *
              ∏ player ∈ coalitionᶜ \ {who}, (1 - x player)) := by
      intro endpoint
      unfold coalitionMass
      have hfirst :
          (∏ player ∈ coalition,
              Function.update x who endpoint player) =
            ∏ player ∈ coalition, x player :=
        Finset.prod_update_of_notMem hwho x endpoint
      rw [hfirst]
      have hupdate :
          (fun player => 1 - Function.update x who endpoint player) =
            Function.update (fun player => 1 - x player) who
              (1 - endpoint) := by
        funext player
        by_cases hplayer : player = who <;> simp [hplayer]
      rw [hupdate, Finset.prod_update_of_mem hcomplement]
    rw [hformula newEndpoint, hformula oldEndpoint,
      show coalitionMass x coalition =
          ((∏ player ∈ coalition, x player) *
            ((1 - x who) *
              ∏ player ∈ coalitionᶜ \ {who}, (1 - x player))) by
        simpa using hformula (x who)]
    rw [hnew]
    ring

/-- Every exact root coalition is affine along a fractional endpoint move. -/
theorem quittingRootCoalitionMass_partialEndpointRoot
    (root : ι → PMF Bool) (who : ι) (action : Bool)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (coalition : Finset ι) :
    quittingRootCoalitionMass
        (quittingPartialEndpointRoot root who action lambda
          hlambda0 hlambda1) coalition =
      (1 - lambda) * quittingRootCoalitionMass root coalition +
        lambda * quittingRootCoalitionMass
          (Function.update root who (PMF.pure action)) coalition := by
  let rates := quittingRootQuitRates root
  have hpartialRates : quittingRootQuitRates
      (quittingPartialEndpointRoot root who action lambda
        hlambda0 hlambda1) =
      Function.update rates who
        ((1 - lambda) * rates who +
          lambda * (PMF.pure action true).toReal) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingRootQuitRates, quittingPartialEndpointRoot, rates]
    · change ((Function.update root who
          (quittingPartialEndpointMarginal root who action lambda
            hlambda0 hlambda1)) player true).toReal =
        Function.update rates who
          ((1 - lambda) * rates who +
            lambda * (PMF.pure action true).toReal) player
      rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
      rfl
  have hpureRates : quittingRootQuitRates
      (Function.update root who (PMF.pure action)) =
      Function.update rates who (PMF.pure action true).toReal := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingRootQuitRates, rates]
    · change ((Function.update root who (PMF.pure action) player true).toReal) =
        Function.update rates who (PMF.pure action true).toReal player
      rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
      rfl
  unfold quittingRootCoalitionMass
  rw [hpartialRates, hpureRates]
  exact quittingCoalitionMass_update_affine rates who
    (PMF.pure action true).toReal
    ((1 - lambda) * rates who +
      lambda * (PMF.pure action true).toReal)
    lambda rfl coalition

/-- **Same-coalition retention.**  Irrespective of whether the interpolated
player leaves or joins the displayed coalition at the endpoint, the partial
root retains at least the `1 - lambda` fraction of its old exact mass. -/
theorem one_sub_mul_quittingRootCoalitionMass_le_partialEndpointRoot
    (root : ι → PMF Bool) (who : ι) (action : Bool)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (coalition : Finset ι) :
    (1 - lambda) * quittingRootCoalitionMass root coalition ≤
      quittingRootCoalitionMass
        (quittingPartialEndpointRoot root who action lambda
          hlambda0 hlambda1) coalition := by
  rw [quittingRootCoalitionMass_partialEndpointRoot]
  exact le_add_of_nonneg_right <| mul_nonneg hlambda0
    (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
      (Function.update root who (PMF.pure action)) coalition)

/-- Empty-coalition root mass is the all-Continue probability. -/
theorem quittingRootCoalitionMass_empty_eq_stationaryContinueMass
    (root : ι → PMF Bool) :
    quittingRootCoalitionMass root ∅ =
      quittingStationaryContinueMass root := by
  rw [quittingRootCoalitionMass, coalitionMass_empty,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  unfold continueMass quittingRootQuitRates
  apply Finset.prod_congr rfl
  intro player _
  have hsum := quittingRoot_continueProbability_add_quitProbability root player
  linarith

/-- Root all-Continue mass is affine along a fractional endpoint move. -/
theorem quittingStationaryContinueMass_partialEndpointRoot
    (root : ι → PMF Bool) (who : ι) (action : Bool)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingStationaryContinueMass
        (quittingPartialEndpointRoot root who action lambda
          hlambda0 hlambda1) =
      (1 - lambda) * quittingStationaryContinueMass root +
        lambda * quittingStationaryContinueMass
          (Function.update root who (PMF.pure action)) := by
  rw [← quittingRootCoalitionMass_empty_eq_stationaryContinueMass,
    ← quittingRootCoalitionMass_empty_eq_stationaryContinueMass,
    ← quittingRootCoalitionMass_empty_eq_stationaryContinueMass]
  exact quittingRootCoalitionMass_partialEndpointRoot
    root who action lambda hlambda0 hlambda1 ∅

/-- First-row displayed opponent incidence is affine along the partial move. -/
theorem quittingRootOpponentIncidenceMass_partialEndpointRoot
    (marked other : ι) (root : ι → PMF Bool) (who : ι) (action : Bool)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingRootOpponentIncidenceMass marked other
        (quittingPartialEndpointRoot root who action lambda
          hlambda0 hlambda1) =
      (1 - lambda) * quittingRootOpponentIncidenceMass marked other root +
        lambda * quittingRootOpponentIncidenceMass marked other
          (Function.update root who (PMF.pure action)) := by
  unfold quittingRootOpponentIncidenceMass
  simp_rw [quittingRootCoalitionMass_partialEndpointRoot]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- The complete displayed incidence after prefixing a fixed continuation law
is affine along the partial move. -/
theorem quittingTerminalOpponentIncidenceMass_partialLawPrefix
    (marked other : ι) (root : ι → PMF Bool) (who : ι) (action : Bool)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (mass : QuittingTerminalOutcome ι → ℝ) :
    quittingTerminalOpponentIncidenceMass marked other
        (quittingTerminalOutcomeLawPrefix
          (quittingPartialEndpointRoot root who action lambda
            hlambda0 hlambda1) mass) =
      (1 - lambda) *
          quittingTerminalOpponentIncidenceMass marked other
            (quittingTerminalOutcomeLawPrefix root mass) +
        lambda *
          quittingTerminalOpponentIncidenceMass marked other
            (quittingTerminalOutcomeLawPrefix
              (Function.update root who (PMF.pure action)) mass) := by
  rw [quittingTerminalOpponentIncidenceMass_lawPrefix,
    quittingTerminalOpponentIncidenceMass_lawPrefix,
    quittingTerminalOpponentIncidenceMass_lawPrefix,
    quittingRootOpponentIncidenceMass_partialEndpointRoot,
    quittingStationaryContinueMass_partialEndpointRoot]
  ring

/-- **Co-realized incidence retention.**  If the old continuation incidence
is nonnegative, the partially prefixed law retains at least `1 - lambda` of
the whole old prefixed incidence. -/
theorem one_sub_mul_incidence_le_partialLawPrefix
    (marked other : ι) (root : ι → PMF Bool) (who : ι) (action : Bool)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : 0 ≤ quittingTerminalOpponentIncidenceMass marked other mass) :
    (1 - lambda) *
        quittingTerminalOpponentIncidenceMass marked other
          (quittingTerminalOutcomeLawPrefix root mass) ≤
      quittingTerminalOpponentIncidenceMass marked other
        (quittingTerminalOutcomeLawPrefix
          (quittingPartialEndpointRoot root who action lambda
            hlambda0 hlambda1) mass) := by
  rw [quittingTerminalOpponentIncidenceMass_partialLawPrefix]
  apply le_add_of_nonneg_right
  apply mul_nonneg hlambda0
  rw [quittingTerminalOpponentIncidenceMass_lawPrefix]
  apply add_nonneg
  · exact Finset.sum_nonneg fun terminal _ =>
      MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
        (Function.update root who (PMF.pure action)) terminal.val
  · exact mul_nonneg
      (quittingStationaryContinueMass_nonneg _) hmass

/-! ## Minimum-debt transfer and the co-realized capstone -/

/-- Any exact decrease of one coordinate at a minimum-total-debt source is
transferred in aggregate to the opposite player face. -/
theorem minimumDebt_opponentTransfer_of_coordinateDecrease
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : QuittingTerminalSemanticPair ι) (who : ι) (gain : ℝ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hdecrease : quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - gain) :
    gain ≤ ∑ other ∈ Finset.univ.erase who,
      quittingTerminalSemanticDebtChange source target other := by
  have hsum := Finset.sum_erase_add Finset.univ
    (fun player => quittingTerminalSemanticDebtChange source target player)
    (Finset.mem_univ who)
  have htotal : (∑ player,
      quittingTerminalSemanticDebtChange source target player) =
      quittingTerminalSemanticDebtSum target -
        quittingTerminalSemanticDebtSum source := by
    unfold quittingTerminalSemanticDebtChange
      quittingTerminalSemanticDebtSum
    rw [Finset.sum_sub_distrib]
  have hwho : quittingTerminalSemanticDebtChange source target who = -gain := by
    unfold quittingTerminalSemanticDebtChange
    rw [hdecrease]
    ring
  rw [htotal, hwho] at hsum
  have hmin := hminimum target htarget
  linarith

/-- Near-minimum variant of the opposite-face transfer account. -/
theorem nearMinimumDebt_opponentTransfer_of_coordinateDecrease
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : QuittingTerminalSemanticPair ι) (who : ι)
    (gain epsilon : ℝ)
    (hnear : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate + epsilon)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hdecrease : quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - gain) :
    gain ≤ epsilon + ∑ other ∈ Finset.univ.erase who,
      quittingTerminalSemanticDebtChange source target other := by
  have hsum := Finset.sum_erase_add Finset.univ
    (fun player => quittingTerminalSemanticDebtChange source target player)
    (Finset.mem_univ who)
  have htotal : (∑ player,
      quittingTerminalSemanticDebtChange source target player) =
      quittingTerminalSemanticDebtSum target -
        quittingTerminalSemanticDebtSum source := by
    unfold quittingTerminalSemanticDebtChange
      quittingTerminalSemanticDebtSum
    rw [Finset.sum_sub_distrib]
  have hwho : quittingTerminalSemanticDebtChange source target who = -gain := by
    unfold quittingTerminalSemanticDebtChange
    rw [hdecrease]
    ring
  rw [htotal, hwho] at hsum
  have hnearTarget := hnear target htarget
  linarith

/-- **Exact excess-debt transfer account.**  Relative to a global minimum
reference, an actual source need not itself be minimal.  Its own-coordinate
decrease is bounded by the opposite-face transfer plus precisely the source's
total-debt excess over the minimum.  This is the form directly compatible
with marked-tail localization, which places the continuation tail—not
automatically the currently prefixed source—on the minimum fiber. -/
theorem minimumReference_opponentTransfer_of_coordinateDecrease
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum source target : QuittingTerminalSemanticPair ι)
    (who : ι) (gain : ℝ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hdecrease : quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - gain) :
    gain ≤
      (quittingTerminalSemanticDebtSum source -
        quittingTerminalSemanticDebtSum minimum) +
      ∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target other := by
  have hsum := Finset.sum_erase_add Finset.univ
    (fun player => quittingTerminalSemanticDebtChange source target player)
    (Finset.mem_univ who)
  have htotal : (∑ player,
      quittingTerminalSemanticDebtChange source target player) =
      quittingTerminalSemanticDebtSum target -
        quittingTerminalSemanticDebtSum source := by
    unfold quittingTerminalSemanticDebtChange
      quittingTerminalSemanticDebtSum
    rw [Finset.sum_sub_distrib]
  have hwho : quittingTerminalSemanticDebtChange source target who = -gain := by
    unfold quittingTerminalSemanticDebtChange
    rw [hdecrease]
    ring
  rw [htotal, hwho] at hsum
  have hminTarget := hminimum target htarget
  linarith

/-- A first-stage fractional root move changes only the displayed player's
strategy in the literal spliced profile. -/
theorem quittingRootThenContinuation_partialEndpoint_eq_updateSelf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (action : Bool) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingRootThenContinuationProfile reward
        (quittingPartialEndpointRoot root who action lambda
          hlambda0 hlambda1) continuation =
      Function.update
        (quittingRootThenContinuationProfile reward root continuation) who
        ((quittingRootThenContinuationProfile reward
          (quittingPartialEndpointRoot root who action lambda
            hlambda0 hlambda1) continuation) who) := by
  funext player time history
  by_cases hplayer : player = who
  · subst player
    rw [Function.update_self]
  · rw [Function.update_of_ne hplayer]
    cases time with
    | zero =>
        change quittingPartialEndpointRoot root who action lambda
            hlambda0 hlambda1 player = root player
        simp [quittingPartialEndpointRoot, Function.update_of_ne hplayer]
    | succ time => rfl

/-- Actual terminal-outcome incidence is nonnegative. -/
theorem quittingTerminalOpponentIncidenceMass_outcomeMass_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (marked other : ι) :
    0 ≤ quittingTerminalOpponentIncidenceMass marked other
      (quittingTerminalOutcomeMass reward profile) := by
  unfold quittingTerminalOpponentIncidenceMass
  apply Finset.sum_nonneg
  intro terminal _
  exact quittingAbsorbedMassLimit_nonneg reward profile terminal

/-- **Co-realized near-minimum fractional reset/transfer/incidence capstone.**

At a literal first-stage splice that is separately known to be within
`epsilon` of the global minimum, move a strict fraction toward the reached
root's better endpoint.  The target is an actual profile.  Its own debt drops
by exactly `lambda * localDefect`; all but the explicit `epsilon` loss is
transferred to the other player coordinates; and every displayed positive
opponent incidence remains positive, with lower factor `1 - lambda`.

This is one co-realized semantic/law step.  It deliberately makes no claim
that marked-tail localization already makes the prefixed source near-minimal,
or that iterating such steps returns to a prior state or player label.  In the
absence of the extra near-minimum premise, use the exact excess account in
`minimumReference_opponentTransfer_of_coordinateDecrease`. -/
theorem partialBestEndpoint_nearMinimumDebt_transfer_with_positiveIncidence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who marked other : ι) (lambda epsilon : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hlambdaStrict : lambda < 1)
    (hnear : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward root continuation)) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon)
    (hincidence : 0 < quittingTerminalOpponentIncidenceMass marked other
      (quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward root continuation))) :
    let tail := quittingTerminalSemanticPair reward continuation
    let action := quittingRootBestEndpointAction reward tail.1 root who
    let sourceProfile :=
      quittingRootThenContinuationProfile reward root continuation
    let targetProfile := quittingRootThenContinuationProfile reward
      (quittingPartialEndpointRoot root who action lambda
        hlambda0 hlambda1) continuation
    let source := quittingTerminalSemanticPair reward sourceProfile
    let target := quittingTerminalSemanticPair reward targetProfile
    let gain := lambda *
      quittingRootCoordinateNashDefect reward tail.1 root who
    target ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebt target who =
        quittingTerminalSemanticDebt source who - gain ∧
      gain ≤ epsilon + ∑ recipient ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target recipient ∧
      (1 - lambda) *
          quittingTerminalOpponentIncidenceMass marked other
            (quittingTerminalOutcomeMass reward sourceProfile) ≤
        quittingTerminalOpponentIncidenceMass marked other
          (quittingTerminalOutcomeMass reward targetProfile) ∧
      0 < quittingTerminalOpponentIncidenceMass marked other
        (quittingTerminalOutcomeMass reward targetProfile) := by
  dsimp only
  let action := quittingRootBestEndpointAction reward
    (quittingTerminalSemanticPair reward continuation).1 root who
  let sourceProfile :=
    quittingRootThenContinuationProfile reward root continuation
  let targetProfile := quittingRootThenContinuationProfile reward
    (quittingPartialEndpointRoot root who action lambda
      hlambda0 hlambda1) continuation
  let source := quittingTerminalSemanticPair reward sourceProfile
  let target := quittingTerminalSemanticPair reward targetProfile
  let gain := lambda * quittingRootCoordinateNashDefect reward
    (quittingTerminalSemanticPair reward continuation).1 root who
  have htargetMem : target ∈ quittingTerminalSemanticCarrier reward := by
    apply subset_closure
    exact ⟨targetProfile, rfl⟩
  have henvelope : quittingContinuationBestResponseValue reward targetProfile who =
      quittingContinuationBestResponseValue reward sourceProfile who := by
    dsimp [targetProfile, sourceProfile]
    rw [quittingRootThenContinuation_partialEndpoint_eq_updateSelf]
    exact quittingContinuationBestResponseValue_update_self _ _ _ _
  have hpayoff : quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward sourceProfile who = gain := by
    rw [quittingTerminalPayoff_rootThenContinuation_eq,
      quittingTerminalPayoff_rootThenContinuation_eq]
    exact quittingRootSuccessorPayoff_partialBestEndpoint_sub_eq_mul_defect
      reward (quittingTerminalSemanticPair reward continuation).1 root who
        lambda hlambda0 hlambda1
  have hdecrease : quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - gain := by
    change quittingContinuationBestResponseValue reward targetProfile who -
        quittingTerminalPayoff reward targetProfile who =
      quittingContinuationBestResponseValue reward sourceProfile who -
        quittingTerminalPayoff reward sourceProfile who - gain
    linarith
  have htransfer : gain ≤ epsilon + ∑ recipient ∈ Finset.univ.erase who,
      quittingTerminalSemanticDebtChange source target recipient :=
    nearMinimumDebt_opponentTransfer_of_coordinateDecrease reward source target
      who gain epsilon hnear htargetMem hdecrease
  have hcontinuationIncidence : 0 ≤
      quittingTerminalOpponentIncidenceMass marked other
        (quittingTerminalOutcomeMass reward continuation) :=
    quittingTerminalOpponentIncidenceMass_outcomeMass_nonneg
      reward continuation marked other
  have hincidenceLower : (1 - lambda) *
      quittingTerminalOpponentIncidenceMass marked other
        (quittingTerminalOutcomeMass reward sourceProfile) ≤
    quittingTerminalOpponentIncidenceMass marked other
      (quittingTerminalOutcomeMass reward targetProfile) := by
    unfold sourceProfile targetProfile
    rw [← quittingTerminalOutcomeLawPrefix_outcomeMass,
      ← quittingTerminalOutcomeLawPrefix_outcomeMass]
    exact one_sub_mul_incidence_le_partialLawPrefix
      marked other root who action lambda hlambda0 hlambda1
      (quittingTerminalOutcomeMass reward continuation)
      hcontinuationIncidence
  have hincidencePositive : 0 <
      quittingTerminalOpponentIncidenceMass marked other
        (quittingTerminalOutcomeMass reward targetProfile) :=
    (mul_pos (sub_pos.mpr hlambdaStrict) hincidence).trans_le hincidenceLower
  exact ⟨htargetMem, hdecrease, htransfer,
    hincidenceLower, hincidencePositive⟩

/-- **Minimum-reference version of the co-realized capstone.**  This is the
honest form when only a separate continuation/minimum point is known: the
unabsorbed loss is exactly the actual prefixed source's total-debt excess over
that minimum. -/
theorem partialBestEndpoint_minimumReference_transfer_with_positiveIncidence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who marked other : ι) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hlambdaStrict : lambda < 1)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hincidence : 0 < quittingTerminalOpponentIncidenceMass marked other
      (quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward root continuation))) :
    let tail := quittingTerminalSemanticPair reward continuation
    let action := quittingRootBestEndpointAction reward tail.1 root who
    let sourceProfile :=
      quittingRootThenContinuationProfile reward root continuation
    let targetProfile := quittingRootThenContinuationProfile reward
      (quittingPartialEndpointRoot root who action lambda
        hlambda0 hlambda1) continuation
    let source := quittingTerminalSemanticPair reward sourceProfile
    let target := quittingTerminalSemanticPair reward targetProfile
    let gain := lambda *
      quittingRootCoordinateNashDefect reward tail.1 root who
    target ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebt target who =
        quittingTerminalSemanticDebt source who - gain ∧
      gain ≤
        (quittingTerminalSemanticDebtSum source -
          quittingTerminalSemanticDebtSum minimum) +
        ∑ recipient ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source target recipient ∧
      (1 - lambda) *
          quittingTerminalOpponentIncidenceMass marked other
            (quittingTerminalOutcomeMass reward sourceProfile) ≤
        quittingTerminalOpponentIncidenceMass marked other
          (quittingTerminalOutcomeMass reward targetProfile) ∧
      0 < quittingTerminalOpponentIncidenceMass marked other
        (quittingTerminalOutcomeMass reward targetProfile) := by
  let source := quittingTerminalSemanticPair reward
    (quittingRootThenContinuationProfile reward root continuation)
  have hnear : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate +
          (quittingTerminalSemanticDebtSum source -
            quittingTerminalSemanticDebtSum minimum) := by
    intro candidate hcandidate
    have hmin := hminimum candidate hcandidate
    linarith
  exact partialBestEndpoint_nearMinimumDebt_transfer_with_positiveIncidence
    reward root continuation who marked other lambda
      (quittingTerminalSemanticDebtSum source -
        quittingTerminalSemanticDebtSum minimum)
      hlambda0 hlambda1 hlambdaStrict hnear hincidence

end GameTheory
