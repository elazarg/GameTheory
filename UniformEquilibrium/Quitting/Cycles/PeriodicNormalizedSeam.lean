/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.CertifiedBoundaryReinsertion
import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity
import UniformEquilibrium.Quitting.Cycles.PeriodicWindowEvaluation
import UniformEquilibrium.Quitting.Terminal.TargetTail.DiagonalTargetTailSemantics

/-!
# Normalized seam of a periodically repeated quitting window

Closing a finite Nash--Bellman window by periodic repetition changes two
different boundary maps.  The prescribed profile payoff sees the terminal
boundary with full joint survival, while a deviator who refuses throughout
the window sees it with opponent-only survival.  This module identifies the
resulting exploitability exactly.

For a window with joint survival `C`, opponent survival `rho`, initial
annotation `w`, terminal annotation `z`, and drift `Delta = w - z`, the two
branches of the literal behavioral periodic evaluator differ from the honest
periodic payoff by

* `-C / (1-C) * Delta` minus the finite-stop slack; and
* `(rho-C) / ((1-rho)(1-C)) * Delta` minus the refusal slack divided by
  `1-rho`.

Thus ordinary endpoint recurrence is not an attachment theorem.  What must
vanish is endpoint displacement normalized by the relevant survival gaps.
The result is about the actual periodically repeated root sequence and its
complete behavioral deviation envelope; it introduces no proxy deviation
semantics.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Finite refusal and exact periodic restart -/

/-- Following sure Continue through a finite prefix is the finite
terminal-hazard recursion for the `Never` hazard. -/
theorem quittingFiniteTerminalHazardValue_never_eq_continueToBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (terminalValue : ℝ) :
    ∀ start fuel,
      quittingFiniteTerminalHazardValue reward roots who
          (quittingPureTimeHazard none) terminalValue start fuel =
        quittingFiniteContinueToBoundaryValue reward roots who terminalValue
          start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [quittingFiniteTerminalHazardValue,
        quittingFiniteContinueToBoundaryValue, ih (start + 1)]
      simp only [quittingPureTimeHazard_none, PMF.pure_apply,
        if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
        if_true, ENNReal.toReal_one, zero_mul, one_mul, zero_add]

/-- The Continue-through-boundary branch is one of the alternatives in the
finite all-behavior Bellman envelope. -/
theorem quittingFiniteContinueToBoundaryValue_le_bestResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (terminalValue : ℝ) :
    ∀ start fuel,
      quittingFiniteContinueToBoundaryValue reward roots who terminalValue
          start fuel ≤
        quittingFiniteTerminalBestResponseValue reward roots who terminalValue
          start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => exact le_rfl
  | succ fuel ih =>
      rw [quittingFiniteContinueToBoundaryValue,
        quittingFiniteTerminalBestResponseValue]
      have hmass : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      have hscaled := mul_le_mul_of_nonneg_left (ih (start + 1)) hmass
      calc
        quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingFiniteContinueToBoundaryValue reward roots who
                  terminalValue (start + 1) fuel ≤
            quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingFiniteTerminalBestResponseValue reward roots who
                  terminalValue (start + 1) fuel := by
          exact add_le_add_right hscaled _
        _ ≤ max (quittingFixedOpponentsQuitValue reward roots who start)
            (quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingFiniteTerminalBestResponseValue reward roots who
                  terminalValue (start + 1) fuel) := le_max_right _ _

/-- A finite Bellman envelope with a displayed terminal boundary returns the
displayed initial cap when that cap solves the pure-action Bellman recursion
at every prefix date. -/
theorem quittingFiniteTerminalBestResponseValue_eq_prescribed_of_isLiveBellmanCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hcap : IsQuittingLiveBellmanCap reward roots who prescribed) :
    ∀ start fuel,
      quittingFiniteTerminalBestResponseValue reward roots who
          (prescribed (start + fuel)) start fuel = prescribed start := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp
  | succ fuel ih =>
      rw [show start + (fuel + 1) = start + 1 + fuel by omega,
        quittingFiniteTerminalBestResponseValue, ih (start + 1)]
      exact (hcap start).symm

/-- Literal periodic refusal is a fixed point of the finite
Continue-through-boundary map of one period. -/
theorem quittingPeriodicWindowRefusalValue_eq_continueToBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ)
    (hperiodic : ∀ time, roots (time + period) = roots time) :
    quittingPeriodicWindowRefusalValue reward roots who =
      quittingFiniteContinueToBoundaryValue reward roots who
        (quittingPeriodicWindowRefusalValue reward roots who) 0 period := by
  have hfinite := quittingRootSequenceHazardTerminalValue_phaseSwitch_eq_finite
    reward roots roots period who (quittingPureTimeHazard none)
  rw [quittingPhaseSwitchRoots_self_of_periodic roots period hperiodic] at hfinite
  have hshift : (fun offset ↦ quittingPureTimeHazard none (period + offset)) =
      quittingPureTimeHazard none := rfl
  rw [hshift,
    quittingFiniteTerminalHazardValue_never_eq_continueToBoundary] at hfinite
  exact hfinite

/-- One-period refusal decomposes into the same finite refusal evaluated at
an arbitrary boundary plus opponent survival times the boundary mismatch. -/
theorem quittingPeriodicWindowRefusalValue_eq_continueToBoundary_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ)
    (hperiodic : ∀ time, roots (time + period) = roots time)
    (boundary : ℝ) :
    quittingPeriodicWindowRefusalValue reward roots who =
      quittingFiniteContinueToBoundaryValue reward roots who boundary 0 period +
        quittingOpponentSurvivalWeight roots who 0 period *
          (quittingPeriodicWindowRefusalValue reward roots who - boundary) := by
  have hfixed := quittingPeriodicWindowRefusalValue_eq_continueToBoundary
    reward roots who period hperiodic
  have hadd := quittingFiniteContinueToBoundaryValue_add
    reward roots who boundary
      (quittingPeriodicWindowRefusalValue reward roots who - boundary) 0 period
  rw [show boundary +
      (quittingPeriodicWindowRefusalValue reward roots who - boundary) =
        quittingPeriodicWindowRefusalValue reward roots who by ring] at hadd
  exact hfixed.trans hadd

/-! ## The two exact normalized branches -/

/-- Slack of the best finite stop phase below the initial annotation. -/
def quittingPeriodicWindowPhaseSlack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ)
    [NeZero period] (initial : ℝ) : ℝ :=
  initial - quittingPeriodicWindowBestPhaseStop reward roots who period

/-- Slack of refusing through the finite window and accepting its displayed
terminal annotation, relative to the initial annotation. -/
def quittingPeriodicWindowRefusalSlack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ)
    (initial terminal : ℝ) : ℝ :=
  initial - quittingFiniteContinueToBoundaryValue reward roots who terminal
    0 period

/-- Exact finite-phase displacement from the honest periodic delivery. -/
theorem quittingPeriodicWindowBestPhaseStop_sub_restartDelivery_eq_normalizedSeam
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (period : ℕ) [NeZero period]
    (hsurvival : quittingJointSurvivalWeight roots 0 period < 1) :
    quittingPeriodicWindowBestPhaseStop reward roots who period -
        quittingWindowRestartDelivery reward roots who 0 period =
      -(quittingJointSurvivalWeight roots 0 period /
          (1 - quittingJointSurvivalWeight roots 0 period)) *
          (prescribed 0 - prescribed period) -
        quittingPeriodicWindowPhaseSlack reward roots who period
          (prescribed 0) := by
  have hseam := quittingWindowRestartDelivery_sub_prescribed
    reward roots who prescribed hprescribed 0 period hsurvival
  simp only [Nat.zero_add] at hseam
  have hne : 1 - quittingJointSurvivalWeight roots 0 period ≠ 0 := by
    linarith
  unfold quittingPeriodicWindowPhaseSlack
  field_simp [hne]
  linarith

/-- Exact refusal displacement from the honest periodic delivery. -/
theorem quittingPeriodicWindowRefusalValue_sub_restartDelivery_eq_normalizedSeam
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (period : ℕ)
    (hperiodic : ∀ time, roots (time + period) = roots time)
    (hjoint : quittingJointSurvivalWeight roots 0 period < 1)
    (hopponent : quittingOpponentSurvivalWeight roots who 0 period < 1) :
    quittingPeriodicWindowRefusalValue reward roots who -
        quittingWindowRestartDelivery reward roots who 0 period =
      ((quittingOpponentSurvivalWeight roots who 0 period -
          quittingJointSurvivalWeight roots 0 period) /
          ((1 - quittingOpponentSurvivalWeight roots who 0 period) *
            (1 - quittingJointSurvivalWeight roots 0 period))) *
          (prescribed 0 - prescribed period) -
        quittingPeriodicWindowRefusalSlack reward roots who period
            (prescribed 0) (prescribed period) /
          (1 - quittingOpponentSurvivalWeight roots who 0 period) := by
  have hseam := quittingWindowRestartDelivery_sub_prescribed
    reward roots who prescribed hprescribed 0 period hjoint
  simp only [Nat.zero_add] at hseam
  have hrefusal := quittingPeriodicWindowRefusalValue_eq_continueToBoundary_add
    reward roots who period hperiodic (prescribed period)
  have hjointNe : 1 - quittingJointSurvivalWeight roots 0 period ≠ 0 := by
    linarith
  have hopponentNe :
      1 - quittingOpponentSurvivalWeight roots who 0 period ≠ 0 := by
    linarith
  unfold quittingPeriodicWindowRefusalSlack
  field_simp [hjointNe, hopponentNe]
  nlinarith

/-! ## Complete periodic exploitability bound -/

/-- The exact two-branch identities give a complete behavioral attachment
bound once the displayed finite-stop and refusal slacks are nonnegative.
Only normalized endpoint drift appears on the right-hand side. -/
theorem quittingPeriodicWindowBestResponseValue_sub_restartDelivery_le_normalizedDrift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (period : ℕ) [NeZero period]
    (hperiodic : ∀ time, roots (time + period) = roots time)
    (hjoint : quittingJointSurvivalWeight roots 0 period < 1)
    (hopponent : quittingOpponentSurvivalWeight roots who 0 period < 1)
    (hphaseSlack : 0 ≤ quittingPeriodicWindowPhaseSlack
      reward roots who period (prescribed 0))
    (hrefusalSlack : 0 ≤ quittingPeriodicWindowRefusalSlack
      reward roots who period (prescribed 0) (prescribed period)) :
    quittingPeriodicWindowBestResponseValue reward roots who period -
        quittingWindowRestartDelivery reward roots who 0 period ≤
      max
        (quittingJointSurvivalWeight roots 0 period *
          max (-(prescribed 0 - prescribed period)) 0 /
            (1 - quittingJointSurvivalWeight roots 0 period))
        ((quittingOpponentSurvivalWeight roots who 0 period -
              quittingJointSurvivalWeight roots 0 period) *
            max (prescribed 0 - prescribed period) 0 /
          ((1 - quittingOpponentSurvivalWeight roots who 0 period) *
            (1 - quittingJointSurvivalWeight roots 0 period))) := by
  let C := quittingJointSurvivalWeight roots 0 period
  let rho := quittingOpponentSurvivalWeight roots who 0 period
  let drift := prescribed 0 - prescribed period
  let phaseSlack := quittingPeriodicWindowPhaseSlack
    reward roots who period (prescribed 0)
  let refusalSlack := quittingPeriodicWindowRefusalSlack
    reward roots who period (prescribed 0) (prescribed period)
  have hC0 : 0 ≤ C := quittingJointSurvivalWeight_nonneg roots 0 period
  have hrho0 : 0 ≤ rho := quittingOpponentSurvivalWeight_nonneg roots who 0 period
  have hCrho : C ≤ rho :=
    quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
      roots who 0 period
  have hCgap : 0 < 1 - C := by dsimp only [C]; linarith
  have hrhoGap : 0 < 1 - rho := by dsimp only [rho]; linarith
  have hphase :=
    quittingPeriodicWindowBestPhaseStop_sub_restartDelivery_eq_normalizedSeam
      reward roots who prescribed hprescribed period hjoint
  have hrefusal :=
    quittingPeriodicWindowRefusalValue_sub_restartDelivery_eq_normalizedSeam
      reward roots who prescribed hprescribed period hperiodic hjoint hopponent
  change max (quittingPeriodicWindowRefusalValue reward roots who)
        (quittingPeriodicWindowBestPhaseStop reward roots who period) -
      quittingWindowRestartDelivery reward roots who 0 period ≤ _
  have hmaxSub :
      max (quittingPeriodicWindowRefusalValue reward roots who)
          (quittingPeriodicWindowBestPhaseStop reward roots who period) -
          quittingWindowRestartDelivery reward roots who 0 period =
        max
          (quittingPeriodicWindowRefusalValue reward roots who -
            quittingWindowRestartDelivery reward roots who 0 period)
          (quittingPeriodicWindowBestPhaseStop reward roots who period -
            quittingWindowRestartDelivery reward roots who 0 period) := by
    rcases le_total
        (quittingPeriodicWindowRefusalValue reward roots who)
        (quittingPeriodicWindowBestPhaseStop reward roots who period) with h | h
    · rw [max_eq_right h, max_eq_right (sub_le_sub_right h _)]
    · rw [max_eq_left h, max_eq_left (sub_le_sub_right h _)]
  rw [hmaxSub]
  apply max_le
  · refine le_max_of_le_right ?_
    rw [hrefusal]
    have hcoeff : 0 ≤ (rho - C) / ((1 - rho) * (1 - C)) :=
      div_nonneg (sub_nonneg.mpr hCrho) (mul_nonneg hrhoGap.le hCgap.le)
    have hdriftLe : drift ≤ max drift 0 := le_max_left _ _
    have hscaled := mul_le_mul_of_nonneg_left hdriftLe hcoeff
    have hslackTerm : 0 ≤ refusalSlack / (1 - rho) :=
      div_nonneg hrefusalSlack hrhoGap.le
    change ((rho - C) / ((1 - rho) * (1 - C))) * drift -
        refusalSlack / (1 - rho) ≤
      (rho - C) * max drift 0 / ((1 - rho) * (1 - C))
    calc
      ((rho - C) / ((1 - rho) * (1 - C))) * drift -
            refusalSlack / (1 - rho) ≤
          ((rho - C) / ((1 - rho) * (1 - C))) * drift :=
        sub_le_self _ hslackTerm
      _ ≤ ((rho - C) / ((1 - rho) * (1 - C))) * max drift 0 := hscaled
      _ = (rho - C) * max drift 0 / ((1 - rho) * (1 - C)) := by ring
  · refine le_max_of_le_left ?_
    rw [hphase]
    have hcoeff : 0 ≤ C / (1 - C) := div_nonneg hC0 hCgap.le
    have hdriftLe : -drift ≤ max (-drift) 0 := le_max_left _ _
    have hscaled := mul_le_mul_of_nonneg_left hdriftLe hcoeff
    have hsubtract :
        -(C / (1 - C)) * drift - phaseSlack ≤
          (C / (1 - C)) * (-drift) := by
      nlinarith [hphaseSlack]
    calc
      -(C / (1 - C)) * drift - phaseSlack ≤
          (C / (1 - C)) * (-drift) := hsubtract
      _ ≤ (C / (1 - C)) * max (-drift) 0 := hscaled
      _ = C * max (-drift) 0 / (1 - C) := by ring

/-- Exact Nash--Bellman windows automatically have nonnegative finite-stop
and refusal slacks, so their periodic closure is controlled solely by the two
normalized endpoint-drift terms. -/
theorem quittingPeriodicWindowBestResponseValue_sub_restartDelivery_le_normalizedDrift_of_exactNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time, IsεQuittingRootNash reward
      (value (time + 1)) 0 (roots time))
    (period : ℕ) [NeZero period]
    (hperiodic : ∀ time, roots (time + period) = roots time)
    (hjoint : quittingJointSurvivalWeight roots 0 period < 1)
    (hopponent : quittingOpponentSurvivalWeight roots who 0 period < 1) :
    quittingPeriodicWindowBestResponseValue reward roots who period -
        quittingWindowRestartDelivery reward roots who 0 period ≤
      max
        (quittingJointSurvivalWeight roots 0 period *
          max (-(value 0 who - value period who)) 0 /
            (1 - quittingJointSurvivalWeight roots 0 period))
        ((quittingOpponentSurvivalWeight roots who 0 period -
              quittingJointSurvivalWeight roots 0 period) *
            max (value 0 who - value period who) 0 /
          ((1 - quittingOpponentSurvivalWeight roots who 0 period) *
            (1 - quittingJointSurvivalWeight roots 0 period))) := by
  let prescribed : ℕ → ℝ := fun time ↦ value time who
  have hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed := by
    intro time
    exact congrFun (hpolicy time) who
  have hphaseSlack : 0 ≤ quittingPeriodicWindowPhaseSlack
      reward roots who period (prescribed 0) := by
    unfold quittingPeriodicWindowPhaseSlack
    exact sub_nonneg.mpr
      (quittingPeriodicWindowBestPhaseStop_le_prescribed
        reward roots who value hpolicy hnash period)
  have hdeviation : ∀ time (deviation : PMF Bool),
      quittingRootExpectedPayoff reward
          (fun _ ↦ prescribed (time + 1))
          (Function.update (roots time) who deviation) who ≤
        quittingRootExpectedPayoff reward
            (fun _ ↦ prescribed (time + 1)) (roots time) who + 0 := by
    intro time deviation
    have hnashAt := hnash time who deviation
    calc
      quittingRootExpectedPayoff reward (fun _ ↦ prescribed (time + 1))
          (Function.update (roots time) who deviation) who =
        quittingRootExpectedPayoff reward (value (time + 1))
          (Function.update (roots time) who deviation) who :=
            quittingRootExpectedPayoff_continuation_congr _ _ _ _ _ rfl
      _ ≤ quittingRootExpectedPayoff reward (value (time + 1))
          (roots time) who + 0 := hnashAt
      _ = quittingRootExpectedPayoff reward (fun _ ↦ prescribed (time + 1))
          (roots time) who + 0 := by
            rw [quittingRootExpectedPayoff_continuation_congr
              reward (value (time + 1)) (fun _ ↦ prescribed (time + 1))
                (roots time) who rfl]
  have hcap : IsQuittingLiveBellmanCap reward roots who prescribed := by
    intro time
    have hresidual := quittingPrescribedOneStepResidual_eq_zero_of_isZeroRootNash
      reward roots who prescribed hprescribed hdeviation time
    unfold quittingPrescribedOneStepResidual at hresidual
    linarith
  have hbest :=
    quittingFiniteTerminalBestResponseValue_eq_prescribed_of_isLiveBellmanCap
      reward roots who prescribed hcap 0 period
  simp only [Nat.zero_add] at hbest
  have hcontinue := quittingFiniteContinueToBoundaryValue_le_bestResponse
    reward roots who (prescribed period) 0 period
  rw [hbest] at hcontinue
  have hrefusalSlack : 0 ≤ quittingPeriodicWindowRefusalSlack
      reward roots who period (prescribed 0) (prescribed period) := by
    exact sub_nonneg.mpr hcontinue
  simpa only [prescribed] using
    quittingPeriodicWindowBestResponseValue_sub_restartDelivery_le_normalizedDrift
      reward roots who prescribed hprescribed period hperiodic hjoint hopponent
        hphaseSlack hrefusalSlack

/-- Actual terminal form of the normalized attachment bound.  Periodicity and
positive absorption identify the restart delivery with the literal terminal
payoff of the repeated root word. -/
theorem quittingPeriodicWindowBestResponseValue_sub_terminalValue_le_normalizedDrift_of_exactNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time, IsεQuittingRootNash reward
      (value (time + 1)) 0 (roots time))
    (period : ℕ) [NeZero period]
    (hperiodic : ∀ time, roots (time + period) = roots time)
    (hjoint : quittingJointSurvivalWeight roots 0 period < 1)
    (hopponent : quittingOpponentSurvivalWeight roots who 0 period < 1) :
    quittingPeriodicWindowBestResponseValue reward roots who period -
        quittingRootSequenceTerminalValue reward roots who 0 ≤
      max
        (quittingJointSurvivalWeight roots 0 period *
          max (-(value 0 who - value period who)) 0 /
            (1 - quittingJointSurvivalWeight roots 0 period))
        ((quittingOpponentSurvivalWeight roots who 0 period -
              quittingJointSurvivalWeight roots 0 period) *
            max (value 0 who - value period who) 0 /
          ((1 - quittingOpponentSurvivalWeight roots who 0 period) *
            (1 - quittingJointSurvivalWeight roots 0 period))) := by
  rw [quittingRootSequenceTerminalValue_eq_windowRestartDelivery_of_periodic
    reward roots who period hperiodic hjoint]
  exact
    quittingPeriodicWindowBestResponseValue_sub_restartDelivery_le_normalizedDrift_of_exactNash
      reward roots who value hpolicy hnash period hperiodic hjoint hopponent

end GameTheory
