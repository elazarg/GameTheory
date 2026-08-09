/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Cycles.PeriodicPureTimeBellman

/-!
# Exact finite evaluation of a periodically repeated quitting window

Against periodic opponents, a player's behavioral best response is the
larger of two finite statistics:

* the value of refusing forever (`Never`); and
* the best deterministic stop phase in one pass of the window.

The proof first strips one whole pass from any later deterministic stop.
The stripped value is an affine interpolation between the refusal value and
the corresponding earlier stop, with coefficient equal to deleted-player
survival through the pass.  Induction then folds every calendar stop into
the first pass.  Behavioral pure-time extremality upgrades the result from
deterministic stops to arbitrary behavioral deviations.

The final section proves phase domination.  Along an exact prescribed
Nash--Bellman path, every deterministic stop reached inside a finite window
is bounded by the annotation at the window's start.  This is strategic
local optimality; endpoint drift alone has no such implication.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Value obtained by refusing to quit forever against a periodic window. -/
def quittingPeriodicWindowRefusalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootSequencePureTimeTerminalValue reward roots who none 0

/-- Value obtained by quitting at a phase in the first pass. -/
def quittingPeriodicWindowPhaseStopValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {period : ℕ}
    (phase : Fin period) : ℝ :=
  quittingRootSequencePureTimeTerminalValue reward roots who
    (some phase.val) 0

/-- Best stop value among the finitely many phases of one nonempty pass. -/
def quittingPeriodicWindowBestPhaseStop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ)
    [NeZero period] : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty :
    (Finset.univ : Finset (Fin period)).Nonempty)
    (quittingPeriodicWindowPhaseStopValue reward roots who)

/-- Exact finite best-response statistic of a periodic window. -/
def quittingPeriodicWindowBestResponseValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ)
    [NeZero period] : ℝ :=
  max (quittingPeriodicWindowRefusalValue reward roots who)
    (quittingPeriodicWindowBestPhaseStop reward roots who period)

omit [Fintype ι] [DecidableEq ι] in
/-- A root sequence invariant under one period is literally its own
phase-switch restart after that period. -/
theorem quittingPhaseSwitchRoots_self_of_periodic
    (roots : ℕ → ι → PMF Bool) (period : ℕ)
    (hperiodic : ∀ time, roots (time + period) = roots time) :
    quittingPhaseSwitchRoots roots roots period = roots := by
  funext time
  by_cases htime : time < period
  · rw [quittingPhaseSwitchRoots_of_lt roots roots htime]
  · have hle : period ≤ time := Nat.not_lt.mp htime
    rw [quittingPhaseSwitchRoots_of_le roots roots hle]
    calc
      roots (time - period) = roots ((time - period) + period) :=
        (hperiodic (time - period)).symm
      _ = roots time := by rw [Nat.sub_add_cancel hle]

/-- Updating a coordinate to sure Continue makes joint survival exactly the
deleted-player survival clock. -/
theorem quittingJointSurvivalWeight_update_none_eq_opponentSurvivalWeight
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingJointSurvivalWeight
        (quittingRootSequenceUpdate roots who
          (quittingPureTimeHazard none)) start fuel =
      quittingOpponentSurvivalWeight roots who start fuel := by
  rw [quittingJointSurvivalWeight_eq_prod]
  unfold quittingOpponentSurvivalWeight quittingFixedOpponentsContinueMass
    quittingRootSequenceUpdate
  apply Finset.prod_congr rfl
  intro offset _
  rfl

/-- Before a scheduled stop at `period + later`, the deviator continues
surely throughout the first pass, so joint survival is deleted-player
survival. -/
theorem quittingJointSurvivalWeight_update_add_period_eq_opponentSurvivalWeight
    (roots : ℕ → ι → PMF Bool) (who : ι) (period later : ℕ) :
    quittingJointSurvivalWeight
        (quittingRootSequenceUpdate roots who
          (quittingPureTimeHazard (some (period + later)))) 0 period =
      quittingOpponentSurvivalWeight roots who 0 period := by
  calc
    quittingJointSurvivalWeight
        (quittingRootSequenceUpdate roots who
          (quittingPureTimeHazard (some (period + later)))) 0 period =
      quittingJointSurvivalWeight
        (quittingRootSequenceUpdate roots who
          (quittingPureTimeHazard none)) 0 period := by
        apply quittingJointSurvivalWeight_congr
        intro offset hoffset
        simp only [Nat.zero_add, quittingRootSequenceUpdate]
        rw [quittingPureTimeHazard_some_of_ne (by omega)]
        rfl
    _ = quittingOpponentSurvivalWeight roots who 0 period :=
      quittingJointSurvivalWeight_update_none_eq_opponentSurvivalWeight
        roots who 0 period

/-- A deterministic stop scheduled after the first pass continues surely
through the truncated prefix. -/
theorem quittingTruncatedHazard_pureTime_add_period
    (period later : ℕ) :
    quittingTruncatedHazard
        (quittingPureTimeHazard (some (period + later))) period =
      quittingPureTimeHazard none := by
  funext time
  by_cases htime : time < period
  · rw [quittingTruncatedHazard_of_lt _ htime,
      quittingPureTimeHazard_some_of_ne (by omega)]
    rfl
  · rw [quittingTruncatedHazard_of_le _ (Nat.not_lt.mp htime)]
    rfl

/-- After the first pass, the shifted deterministic hazard is the same stop
phase measured from the next pass. -/
theorem quittingPureTimeHazard_add_period_shift
    (period later : ℕ) :
    (fun offset ↦
      quittingPureTimeHazard (some (period + later)) (period + offset)) =
      quittingPureTimeHazard (some later) := by
  funext offset
  simp only [quittingPureTimeHazard]
  by_cases h : offset = later
  · subst offset
    simp
  · have hne : period + offset ≠ period + later := by omega
    simp [h]

/-- Exact one-pass recursion for a deterministic stop scheduled in a later
pass. -/
theorem quittingPeriodicPureTimeTerminalValue_add_period
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period later : ℕ)
    (hperiodic : ∀ time, roots (time + period) = roots time) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some (period + later)) 0 =
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots roots period) who
          (quittingPureTimeHazard none) 0 +
        quittingOpponentSurvivalWeight roots who 0 period *
          quittingRootSequencePureTimeTerminalValue reward roots who
            (some later) 0 := by
  have hdecomp :=
    quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots
      reward roots roots period who
        (quittingPureTimeHazard (some (period + later)))
  rw [quittingPhaseSwitchRoots_self_of_periodic roots period hperiodic,
    quittingTruncatedHazard_pureTime_add_period,
    quittingJointSurvivalWeight_update_add_period_eq_opponentSurvivalWeight,
    quittingPureTimeHazard_add_period_shift] at hdecomp
  exact hdecomp

/-- The refusal value satisfies the same one-pass affine recursion. -/
theorem quittingPeriodicWindowRefusalValue_eq_prefix_add_survival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ)
    (hperiodic : ∀ time, roots (time + period) = roots time) :
    quittingPeriodicWindowRefusalValue reward roots who =
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots roots period) who
          (quittingPureTimeHazard none) 0 +
        quittingOpponentSurvivalWeight roots who 0 period *
          quittingPeriodicWindowRefusalValue reward roots who := by
  have hdecomp :=
    quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots
      reward roots roots period who (quittingPureTimeHazard none)
  have htruncated : quittingTruncatedHazard
      (quittingPureTimeHazard none) period = quittingPureTimeHazard none := by
    funext time
    by_cases htime : time < period
    · rw [quittingTruncatedHazard_of_lt _ htime]
    · rw [quittingTruncatedHazard_of_le _ (Nat.not_lt.mp htime),
        quittingPureTimeHazard_none]
  have hshift : (fun offset ↦
      quittingPureTimeHazard none (period + offset)) =
        quittingPureTimeHazard none := rfl
  rw [quittingPhaseSwitchRoots_self_of_periodic roots period hperiodic,
    htruncated,
    quittingJointSurvivalWeight_update_none_eq_opponentSurvivalWeight,
    hshift] at hdecomp
  exact hdecomp

/-- A later-pass stop is the affine interpolation between refusal and the
same phase in the preceding pass. -/
theorem quittingPeriodicPureTimeTerminalValue_add_period_eq_interpolation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period later : ℕ)
    (hperiodic : ∀ time, roots (time + period) = roots time) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some (period + later)) 0 =
      (1 - quittingOpponentSurvivalWeight roots who 0 period) *
          quittingPeriodicWindowRefusalValue reward roots who +
        quittingOpponentSurvivalWeight roots who 0 period *
          quittingRootSequencePureTimeTerminalValue reward roots who
            (some later) 0 := by
  have hlater := quittingPeriodicPureTimeTerminalValue_add_period
    reward roots who period later hperiodic
  have hrefusal :=
    quittingPeriodicWindowRefusalValue_eq_prefix_add_survival_mul
      reward roots who period hperiodic
  linarith

/-- Stripping a pass cannot beat both the refusal branch and the earlier
stop branch. -/
theorem quittingPeriodicPureTimeTerminalValue_add_period_le_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period later : ℕ)
    (hperiodic : ∀ time, roots (time + period) = roots time) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some (period + later)) 0 ≤
      max (quittingPeriodicWindowRefusalValue reward roots who)
        (quittingRootSequencePureTimeTerminalValue reward roots who
          (some later) 0) := by
  rw [quittingPeriodicPureTimeTerminalValue_add_period_eq_interpolation
    reward roots who period later hperiodic]
  have hP0 := quittingOpponentSurvivalWeight_nonneg roots who 0 period
  have hP1 := quittingOpponentSurvivalWeight_le_one roots who 0 period
  have hleft := le_max_left
    (quittingPeriodicWindowRefusalValue reward roots who)
    (quittingRootSequencePureTimeTerminalValue reward roots who
      (some later) 0)
  have hright := le_max_right
    (quittingPeriodicWindowRefusalValue reward roots who)
    (quittingRootSequencePureTimeTerminalValue reward roots who
      (some later) 0)
  nlinarith

/-- Every deterministic calendar stop folds into the refusal value or a
phase stop in the first pass. -/
theorem quittingPeriodicPureTimeTerminalValue_some_le_finiteWindow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ) [NeZero period]
    (hperiodic : ∀ time, roots (time + period) = roots time) (quitTime : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some quitTime) 0 ≤
      quittingPeriodicWindowBestResponseValue reward roots who period := by
  induction quitTime using Nat.strong_induction_on with
  | h quitTime ih =>
      by_cases hphase : quitTime < period
      · let phase : Fin period := ⟨quitTime, hphase⟩
        have hphaseLe :
            quittingPeriodicWindowPhaseStopValue reward roots who phase ≤
              quittingPeriodicWindowBestPhaseStop reward roots who period :=
          by
            unfold quittingPeriodicWindowBestPhaseStop
            exact Finset.le_sup' (f :=
              quittingPeriodicWindowPhaseStopValue reward roots who)
              (Finset.mem_univ phase)
        exact hphaseLe.trans (le_max_right _ _)
      · have hperiodPos : 0 < period := Nat.pos_of_ne_zero (NeZero.ne period)
        have hle : period ≤ quitTime := Nat.not_lt.mp hphase
        have hsplit : quitTime = period + (quitTime - period) := by omega
        have hsmaller : quitTime - period < quitTime := by omega
        rw [hsplit]
        refine (quittingPeriodicPureTimeTerminalValue_add_period_le_max
          reward roots who period (quitTime - period) hperiodic).trans ?_
        apply max_le
        · exact le_max_left _ _
        · exact ih (quitTime - period) hsmaller

/-- **Exact pure-time evaluator.**  The supremum over all deterministic quit
times and `Never` is the maximum of refusal and the finitely many phase-stop
values in one pass. -/
theorem sSup_range_quittingRootSequencePureTimeTerminalValue_eq_finiteWindow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ) [NeZero period]
    (hperiodic : ∀ time, roots (time + period) = roots time)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    sSup (Set.range fun quitTime : Option ℕ ↦
      quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0) =
      quittingPeriodicWindowBestResponseValue reward roots who period := by
  let values : Set ℝ := Set.range fun quitTime : Option ℕ ↦
    quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0
  have hbdd : BddAbove values :=
    bddAbove_range_quittingRootSequencePureTimeTerminalValue
      reward roots who hM hreward
  apply le_antisymm
  · apply csSup_le
    · exact ⟨quittingPeriodicWindowRefusalValue reward roots who, ⟨none, rfl⟩⟩
    · rintro _ ⟨quitTime, rfl⟩
      cases quitTime with
      | none => exact le_max_left _ _
      | some time =>
          exact quittingPeriodicPureTimeTerminalValue_some_le_finiteWindow
            reward roots who period hperiodic time
  · apply max_le
    · exact le_csSup hbdd ⟨none, rfl⟩
    · unfold quittingPeriodicWindowBestPhaseStop
      apply Finset.sup'_le
      intro phase _
      exact le_csSup hbdd ⟨some phase.val, rfl⟩

/-- **Exact behavioral evaluator.**  Arbitrary unilateral behavior against a
periodic window has the same finite maximum: refusal or one of the phase
stops in the first pass. -/
theorem sSup_range_quittingTerminalPayoff_update_eq_periodicWindow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (period : ℕ) [NeZero period]
    (hperiodic : ∀ time,
      quittingProfileLiveRoot reward profile (time + period) =
        quittingProfileLiveRoot reward profile time)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    sSup (Set.range fun deviation :
        (quittingGame reward).BehaviorStrategy who ↦
      quittingTerminalPayoff reward
        (Function.update profile who deviation) who) =
      quittingPeriodicWindowBestResponseValue reward
        (quittingProfileLiveRoot reward profile) who period := by
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime
    reward profile who hM hreward]
  simp_rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  exact sSup_range_quittingRootSequencePureTimeTerminalValue_eq_finiteWindow
    reward (quittingProfileLiveRoot reward profile) who period hperiodic
      hM hreward

/-! ## Phase domination under exact local Nash -/

/-- A deterministic stop after `fuel` prescribed stages is bounded by the
annotation at the window's start whenever every one-stage root is exact
Nash against the next annotation. -/
theorem quittingPureTimeTerminalValue_le_prescribed_of_exactNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time, IsεQuittingRootNash reward
      (value (time + 1)) 0 (roots time))
    (start fuel : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some (start + fuel)) start ≤ value start who := by
  induction fuel generalizing start with
  | zero =>
      rw [Nat.add_zero,
        quittingRootSequencePureTimeTerminalValue_some_self]
      have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
        reward (value (start + 1)) (roots start) who
          (hnash start)
      rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue,
        ← congrFun (hpolicy start) who] at hquit
      exact hquit
  | succ fuel ih =>
      have hne : start ≠ start + (fuel + 1) := by omega
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
        quittingPureTimeHazard_some_of_ne hne]
      simp only [PMF.pure_apply, if_neg (by decide : (true : Bool) ≠ false),
        ENNReal.toReal_zero, if_true, ENNReal.toReal_one, zero_mul, one_mul]
      have htail := ih (start + 1)
      have hidx : start + (fuel + 1) = start + 1 + fuel := by omega
      have htail' : quittingRootSequenceHazardTerminalValue reward roots who
          (quittingPureTimeHazard (some (start + (fuel + 1)))) (start + 1) ≤
          value (start + 1) who := by
        simpa only [quittingRootSequencePureTimeTerminalValue, hidx] using htail
      have hmass : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      have hcontinue := quittingRootContinuePayoff_le_successor_of_isZeroNash
        reward (value (start + 1)) (roots start) who
          (hnash start)
      rw [quittingRootContinuePayoff_eq_fixedOpponents,
        ← congrFun (hpolicy start) who] at hcontinue
      calc
        0 + (quittingFixedOpponentsContinueReward reward roots who start +
            quittingFixedOpponentsContinueMass roots who start *
              quittingRootSequenceHazardTerminalValue reward roots who
                (quittingPureTimeHazard (some (start + (fuel + 1))))
                (start + 1)) =
            quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingRootSequenceHazardTerminalValue reward roots who
                  (quittingPureTimeHazard (some (start + (fuel + 1))))
                  (start + 1) := by ring
        _ ≤ quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                value (start + 1) who :=
          by
            have hscaled := mul_le_mul_of_nonneg_left htail' hmass
            linarith
        _ ≤ value start who := hcontinue

/-- Every phase stop in a periodic exact-Nash prescribed window is dominated
by the initial annotation. -/
theorem quittingPeriodicWindowPhaseStopValue_le_prescribed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time, IsεQuittingRootNash reward
      (value (time + 1)) 0 (roots time))
    {period : ℕ} (phase : Fin period) :
    quittingPeriodicWindowPhaseStopValue reward roots who phase ≤
      value 0 who := by
  simpa [quittingPeriodicWindowPhaseStopValue] using
    quittingPureTimeTerminalValue_le_prescribed_of_exactNash
      reward roots who value hpolicy hnash 0 phase.val

/-- Consequently the best phase-stop statistic of a nonempty exact-Nash
window is bounded by its initial annotation. -/
theorem quittingPeriodicWindowBestPhaseStop_le_prescribed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time, IsεQuittingRootNash reward
      (value (time + 1)) 0 (roots time))
    (period : ℕ) [NeZero period] :
    quittingPeriodicWindowBestPhaseStop reward roots who period ≤
      value 0 who := by
  unfold quittingPeriodicWindowBestPhaseStop
  apply Finset.sup'_le
  intro phase _
  exact quittingPeriodicWindowPhaseStopValue_le_prescribed
    reward roots who value hpolicy hnash phase

/-! ## Exact escape form and the favorable-drift regression -/

/-- Exceeding a delivery target has exactly two finite causes: refusal, or a
specific phase stop.  `Never` is included literally in the refusal branch,
including the deleted-survival-one case where its payoff is zero. -/
theorem lt_quittingPeriodicWindowBestResponseValue_sub_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ) [NeZero period]
    (delivery ε : ℝ) :
    ε < quittingPeriodicWindowBestResponseValue reward roots who period -
        delivery ↔
      ε < quittingPeriodicWindowRefusalValue reward roots who - delivery ∨
        ∃ phase : Fin period,
          ε < quittingPeriodicWindowPhaseStopValue reward roots who phase -
            delivery := by
  let nonempty : (Finset.univ : Finset (Fin period)).Nonempty :=
    Finset.univ_nonempty
  unfold quittingPeriodicWindowBestResponseValue
    quittingPeriodicWindowBestPhaseStop
  have hmax : max (quittingPeriodicWindowRefusalValue reward roots who)
          (Finset.univ.sup' nonempty
            (quittingPeriodicWindowPhaseStopValue reward roots who)) - delivery =
        max (quittingPeriodicWindowRefusalValue reward roots who - delivery)
          (Finset.univ.sup' nonempty
            (quittingPeriodicWindowPhaseStopValue reward roots who) -
              delivery) := by
    rcases le_total
        (quittingPeriodicWindowRefusalValue reward roots who)
        (Finset.univ.sup' nonempty
          (quittingPeriodicWindowPhaseStopValue reward roots who)) with h | h
    · rw [max_eq_right h, max_eq_right (sub_le_sub_right h delivery)]
    · rw [max_eq_left h, max_eq_left (sub_le_sub_right h delivery)]
  constructor
  · intro h
    rw [hmax, lt_max_iff] at h
    rcases h with hrefusal | hphase
    · exact Or.inl hrefusal
    · right
      have hphase' : ε + delivery < Finset.univ.sup' nonempty
          (quittingPeriodicWindowPhaseStopValue reward roots who) := by
        linarith
      rw [Finset.lt_sup'_iff nonempty] at hphase'
      obtain ⟨phase, _, hphaseValue⟩ := hphase'
      exact ⟨phase, by linarith⟩
  · rintro (hrefusal | ⟨phase, hphase⟩)
    · rw [hmax, lt_max_iff]
      exact Or.inl hrefusal
    · rw [hmax, lt_max_iff]
      right
      have hphaseValue : ε + delivery <
          quittingPeriodicWindowPhaseStopValue reward roots who phase := by
        linarith
      have hphaseSup : ε + delivery < Finset.univ.sup' nonempty
          (quittingPeriodicWindowPhaseStopValue reward roots who) :=
        (Finset.lt_sup'_iff nonempty).2
          ⟨phase, Finset.mem_univ phase, hphaseValue⟩
      linarith

omit [DecidableEq ι] in
/-- A periodic root sequence realizes exactly the normalized absorbing
delivery of one pass whenever that pass has positive absorption. -/
theorem quittingRootSequenceTerminalValue_eq_windowRestartDelivery_of_periodic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ)
    (hperiodic : ∀ time, roots (time + period) = roots time)
    (hsurvival : quittingJointSurvivalWeight roots 0 period < 1) :
    quittingRootSequenceTerminalValue reward roots who 0 =
      quittingWindowRestartDelivery reward roots who 0 period := by
  have hdecomp := quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots
    reward roots roots period who
  rw [quittingPhaseSwitchRoots_self_of_periodic roots period hperiodic] at hdecomp
  have hmass : 1 - quittingJointSurvivalWeight roots 0 period ≠ 0 := by
    linarith
  rw [quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum]
    at hdecomp
  unfold quittingWindowRestartDelivery quittingWindowAbsorbingIntercept
  simp only [Nat.zero_add] at hdecomp ⊢
  apply (eq_div_iff hmass).2
  linarith

/-- **Favorable-drift regression.**  Along an exact Nash--Bellman source
window, positive signed drift (`value period ≤ value 0`) can make the
periodic restart *overdeliver*.  If refusal is also below that delivery,
then the restart's entire behavioral best-response value is below delivery.
Hence drift magnitude is not an exploitability certificate. -/
theorem quittingPeriodicWindowBestResponseValue_le_restartDelivery_of_drift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time, IsεQuittingRootNash reward
      (value (time + 1)) 0 (roots time))
    (period : ℕ) [NeZero period]
    (hsurvival : quittingJointSurvivalWeight roots 0 period < 1)
    (hdrift : value period who ≤ value 0 who)
    (hrefusal : quittingPeriodicWindowRefusalValue reward roots who ≤
      quittingWindowRestartDelivery reward roots who 0 period) :
    quittingPeriodicWindowBestResponseValue reward roots who period ≤
      quittingWindowRestartDelivery reward roots who 0 period := by
  have hprescribed : IsQuittingLivePrescribedValue reward roots who
      (fun time ↦ value time who) := by
    intro time
    have hcoordinate := congrFun (hpolicy time) who
    rw [quittingRootSuccessorPayoff_apply_eq_affine] at hcoordinate
    rw [quittingRootSuccessorPayoff_apply_eq_affine]
    exact hcoordinate
  have hseam := quittingWindowRestartDelivery_sub_prescribed
    reward roots who (fun time ↦ value time who) hprescribed 0 period hsurvival
  simp only [Nat.zero_add] at hseam
  have hmass : 0 < 1 - quittingJointSurvivalWeight roots 0 period := by
    linarith
  have hdelivery : value 0 who ≤
      quittingWindowRestartDelivery reward roots who 0 period := by
    have hsurvivalNonneg := quittingJointSurvivalWeight_nonneg roots 0 period
    nlinarith
  unfold quittingPeriodicWindowBestResponseValue
  apply max_le hrefusal
  exact (quittingPeriodicWindowBestPhaseStop_le_prescribed
    reward roots who value hpolicy hnash period).trans hdelivery

/-! ## The corrected arbitrarily-late alternative -/

/-- A calendar-indexed family of nonempty periodic windows together with the
payoff delivered by each restart.  `periodIndex + 1` keeps nonemptiness in
the type of the API. -/
structure QuittingPeriodicWindowFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  roots : ℕ → ℕ → ι → PMF Bool
  periodIndex : ℕ → ℕ
  delivery : ℕ → Payoff ι
  periodic : ∀ window time,
    roots window (time + (periodIndex window + 1)) = roots window time

namespace QuittingPeriodicWindowFamily

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Exact coordinatewise exploitability statistic of one periodic restart. -/
def coordinateGap
    (family : QuittingPeriodicWindowFamily reward)
    (window : ℕ) (who : ι) : ℝ :=
  quittingPeriodicWindowBestResponseValue reward (family.roots window) who
      (family.periodIndex window + 1) - family.delivery window who

/-- Arbitrarily late windows have arbitrarily small exploitability in every
coordinate. -/
def LateRepairable (family : QuittingPeriodicWindowFamily reward) : Prop :=
  ∀ ε, 0 < ε → ∀ threshold,
    ∃ window, threshold ≤ window ∧ ∀ who, family.coordinateGap window who ≤ ε

/-- Every sufficiently late window has either a profitable refusal/`Never`
branch or a profitable concrete phase stop. -/
def EventuallyPayoffBlocked
    (family : QuittingPeriodicWindowFamily reward) : Prop :=
  ∃ ε, 0 < ε ∧ ∃ threshold, ∀ window, threshold ≤ window →
    ∃ who,
      ε < quittingPeriodicWindowRefusalValue reward
            (family.roots window) who - family.delivery window who ∨
        ∃ phase : Fin (family.periodIndex window + 1),
          ε < quittingPeriodicWindowPhaseStopValue reward
              (family.roots window) who phase - family.delivery window who

/-- Failure of arbitrarily-late repair is exactly eventual payoff blocking
by the two finite evaluator branches.  This is the corrected quantifier and
the corrected strategic taxonomy.  Splitting its phase branch further into
solo-promise versus collision error is an asymptotic tail estimate, not part
of this logical alternative. -/
theorem lateRepairable_or_eventuallyPayoffBlocked
    (family : QuittingPeriodicWindowFamily reward) :
    family.LateRepairable ∨
      (¬family.LateRepairable ∧ family.EventuallyPayoffBlocked) := by
  classical
  by_cases hrepair : family.LateRepairable
  · exact Or.inl hrepair
  · right
    refine ⟨hrepair, ?_⟩
    unfold LateRepairable at hrepair
    push Not at hrepair
    obtain ⟨ε, hε, threshold, hlate⟩ := hrepair
    refine ⟨ε, hε, threshold, fun window hwindow ↦ ?_⟩
    obtain ⟨who, hgap⟩ := hlate window hwindow
    have hescape :=
      (lt_quittingPeriodicWindowBestResponseValue_sub_iff reward
        (family.roots window) who (family.periodIndex window + 1)
        (family.delivery window who) ε).1 hgap
    exact ⟨who, hescape⟩

/-- The two sides of the corrected late alternative are disjoint. -/
theorem not_eventuallyPayoffBlocked_of_lateRepairable
    (family : QuittingPeriodicWindowFamily reward)
    (hrepair : family.LateRepairable) :
    ¬family.EventuallyPayoffBlocked := by
  rintro ⟨ε, hε, threshold, hblocked⟩
  obtain ⟨window, hwindow, hsmall⟩ :=
    hrepair (ε / 2) (half_pos hε) threshold
  obtain ⟨who, hescape⟩ := hblocked window hwindow
  have hgap :=
    (lt_quittingPeriodicWindowBestResponseValue_sub_iff reward
      (family.roots window) who (family.periodIndex window + 1)
      (family.delivery window who) ε).2 hescape
  have hsmallWho := hsmall who
  unfold coordinateGap at hsmallWho
  linarith

end QuittingPeriodicWindowFamily

end GameTheory
