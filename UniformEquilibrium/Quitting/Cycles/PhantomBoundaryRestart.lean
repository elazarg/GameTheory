/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.SequenceVariation
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Phantom boundary and one-window restart identities

A bounded sequence satisfying the quitting policy-evaluation recursion need
not equal the terminal payoff of its root sequence.  This module identifies
the discrepancy exactly.  If the prescribed value converges to `boundary`,
then

`prescribed start = terminalValue start + survivalLimit start * boundary`.

Thus the only semantic mismatch is the value attached to the event that play
never absorbs.  The result does not identify a Bellman annotation with an
actual terminal payoff when limiting survival is positive.

The finite companion identity records the same phenomenon on a window.  The
payoff obtained by repeating a positive-absorption window is its absorbing
intercept divided by absorbed mass, and its displacement from the initial
annotation is exactly signed endpoint drift divided by absorbed mass.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The absorbing payoff collected strictly inside a finite root window. -/
def quittingWindowAbsorbingIntercept
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range fuel,
    quittingJointSurvivalWeight roots start offset *
      quittingRootAbsorbingContribution reward (roots (start + offset)) who

/-- Normalized payoff delivered by repeating a finite root window.  This
definition is used only when the window has positive absorption mass. -/
def quittingWindowRestartDelivery
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) : ℝ :=
  quittingWindowAbsorbingIntercept reward roots who start fuel /
    (1 - quittingJointSurvivalWeight roots start fuel)

omit [DecidableEq ι] in
/-- A prescribed path is its finite absorbing intercept plus the surviving
far-end annotation. -/
theorem quittingPrescribedValue_eq_windowIntercept_add_survival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (start fuel : ℕ) :
    prescribed start =
      quittingWindowAbsorbingIntercept reward roots who start fuel +
        quittingJointSurvivalWeight roots start fuel *
          prescribed (start + fuel) := by
  simpa [quittingWindowAbsorbingIntercept] using
    eq_sum_jointSurvivalWeight_mul_absorbingContribution_add
      reward roots who prescribed hprescribed start fuel

omit [DecidableEq ι] in
/-- **Exact periodic-restart seam.**  Repeating a window transforms its
signed endpoint drift into a normalized delivery displacement. -/
theorem quittingWindowRestartDelivery_sub_prescribed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (start fuel : ℕ)
    (hsurvival : quittingJointSurvivalWeight roots start fuel < 1) :
    (1 - quittingJointSurvivalWeight roots start fuel) *
        (quittingWindowRestartDelivery reward roots who start fuel -
          prescribed start) =
      quittingJointSurvivalWeight roots start fuel *
        (prescribed start - prescribed (start + fuel)) := by
  have hmass : 1 - quittingJointSurvivalWeight roots start fuel ≠ 0 := by
    linarith
  have htelescope :=
    quittingPrescribedValue_eq_windowIntercept_add_survival_mul
      reward roots who prescribed hprescribed start fuel
  unfold quittingWindowRestartDelivery
  field_simp [hmass]
  linarith

omit [DecidableEq ι] in
/-- Finite `Never` truncations converge to the actual root-sequence terminal
payoff.  This holds in both survival regimes: vanishing survival kills the
boundary directly, while positive limiting survival uses the conditional
tail-absorption estimate. -/
theorem tendsto_quittingRootSequenceTerminalValue_truncatedRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Tendsto (fun fuel ↦ quittingRootSequenceTerminalValue reward
        (quittingTruncatedRoots (fun time ↦ roots (start + time)) fuel)
        who 0) atTop
      (nhds (quittingRootSequenceTerminalValue reward roots who start)) := by
  classical
  let shifted : ℕ → ι → PMF Bool := fun time ↦ roots (start + time)
  have hterminalShift :
      quittingRootSequenceTerminalValue reward shifted who 0 =
        quittingRootSequenceTerminalValue reward roots who start := by
    symm
    exact quittingRootSequenceTerminalValue_eq_shift reward roots who start
  by_cases hlimitZero : quittingJointSurvivalLimit shifted 0 = 0
  · have hsurvival : Tendsto (quittingJointSurvivalWeight shifted 0)
        atTop (nhds 0) := by
      simpa [hlimitZero] using tendsto_quittingJointSurvivalLimit shifted 0
    have hbound : ∀ fuel,
        |quittingRootSequenceTerminalValue reward shifted who 0 -
          quittingRootSequenceTerminalValue reward
            (quittingTruncatedRoots shifted fuel) who 0| ≤
          M * quittingJointSurvivalWeight shifted 0 fuel := by
      intro fuel
      let capped := quittingTruncatedRoots shifted fuel
      have hcappedTail :
          quittingRootSequenceTerminalValue reward capped who fuel = 0 :=
        quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
          reward capped who fuel fun time htime ↦
            quittingTruncatedRoots_of_le shifted htime
      have hprefix : ∀ time, time < fuel → shifted time = capped time := by
        intro time htime
        exact (quittingTruncatedRoots_of_lt shifted htime).symm
      have hscale :=
        quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul
          reward shifted capped who fuel hprefix
      have htail := abs_quittingRootSequenceTerminalValue_le
        reward shifted who fuel hM hreward
      have hsurvivalEq : quittingJointSurvivalWeight capped 0 fuel =
          quittingJointSurvivalWeight shifted 0 fuel := by
        exact quittingJointSurvivalWeight_quittingTruncatedRoots
          shifted fuel fuel le_rfl
      rw [hcappedTail, sub_zero] at hscale
      rw [hscale, hsurvivalEq, abs_mul,
        abs_of_nonneg (quittingJointSurvivalWeight_nonneg shifted 0 fuel)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left htail
        (quittingJointSurvivalWeight_nonneg shifted 0 fuel)
    have hmajorant : Tendsto
        (fun fuel ↦ M * quittingJointSurvivalWeight shifted 0 fuel)
        atTop (nhds 0) := by simpa using hsurvival.const_mul M
    have hconv : Tendsto (fun fuel ↦
        quittingRootSequenceTerminalValue reward
          (quittingTruncatedRoots shifted fuel) who 0) atTop
        (nhds (quittingRootSequenceTerminalValue reward shifted who 0)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨threshold, hthreshold⟩ :=
        (Metric.tendsto_atTop.mp hmajorant) ε hε
      exact ⟨threshold, fun fuel hfuel ↦ by
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (by
          simpa [abs_sub_comm] using hbound fuel) (by
            have hclose := hthreshold fuel hfuel
            rw [Real.dist_eq, sub_zero,
              abs_of_nonneg (mul_nonneg hM
                (quittingJointSurvivalWeight_nonneg shifted 0 fuel))] at hclose
            exact hclose)⟩
    simpa [shifted, hterminalShift] using hconv
  · have hpositive : 0 < quittingJointSurvivalLimit shifted 0 :=
      lt_of_le_of_ne (quittingJointSurvivalLimit_nonneg shifted 0)
        (Ne.symm hlimitZero)
    have hconv := tendsto_quittingRootSequenceTerminalValue_elementaryNever
      reward shifted who hM hreward hpositive
    simpa only [quittingElementaryTailRoots_never, hterminalShift] using hconv

omit [DecidableEq ι] in
/-- **Phantom-boundary decomposition.**  A convergent bounded prescribed
path differs from the actual terminal payoff by precisely the limiting
survival probability times its limiting annotation. -/
theorem quittingPrescribedValue_eq_terminalValue_add_survivalLimit_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {boundary M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hboundary : Tendsto prescribed atTop (nhds boundary))
    (start : ℕ) :
    prescribed start =
      quittingRootSequenceTerminalValue reward roots who start +
        quittingJointSurvivalLimit roots start * boundary := by
  let shifted : ℕ → ι → PMF Bool := fun time ↦ roots (start + time)
  have hfinite : ∀ fuel,
      prescribed start =
        quittingRootSequenceTerminalValue reward
            (quittingTruncatedRoots shifted fuel) who 0 +
          quittingJointSurvivalWeight roots start fuel *
            prescribed (start + fuel) := by
    intro fuel
    rw [quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum]
    simpa [shifted, quittingWindowAbsorbingIntercept,
      quittingJointSurvivalWeight_eq_shift] using
      quittingPrescribedValue_eq_windowIntercept_add_survival_mul
        reward roots who prescribed hprescribed start fuel
  have htruncated :=
    tendsto_quittingRootSequenceTerminalValue_truncatedRoots
      reward roots who start hM hreward
  have hsurvival := tendsto_quittingJointSurvivalLimit roots start
  have hfar : Tendsto (fun fuel ↦ prescribed (start + fuel)) atTop
      (nhds boundary) := by
    simpa [Function.comp_def, Nat.add_comm] using
      hboundary.comp (tendsto_add_atTop_nat start)
  have hrhs := htruncated.add (hsurvival.mul hfar)
  apply tendsto_nhds_unique
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ prescribed start) atTop
      (nhds (prescribed start)))
  exact hrhs.congr (fun fuel ↦ (hfinite fuel).symm)

omit [DecidableEq ι] in
/-- Vector-path form of the phantom-boundary decomposition used by exact
Nash--Bellman tails. -/
theorem quittingValuePath_eq_terminalValue_add_survivalLimit_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (boundary : Payoff ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hboundary : ∀ who,
      Tendsto (fun time ↦ value time who) atTop (nhds (boundary who)))
    (start : ℕ) :
    value start = fun who ↦
      quittingRootSequenceTerminalValue reward roots who start +
        quittingJointSurvivalLimit roots start * boundary who := by
  funext who
  have hprescribed : IsQuittingLivePrescribedValue reward roots who
      (fun time ↦ value time who) := by
    intro time
    have hcoordinate := congrFun (hpolicy time) who
    rw [quittingRootSuccessorPayoff_apply_eq_affine] at hcoordinate
    rw [quittingRootSuccessorPayoff_apply_eq_affine]
    exact hcoordinate
  exact quittingPrescribedValue_eq_terminalValue_add_survivalLimit_mul
    reward roots who (fun time ↦ value time who) hprescribed hM hreward
      (hboundary who) start

omit [DecidableEq ι] in
/-- One policy-evaluation step moves by at most twice the payoff bound times
the stage's joint absorption mass. -/
theorem abs_quittingPrescribedValue_succ_sub_le_absorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : ∀ time, |prescribed time| ≤ M) (time : ℕ) :
    |prescribed (time + 1) - prescribed time| ≤
      2 * M * quittingRootAbsorptionMass (roots time) := by
  rw [hprescribed time]
  simpa [abs_sub_comm] using
    abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
      reward (fun _ ↦ prescribed (time + 1)) (roots time) who M hreward
      (hbound (time + 1))

omit [DecidableEq ι] in
/-- **Remaining-charge modulus for annotations.**  The distance from a
prescribed value to its limit is controlled by the remaining total joint
absorption charge. -/
theorem abs_quittingPrescribedValue_sub_limit_le_tailCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    {boundary M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : ∀ time, |prescribed time| ≤ M)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (hboundary : Tendsto prescribed atTop (nhds boundary)) (start : ℕ) :
    |prescribed start - boundary| ≤
      2 * M * ∑' offset : ℕ,
        quittingRootAbsorptionMass (roots (start + offset)) := by
  let charge : ℕ → ℝ := fun offset ↦
    quittingRootAbsorptionMass (roots (start + offset))
  have hchargeShift : Summable charge := by
    have hinjective : Function.Injective (fun offset : ℕ ↦ start + offset) := by
      intro first second heq
      exact Nat.add_left_cancel heq
    simpa [charge, Function.comp_def] using
      hcharge.comp_injective hinjective
  have hchargeNonneg : ∀ offset, 0 ≤ charge offset := fun offset ↦ by
    exact sub_nonneg.mpr
      (quittingStationaryContinueMass_le_one (roots (start + offset)))
  have hfar : Tendsto (fun fuel ↦ prescribed (start + fuel)) atTop
      (nhds boundary) := by
    simpa [Function.comp_def, Nat.add_comm] using
      hboundary.comp (tendsto_add_atTop_nat start)
  have hleft : Tendsto
      (fun fuel ↦ |prescribed start - prescribed (start + fuel)|) atTop
      (nhds |prescribed start - boundary|) :=
    (tendsto_const_nhds.sub hfar).abs
  apply le_of_tendsto' hleft
  intro fuel
  have htelescope :
      prescribed (start + fuel) - prescribed start =
        ∑ offset ∈ Finset.range fuel,
          (prescribed (start + (offset + 1)) -
            prescribed (start + offset)) := by
    have hsum := Finset.sum_range_sub
      (fun offset ↦ prescribed (start + offset)) fuel
    simpa [Nat.add_assoc] using hsum.symm
  calc
    |prescribed start - prescribed (start + fuel)| =
        |∑ offset ∈ Finset.range fuel,
          (prescribed (start + (offset + 1)) -
            prescribed (start + offset))| := by
      rw [abs_sub_comm, htelescope]
    _ ≤ ∑ offset ∈ Finset.range fuel,
          |prescribed (start + (offset + 1)) -
            prescribed (start + offset)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ offset ∈ Finset.range fuel, 2 * M * charge offset := by
      apply Finset.sum_le_sum
      intro offset _
      simpa [charge, Nat.add_assoc] using
        abs_quittingPrescribedValue_succ_sub_le_absorptionMass
          reward roots who prescribed hprescribed hreward hbound
            (start + offset)
    _ = 2 * M * ∑ offset ∈ Finset.range fuel, charge offset := by
      rw [Finset.mul_sum]
    _ ≤ 2 * M * ∑' offset : ℕ, charge offset := by
      exact mul_le_mul_of_nonneg_left
        (hchargeShift.sum_le_tsum (Finset.range fuel)
          (fun offset _ ↦ hchargeNonneg offset)) (mul_nonneg (by norm_num) hM)

omit [DecidableEq ι] in
/-- Vector-path form of the remaining-charge modulus. -/
theorem abs_quittingValuePath_sub_limit_le_tailCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (boundary : Payoff ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : ∀ time who, |value time who| ≤ M)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (hboundary : ∀ who,
      Tendsto (fun time ↦ value time who) atTop (nhds (boundary who)))
    (start : ℕ) (who : ι) :
    |value start who - boundary who| ≤
      2 * M * ∑' offset : ℕ,
        quittingRootAbsorptionMass (roots (start + offset)) := by
  have hprescribed : IsQuittingLivePrescribedValue reward roots who
      (fun time ↦ value time who) := by
    intro time
    have hcoordinate := congrFun (hpolicy time) who
    rw [quittingRootSuccessorPayoff_apply_eq_affine] at hcoordinate
    rw [quittingRootSuccessorPayoff_apply_eq_affine]
    exact hcoordinate
  exact abs_quittingPrescribedValue_sub_limit_le_tailCharge reward roots who
    (fun time ↦ value time who) hprescribed hM hreward
      (fun time ↦ hbound time who) hcharge (hboundary who) start

omit [DecidableEq ι] in
/-- Limiting live mass of a root-sequence profile equals its canonical joint
survival limit from the same start. -/
theorem quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : ℕ) :
    quittingLiveMassLimit reward
        (quittingRootSequenceProfile reward roots start) =
      quittingJointSurvivalLimit roots start := by
  let shifted : ℕ → ι → PMF Bool := fun time ↦ roots (start + time)
  have hprofile : quittingRootSequenceProfile reward roots start =
      quittingRootSequenceProfile reward shifted 0 :=
    quittingRootSequenceProfile_eq_shift reward roots start
  have hlive : Tendsto (quittingLiveMass reward
      (quittingRootSequenceProfile reward roots start)) atTop
      (nhds (quittingJointSurvivalLimit roots start)) := by
    rw [hprofile]
    have heq : quittingLiveMass reward
        (quittingRootSequenceProfile reward shifted 0) =
          quittingJointSurvivalWeight roots start := by
      funext fuel
      rw [← quittingJointSurvivalWeight_eq_liveMass_rootSequence
        reward shifted fuel]
      exact (quittingJointSurvivalWeight_eq_shift roots start fuel).symm
    rw [heq]
    exact tendsto_quittingJointSurvivalLimit roots start
  exact tendsto_nhds_unique
    (tendsto_quittingLiveMass reward
      (quittingRootSequenceProfile reward roots start)) hlive

omit [DecidableEq ι] in
/-- Actual terminal payoff is bounded by the probability of eventual
absorption from the selected start. -/
theorem abs_quittingRootSequenceTerminalValue_le_one_sub_survivalLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootSequenceTerminalValue reward roots who start| ≤
      M * (1 - quittingJointSurvivalLimit roots start) := by
  unfold quittingRootSequenceTerminalValue
  simpa [quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit]
    using abs_quittingTerminalPayoff_le_absorbedMass reward
      (quittingRootSequenceProfile reward roots start) who hreward

omit [DecidableEq ι] in
/-- The eventual absorption probability is at most the unweighted remaining
sum of one-stage absorption masses. -/
theorem one_sub_quittingJointSurvivalLimit_le_tailCharge
    (roots : ℕ → ι → PMF Bool) (start : ℕ)
    (hcharge : Summable (fun offset ↦
      quittingRootAbsorptionMass (roots (start + offset)))) :
    1 - quittingJointSurvivalLimit roots start ≤
      ∑' offset : ℕ, quittingRootAbsorptionMass (roots (start + offset)) := by
  let charge : ℕ → ℝ := fun offset ↦
    quittingRootAbsorptionMass (roots (start + offset))
  have hchargeNonneg : ∀ offset, 0 ≤ charge offset := fun offset ↦ by
    exact sub_nonneg.mpr
      (quittingStationaryContinueMass_le_one (roots (start + offset)))
  have hlimit : Tendsto
      (fun fuel ↦ 1 - quittingJointSurvivalWeight roots start fuel) atTop
      (nhds (1 - quittingJointSurvivalLimit roots start)) :=
    tendsto_const_nhds.sub (tendsto_quittingJointSurvivalLimit roots start)
  apply le_of_tendsto' hlimit
  intro fuel
  rw [← sum_quittingJointSurvivalWeight_mul_one_sub_continueMass]
  calc
    (∑ offset ∈ Finset.range fuel,
      quittingJointSurvivalWeight roots start offset *
        (1 - quittingStationaryContinueMass (roots (start + offset)))) ≤
        ∑ offset ∈ Finset.range fuel, charge offset := by
      apply Finset.sum_le_sum
      intro offset _
      have hweight := quittingJointSurvivalWeight_le_one roots start offset
      have hnonneg := hchargeNonneg offset
      simpa [charge, quittingRootAbsorptionMass] using
        mul_le_of_le_one_left hnonneg hweight
    _ ≤ ∑' offset : ℕ, charge offset :=
      hcharge.sum_le_tsum (Finset.range fuel)
        (fun offset _ ↦ hchargeNonneg offset)

omit [DecidableEq ι] in
/-- **Remaining-charge modulus for realized payoff.**  Actual terminal
payoff is at most the reward bound times the remaining joint absorption
charge. -/
theorem abs_quittingRootSequenceTerminalValue_le_tailCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcharge : Summable (fun offset ↦
      quittingRootAbsorptionMass (roots (start + offset)))) :
    |quittingRootSequenceTerminalValue reward roots who start| ≤
      M * ∑' offset : ℕ,
        quittingRootAbsorptionMass (roots (start + offset)) := by
  exact (abs_quittingRootSequenceTerminalValue_le_one_sub_survivalLimit
    reward roots who start hreward).trans
      (mul_le_mul_of_nonneg_left
        (one_sub_quittingJointSurvivalLimit_le_tailCharge roots start hcharge)
        hM)

end GameTheory
