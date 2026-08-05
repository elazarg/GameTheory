/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticFinkObstruction

/-!
# Positive supported-action representatives of Fink obstruction flows

A signed Fink action flow is not operationally oriented.  This file
isolates the first repair: add a multiple of the prescribed mixed action at
each state and player.  The prescribed mixture has zero average transition
gain and zero average Bellman charge, so this changes neither obstruction
identity.

This action repair is separate from residual/occupation repair.  In
particular it does not claim that the residual weights are nonnegative or
that the resulting perturbation flow is already an actual occupation
circulation.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.PMFProduct Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- Averaging pure deviations with the mixed action that generated them
returns the original product distribution. -/
theorem finkProfile_weighted_pureDeviationGain_sum_eq_zero
    {U : ℝ} (z : G.finkDomain U)
    (payoff : G.JointAct → ℝ) (s : G.State) (who : ι) :
    ∑ d, (G.finkProfile z s who d).toReal *
      (expect
          (pmfPi
            (Function.update (G.finkProfile z s) who (PMF.pure d)))
          payoff -
        expect (pmfPi (G.finkProfile z s)) payoff) = 0 := by
  let x := G.finkProfile z s
  let baseline := expect (pmfPi x) payoff
  have hmix :
      expect (x who) (fun d =>
          expect (pmfPi (Function.update x who (PMF.pure d))) payoff) =
        baseline := by
    calc
      expect (x who) (fun d =>
          expect (pmfPi (Function.update x who (PMF.pure d))) payoff) =
          expect (pmfPi (Function.update x who (x who))) payoff := by
            rw [pmfPi_update_bind, expect_bind]
      _ = baseline := by
        simp only [Function.update_eq_self, baseline]
  calc
    (∑ d, (G.finkProfile z s who d).toReal *
      (expect
          (pmfPi
            (Function.update (G.finkProfile z s) who (PMF.pure d)))
          payoff -
        expect (pmfPi (G.finkProfile z s)) payoff)) =
        expect (x who) (fun d =>
          expect (pmfPi (Function.update x who (PMF.pure d))) payoff -
            baseline) := by
              simp only [Math.Probability.expect_eq_sum, x, baseline]
    _ = expect (x who) (fun d =>
          expect (pmfPi (Function.update x who (PMF.pure d))) payoff) -
        expect (x who) (fun _ => baseline) := by
          rw [expect_sub]
    _ = 0 := by rw [hmix, expect_const]; exact sub_self baseline

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- The prescribed mixed action has zero average continuation gain. -/
theorem finkProfile_weighted_continuationGain_sum_eq_zero
    {U : ℝ} (z : G.finkDomain U)
    (W : G.State → Payoff ι) (s : G.State) (who : ι) :
    ∑ d, (G.finkProfile z s who d).toReal *
      G.finkContinuationGain W z s who d = 0 := by
  let payoff : G.JointAct → ℝ := fun a =>
    expect (G.transition s a) (fun s' => W s' who)
  simpa only [finkContinuationGain, payoff] using
    G.finkProfile_weighted_pureDeviationGain_sum_eq_zero
      z payoff s who

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- The prescribed mixed action has zero average stage gain. -/
theorem finkProfile_weighted_stageGain_sum_eq_zero
    {U : ℝ} (z : G.finkDomain U) (s : G.State) (who : ι) :
    ∑ d, (G.finkProfile z s who d).toReal *
      G.finkStageGain z s who d = 0 := by
  let payoff : G.JointAct → ℝ := fun a => G.stagePayoff s a who
  simpa only [finkStageGain, mixedStageEU, payoff] using
    G.finkProfile_weighted_pureDeviationGain_sum_eq_zero
      z payoff s who

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- The prescribed mixed action has zero average one-step Bellman gain. -/
theorem finkProfile_weighted_stage_add_continuationGain_sum_eq_zero
    {U : ℝ} (z : G.finkDomain U)
    (W : G.State → Payoff ι) (s : G.State) (who : ι) :
    ∑ d, (G.finkProfile z s who d).toReal *
      (G.finkStageGain z s who d +
        G.finkContinuationGain W z s who d) = 0 := by
  let payoff : G.JointAct → ℝ := fun a =>
    G.stagePayoff s a who +
      expect (G.transition s a) (fun s' => W s' who)
  simpa only [finkStageGain, finkContinuationGain, mixedStageEU,
      payoff, expect_add, sub_add_sub_comm] using
    G.finkProfile_weighted_pureDeviationGain_sum_eq_zero
      z payoff s who

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- Coordinate form of the zero average continuation gain. -/
theorem finkProfile_weighted_pureDeviationKernel_sub_sum_eq_zero
    {U : ℝ} (z : G.finkDomain U)
    (s destination : G.State) (who : ι) :
    ∑ d, (G.finkProfile z s who d).toReal *
      ((G.finkPureDeviationStateKernel z s who d destination).toReal -
        (G.finkStateKernel z s destination).toReal) = 0 := by
  classical
  have h :=
    G.finkProfile_weighted_continuationGain_sum_eq_zero z
      (G.finkPlayerPotential who (Pi.single destination 1)) s who
  simpa [G.finkContinuationGain_playerPotential_self,
    Math.Probability.expect_pi_single] using h

omit [∀ i, DecidableEq (G.Act i)] in
/-- The profile-weighted supported-action columns of the semantic Fink
balance matrix sum to zero. -/
theorem finkProfile_weighted_finkObstructionBalance_action_sum_eq_zero
    {U : ℝ} (z : G.finkDomain U)
    (row : FinkObstructionRow G) :
    ∑ e : Σ who : ι, G.State × G.Act who,
      (G.finkProfile z e.2.1 e.1 e.2.2).toReal *
        G.finkObstructionBalance z row (Sum.inr e) = 0 := by
  rcases row with ⟨rowWho, destination⟩
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single rowWho]
  · apply Finset.sum_eq_zero
    intro s _
    have h :=
      G.finkProfile_weighted_pureDeviationKernel_sub_sum_eq_zero
        z s destination rowWho
    calc
      (∑ d, (G.finkProfile z s rowWho d).toReal *
        G.finkObstructionBalance z (rowWho, destination)
          (Sum.inr ⟨rowWho, s, d⟩)) =
          ∑ d, (G.finkProfile z s rowWho d).toReal *
            ((G.finkPureDeviationStateKernel
                z s rowWho d destination).toReal -
              (G.finkStateKernel z s destination).toReal) := by
            apply Finset.sum_congr rfl
            intro d _
            by_cases hsupported :
                G.finkProfile z s rowWho d ≠ 0
            · simp [finkObstructionBalance, hsupported]
            · have hzero :
                  (G.finkProfile z s rowWho d).toReal = 0 := by
                rw [ENNReal.toReal_eq_zero_iff]
                exact Or.inl (not_ne_iff.mp hsupported)
              simp [finkObstructionBalance, hsupported, hzero]
      _ = 0 := h
  · intro other hother
    simp [finkObstructionBalance, hother]

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- The profile-weighted supported-action entries of the semantic Fink
target row sum to zero. -/
theorem finkProfile_weighted_finkObstructionMass_action_sum_eq_zero
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) :
    ∑ e : Σ who : ι, G.State × G.Act who,
      (G.finkProfile z e.2.1 e.1 e.2.2).toReal *
        G.finkObstructionMass z H K (Sum.inr e) = 0 := by
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro who _
  apply Finset.sum_eq_zero
  intro s _
  have h :=
    G.finkProfile_weighted_stage_add_continuationGain_sum_eq_zero
      z (H - K) s who
  calc
    (∑ d, (G.finkProfile z s who d).toReal *
      G.finkObstructionMass z H K
        (Sum.inr ⟨who, s, d⟩)) =
        ∑ d, (G.finkProfile z s who d).toReal *
          (G.finkStageGain z s who d +
            G.finkContinuationGain (H - K) z s who d) := by
          apply Finset.sum_congr rfl
          intro d _
          by_cases hsupported : G.finkProfile z s who d ≠ 0
          · simp [finkObstructionMass, hsupported]
          · have hzero :
                (G.finkProfile z s who d).toReal = 0 := by
              rw [ENNReal.toReal_eq_zero_iff]
              exact Or.inl (not_ne_iff.mp hsupported)
            simp [finkObstructionMass, hsupported, hzero]
    _ = 0 := h

namespace NormalizedFinkSupportTangentObstructionFlow

/-- A pointwise scale large enough to remove all negative supported-action
weights at one state and player. Unsupported actions have zero prescribed
probability and make no contribution. -/
noncomputable def actionRepairScale
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (s : G.State) (who : ι) : ℝ :=
  ∑ d, if G.finkProfile z s who d ≠ 0 then
    |F.actionWeight s who d| /
      (G.finkProfile z s who d).toReal
  else 0

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
theorem actionRepairScale_nonneg
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (s : G.State) (who : ι) :
    0 ≤ actionRepairScale z H K F s who := by
  apply Finset.sum_nonneg
  intro d _
  by_cases hsupported : G.finkProfile z s who d ≠ 0
  · rw [if_pos hsupported]
    exact div_nonneg (abs_nonneg _)
      (ENNReal.toReal_nonneg)
  · rw [if_neg hsupported]

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
theorem actionWeight_add_profile_nonneg
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (s : G.State) (who : ι) (d : G.Act who)
    (hsupported : G.finkProfile z s who d ≠ 0) :
    0 ≤ F.actionWeight s who d +
      actionRepairScale z H K F s who *
        (G.finkProfile z s who d).toReal := by
  have hprofile_pos :
      0 < (G.finkProfile z s who d).toReal :=
    ENNReal.toReal_pos hsupported (PMF.apply_ne_top _ _)
  have hterm :
      |F.actionWeight s who d| /
          (G.finkProfile z s who d).toReal ≤
        actionRepairScale z H K F s who := by
    have hterm_if :
        (if G.finkProfile z s who d ≠ 0 then
          |F.actionWeight s who d| /
            (G.finkProfile z s who d).toReal
        else 0) ≤
          ∑ d', if G.finkProfile z s who d' ≠ 0 then
          |F.actionWeight s who d'| /
            (G.finkProfile z s who d').toReal
          else 0 := by
      refine Finset.single_le_sum
        (f := fun d' : G.Act who =>
          if G.finkProfile z s who d' ≠ 0 then
            |F.actionWeight s who d'| /
              (G.finkProfile z s who d').toReal
          else 0)
        (s := Finset.univ) ?_ (Finset.mem_univ d)
      intro d' _
      by_cases hsupported' : G.finkProfile z s who d' ≠ 0
      · rw [if_pos hsupported']
        exact div_nonneg (abs_nonneg _) ENNReal.toReal_nonneg
      · rw [if_neg hsupported']
    simpa only [actionRepairScale, if_pos hsupported] using hterm_if
  have habs :
      |F.actionWeight s who d| ≤
        actionRepairScale z H K F s who *
          (G.finkProfile z s who d).toReal := by
    exact (div_le_iff₀ hprofile_pos).mp hterm
  linarith [neg_abs_le (F.actionWeight s who d)]

/-- Add a multiple of the prescribed mixed action at every state-player
pair. This makes all supported action weights nonnegative while preserving
both Fink obstruction identities exactly.

Residual weights are deliberately left unchanged. -/
noncomputable def repairActionWeight
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K) :
    G.NormalizedFinkSupportTangentObstructionFlow z H K where
  residualWeight := F.residualWeight
  actionWeight s who d :=
    F.actionWeight s who d +
      actionRepairScale z H K F s who *
        (G.finkProfile z s who d).toReal
  operator_balance A := by
    have hneutral : ∀ s who,
        ∑ d,
          (G.finkProfile z s who d).toReal *
            (if G.finkProfile z s who d ≠ 0 then
              G.finkContinuationGain A z s who d else 0) = 0 := by
      intro s who
      have h :=
        G.finkProfile_weighted_continuationGain_sum_eq_zero
          z A s who
      calc
        (∑ d,
          (G.finkProfile z s who d).toReal *
            (if G.finkProfile z s who d ≠ 0 then
              G.finkContinuationGain A z s who d else 0)) =
            ∑ d, (G.finkProfile z s who d).toReal *
              G.finkContinuationGain A z s who d := by
                apply Finset.sum_congr rfl
                intro d _
                by_cases hsupported :
                    G.finkProfile z s who d ≠ 0
                · rw [if_pos hsupported]
                · rw [if_neg hsupported]
                  have hzero :
                      (G.finkProfile z s who d).toReal = 0 := by
                    rw [ENNReal.toReal_eq_zero_iff]
                    exact Or.inl (not_ne_iff.mp hsupported)
                  simp [hzero]
        _ = 0 := h
    have hshift :
        (∑ s, ∑ who, ∑ d,
          actionRepairScale z H K F s who *
              (G.finkProfile z s who d).toReal *
            (if G.finkProfile z s who d ≠ 0 then
              G.finkContinuationGain A z s who d else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      apply Finset.sum_eq_zero
      intro who _
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, hneutral s who, mul_zero]
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hshift, add_zero]
    exact F.operator_balance A
  target_balance := by
    have hneutral : ∀ s who,
        ∑ d,
          (G.finkProfile z s who d).toReal *
            (if G.finkProfile z s who d ≠ 0 then
              G.finkStageGain z s who d +
                G.finkContinuationGain (H - K) z s who d else 0) = 0 := by
      intro s who
      have h :=
        G.finkProfile_weighted_stage_add_continuationGain_sum_eq_zero
          z (H - K) s who
      calc
        (∑ d,
          (G.finkProfile z s who d).toReal *
            (if G.finkProfile z s who d ≠ 0 then
              G.finkStageGain z s who d +
                G.finkContinuationGain (H - K) z s who d else 0)) =
            ∑ d, (G.finkProfile z s who d).toReal *
              (G.finkStageGain z s who d +
                G.finkContinuationGain (H - K) z s who d) := by
                apply Finset.sum_congr rfl
                intro d _
                by_cases hsupported :
                    G.finkProfile z s who d ≠ 0
                · rw [if_pos hsupported]
                · rw [if_neg hsupported]
                  have hzero :
                      (G.finkProfile z s who d).toReal = 0 := by
                    rw [ENNReal.toReal_eq_zero_iff]
                    exact Or.inl (not_ne_iff.mp hsupported)
                  simp [hzero]
        _ = 0 := h
    have hshift :
        (∑ s, ∑ who, ∑ d,
          actionRepairScale z H K F s who *
              (G.finkProfile z s who d).toReal *
            (if G.finkProfile z s who d ≠ 0 then
              G.finkStageGain z s who d +
                G.finkContinuationGain (H - K) z s who d else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      apply Finset.sum_eq_zero
      intro who _
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, hneutral s who, mul_zero]
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hshift, add_zero]
    exact F.target_balance

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
@[simp] theorem repairActionWeight_residualWeight
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (s : G.State) (who : ι) :
    (repairActionWeight z H K F).residualWeight s who =
      F.residualWeight s who := rfl

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
theorem repairActionWeight_actionWeight_nonneg
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (s : G.State) (who : ι) (d : G.Act who)
    (hsupported : G.finkProfile z s who d ≠ 0) :
    0 ≤ (repairActionWeight z H K F).actionWeight s who d :=
  actionWeight_add_profile_nonneg z H K F s who d hsupported

end NormalizedFinkSupportTangentObstructionFlow

/-- An operational, owner-pure occupation circulation extracted from a
Fink obstruction. Baseline and pure-deviation coefficients are
nonnegative; pure deviations use their actual forward kernels and consume
mass at their actual source state. -/
structure PositiveFinkActualOccupationFlow
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) where
  baselineMass : G.State → ι → ℝ
  actionMass : G.State → ∀ who : ι, G.Act who → ℝ
  baselineMass_nonneg : ∀ s who, 0 ≤ baselineMass s who
  actionMass_nonneg : ∀ s who d, 0 ≤ actionMass s who d
  player_actual_transition_balance : ∀ who (w : G.State → ℝ),
    (∑ s, baselineMass s who *
      (expect (G.finkStateKernel z s) w - w s)) +
      ∑ s, ∑ d, actionMass s who d *
        (expect (G.finkPureDeviationStateKernel z s who d) w -
          w s) = 0
  target_balance :
    ∑ s, ∑ who, ∑ d, actionMass s who d *
      (G.finkStageGain z s who d +
        G.finkContinuationGain (H - K) z s who d) = 1

namespace PositiveFinkActualOccupationFlow

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- Some player owns a strictly positive share of the operational flow's
raw Bellman charge. This is the unconditional owner extraction supplied by
target normalization. -/
theorem exists_owner_positive_bellmanCharge
    {U : ℝ} {z : G.finkDomain U}
    {H K : G.State → Payoff ι}
    (C : G.PositiveFinkActualOccupationFlow z H K) :
    ∃ who : ι, 0 <
      ∑ s, ∑ d, C.actionMass s who d *
        (G.finkStageGain z s who d +
          G.finkContinuationGain (H - K) z s who d) := by
  have hsum :
      (∑ who, ∑ s, ∑ d, C.actionMass s who d *
        (G.finkStageGain z s who d +
          G.finkContinuationGain (H - K) z s who d)) = 1 := by
    calc
      (∑ who, ∑ s, ∑ d, C.actionMass s who d *
        (G.finkStageGain z s who d +
          G.finkContinuationGain (H - K) z s who d)) =
          ∑ s, ∑ who, ∑ d, C.actionMass s who d *
            (G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d) :=
        Finset.sum_comm
      _ = 1 := C.target_balance
  by_contra hpositive
  push Not at hpositive
  have hnonpos :
      (∑ who, ∑ s, ∑ d, C.actionMass s who d *
        (G.finkStageGain z s who d +
          G.finkContinuationGain (H - K) z s who d)) ≤ 0 :=
    Finset.sum_nonpos fun who _ => hpositive who
  rw [hsum] at hnonpos
  norm_num at hnonpos

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- If the comparison continuation is harmonic for the baseline kernel,
actual-flow conservation cancels its complete continuation contribution.
The positive owner supplied above then has strictly positive
action-mass-weighted stage gain.

Without harmonicity (or the equivalent weighted baseline-drift
orthogonality), this conclusion is false: the Fink target uses `Q-P`,
whereas actual circulation telescopes `Q-δ` together with `P-δ`. -/
theorem exists_owner_positive_stageGain_of_harmonic
    {U : ℝ} {z : G.finkDomain U}
    {H K : G.State → Payoff ι}
    (C : G.PositiveFinkActualOccupationFlow z H K)
    (hharmonic : ∀ who s,
      expect (G.finkStateKernel z s)
          (fun destination => (H - K) destination who) =
        (H - K) s who) :
    ∃ who : ι, 0 <
      ∑ s, ∑ d,
        C.actionMass s who d * G.finkStageGain z s who d := by
  obtain ⟨who, hcharge⟩ :=
    C.exists_owner_positive_bellmanCharge
  let W : G.State → ℝ := fun s => (H - K) s who
  have hactual := C.player_actual_transition_balance who W
  have hcontinuation :
      (∑ s, ∑ d, C.actionMass s who d *
        G.finkContinuationGain (H - K) z s who d) = 0 := by
    have hbaseline :
        ∀ s, expect (G.finkStateKernel z s) W - W s = 0 := by
      intro s
      simpa only [W] using sub_eq_zero.mpr (hharmonic who s)
    have haction (s : G.State) (d : G.Act who) :
        G.finkContinuationGain (H - K) z s who d =
          expect (G.finkPureDeviationStateKernel z s who d) W -
            W s := by
      rw [G.finkContinuationGain_eq_expect_stateKernels]
      rw [hharmonic who s]
    have hactual' :
        (∑ s, ∑ d, C.actionMass s who d *
          (expect (G.finkPureDeviationStateKernel z s who d) W -
            W s)) = 0 := by
      simpa only [hbaseline, mul_zero, Finset.sum_const_zero,
        zero_add] using hactual
    calc
      (∑ s, ∑ d, C.actionMass s who d *
        G.finkContinuationGain (H - K) z s who d) =
          ∑ s, ∑ d, C.actionMass s who d *
            (expect (G.finkPureDeviationStateKernel z s who d) W -
              W s) := by
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro d _
        rw [haction s d]
      _ = 0 := hactual'
  have hdecompose :
      (∑ s, ∑ d, C.actionMass s who d *
        (G.finkStageGain z s who d +
          G.finkContinuationGain (H - K) z s who d)) =
        (∑ s, ∑ d,
          C.actionMass s who d * G.finkStageGain z s who d) +
          ∑ s, ∑ d, C.actionMass s who d *
            G.finkContinuationGain (H - K) z s who d := by
    simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hdecompose, hcontinuation, add_zero] at hcharge
  exact ⟨who, hcharge⟩

end PositiveFinkActualOccupationFlow

namespace NormalizedFinkSupportTangentObstructionFlow

/-- Operational mass assigned to a supported action coefficient. -/
def supportedActionMass
    {U : ℝ} {z : G.finkDomain U}
    {H K : G.State → Payoff ι}
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (s : G.State) (who : ι) (d : G.Act who) : ℝ :=
  if G.finkProfile z s who d ≠ 0 then
    F.actionWeight s who d
  else 0

/-- Total operational action outflow at one state and player. -/
def supportedActionOutflow
    {U : ℝ} {z : G.finkDomain U}
    {H K : G.State → Payoff ι}
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (s : G.State) (who : ι) : ℝ :=
  ∑ d, F.supportedActionMass s who d

/-- A stationary repair scale large enough that the repaired residual mass
dominates the complete supported-action outflow at every source. -/
noncomputable def actualOccupationRepairScale
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (π : G.FullSupportFinkStationaryWeight z)
    (who : ι) : ℝ :=
  ∑ s,
    (|F.residualWeight s who| +
      F.supportedActionOutflow s who) / π.weight s

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
theorem supportedActionMass_nonneg
    {U : ℝ} {z : G.finkDomain U}
    {H K : G.State → Payoff ι}
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (haction :
      ∀ s who d,
        G.finkProfile z s who d ≠ 0 →
          0 ≤ F.actionWeight s who d) :
    ∀ s who d, 0 ≤ F.supportedActionMass s who d := by
  intro s who d
  by_cases hsupported : G.finkProfile z s who d ≠ 0
  · simp [supportedActionMass, hsupported, haction s who d hsupported]
  · simp [supportedActionMass, hsupported]

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
theorem supportedActionOutflow_nonneg
    {U : ℝ} {z : G.finkDomain U}
    {H K : G.State → Payoff ι}
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (haction :
      ∀ s who d,
        G.finkProfile z s who d ≠ 0 →
          0 ≤ F.actionWeight s who d) :
    ∀ s who, 0 ≤ F.supportedActionOutflow s who := by
  intro s who
  exact Finset.sum_nonneg fun d _ =>
    F.supportedActionMass_nonneg haction s who d

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
theorem residual_add_actualOccupationRepair_ge_outflow
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (π : G.FullSupportFinkStationaryWeight z)
    (haction :
      ∀ s who d,
        G.finkProfile z s who d ≠ 0 →
          0 ≤ F.actionWeight s who d)
    (s : G.State) (who : ι) :
    F.supportedActionOutflow s who ≤
      F.residualWeight s who +
        actualOccupationRepairScale z H K F π who * π.weight s := by
  have hout_nonneg :=
    F.supportedActionOutflow_nonneg haction s who
  have hterm :
      (|F.residualWeight s who| +
          F.supportedActionOutflow s who) / π.weight s ≤
        actualOccupationRepairScale z H K F π who := by
    change
      (|F.residualWeight s who| +
          F.supportedActionOutflow s who) / π.weight s ≤
        ∑ t,
          (|F.residualWeight t who| +
            F.supportedActionOutflow t who) / π.weight t
    refine Finset.single_le_sum
      (f := fun t : G.State =>
        (|F.residualWeight t who| +
          F.supportedActionOutflow t who) / π.weight t)
      (s := Finset.univ) ?_ (Finset.mem_univ s)
    intro t _
    exact div_nonneg
      (add_nonneg (abs_nonneg _)
        (F.supportedActionOutflow_nonneg haction t who))
      (π.weight_pos t).le
  have hbound :
      |F.residualWeight s who| +
          F.supportedActionOutflow s who ≤
        actualOccupationRepairScale z H K F π who * π.weight s :=
    (div_le_iff₀ (π.weight_pos s)).mp hterm
  linarith [neg_abs_le (F.residualWeight s who)]

/-- On a full-support recurrent baseline, nonnegative supported action
weights lift to a genuine operational circulation.

The baseline occupation mass is
`residual + stationaryShift - supportedActionOutflow`; this is the exact
source-consumption correction absent from residual-only repair. -/
noncomputable def toPositiveFinkActualOccupationFlow
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (π : G.FullSupportFinkStationaryWeight z)
    (haction :
      ∀ s who d,
        G.finkProfile z s who d ≠ 0 →
          0 ≤ F.actionWeight s who d) :
    G.PositiveFinkActualOccupationFlow z H K where
  baselineMass s who :=
    F.residualWeight s who +
      actualOccupationRepairScale z H K F π who * π.weight s -
        F.supportedActionOutflow s who
  actionMass := F.supportedActionMass
  baselineMass_nonneg s who := by
    exact sub_nonneg.mpr
      (residual_add_actualOccupationRepair_ge_outflow
        z H K F π haction s who)
  actionMass_nonneg :=
    F.supportedActionMass_nonneg haction
  player_actual_transition_balance who w := by
    let scale := actualOccupationRepairScale z H K F π who
    have hF :=
      NormalizedFinkSupportTangentObstructionFlow.player_transition_balance
        G z H K F who w
    have hstationary := π.stationary_balance w
    have hshift :
        (∑ s, scale * π.weight s *
          (expect (G.finkStateKernel z s) w - w s)) = 0 := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, hstationary, mul_zero]
    have hperturbation :
        (∑ s, ∑ d,
          F.supportedActionMass s who d *
            (expect (G.finkPureDeviationStateKernel z s who d) w -
              expect (G.finkStateKernel z s) w)) =
          ∑ s, ∑ d,
            F.actionWeight s who d *
              (if G.finkProfile z s who d ≠ 0 then
                expect (G.finkPureDeviationStateKernel z s who d) w -
                  expect (G.finkStateKernel z s) w
              else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro d _
      by_cases hsupported : G.finkProfile z s who d ≠ 0
      · simp [supportedActionMass, hsupported]
      · simp [supportedActionMass, hsupported]
    rw [← hperturbation] at hF
    have hsource (s : G.State) :
        (∑ d,
          F.supportedActionMass s who d *
            (expect (G.finkPureDeviationStateKernel z s who d) w -
              w s)) =
          (∑ d,
            F.supportedActionMass s who d *
              (expect (G.finkPureDeviationStateKernel z s who d) w -
                expect (G.finkStateKernel z s) w)) +
            F.supportedActionOutflow s who *
              (expect (G.finkStateKernel z s) w - w s) := by
      dsimp only [supportedActionOutflow]
      rw [Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d _
      ring
    simp_rw [hsource]
    rw [Finset.sum_add_distrib]
    simp only [sub_mul, add_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [hshift]
    linarith
  target_balance := by
    have htarget := F.target_balance
    calc
      (∑ s, ∑ who, ∑ d,
        F.supportedActionMass s who d *
          (G.finkStageGain z s who d +
            G.finkContinuationGain (H - K) z s who d)) =
          ∑ s, ∑ who, ∑ d,
            F.actionWeight s who d *
              (if G.finkProfile z s who d ≠ 0 then
                G.finkStageGain z s who d +
                  G.finkContinuationGain (H - K) z s who d
              else 0) := by
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro who _
        apply Finset.sum_congr rfl
        intro d _
        by_cases hsupported : G.finkProfile z s who d ≠ 0
        · simp [supportedActionMass, hsupported]
        · simp [supportedActionMass, hsupported]
      _ = 1 := htarget

/-- Combined pointwise repair: first make every supported action
coefficient nonnegative, then add enough stationary residual mass to pay
for its actual source consumption. -/
noncomputable def repairActionAndOccupation
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K)
    (π : G.FullSupportFinkStationaryWeight z) :
    G.PositiveFinkActualOccupationFlow z H K :=
  let F' := repairActionWeight z H K F
  F'.toPositiveFinkActualOccupationFlow z H K π
    (fun s who d hsupported =>
      repairActionWeight_actionWeight_nonneg
        z H K F s who d hsupported)

end NormalizedFinkSupportTangentObstructionFlow

namespace AnalyticBellmanGerm

omit [DecidableEq G.State] in
/-- At a valid positive parameter, the raw mixing coordinate is the real
mass of the decoded action. -/
theorem rawFinkActionCoordinate_eq_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (e : Σ who : ι, G.State × G.Act who) :
    germ.rawFinkActionCoordinate t e =
      (G.finkProfile (germ.finkPointAt ht)
        e.2.1 e.1 e.2.2).toReal := by
  change
    germ.assignment t
        (BellmanVar.mix e.2.1 e.1 e.2.2) =
      (G.finkProfile (germ.finkPointAt ht)
        e.2.1 e.1 e.2.2).toReal
  rw [germ.finkProfile_finkPointAt]
  exact
    (G.bellmanDecodeProfile_apply_toReal
      (germ.solution t ht) e.2.1 e.1 e.2.2).symm

/-- The raw supported profile shift is in the kernel of every Fink balance
row at a valid positive parameter. -/
theorem sum_rawFinkActionCoordinate_mul_rawFinkObstructionBalance_eq_zero
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hsupported :
      ∀ e : Σ who : ι, G.State × G.Act who,
        supported e = true ↔
          G.finkProfile (germ.finkPointAt ht)
            e.2.1 e.1 e.2.2 ≠ 0)
    (row : FinkObstructionRow G) :
    ∑ e : Σ who : ι, G.State × G.Act who,
      germ.rawFinkActionCoordinate t e *
        germ.rawFinkObstructionBalance supported t row
          (Sum.inr e) = 0 := by
  rw [germ.rawFinkObstructionBalance_eq_finkPointAt
    supported ht hsupported]
  simpa only [germ.rawFinkActionCoordinate_eq_finkPointAt ht] using
    G.finkProfile_weighted_finkObstructionBalance_action_sum_eq_zero
      (germ.finkPointAt ht) row

omit [DecidableEq G.State] in
/-- The same raw supported profile shift has zero tangent target mass. -/
theorem sum_rawFinkActionCoordinate_mul_rawFinkObstructionMass_eq_zero
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (H K : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hsupported :
      ∀ e : Σ who : ι, G.State × G.Act who,
        supported e = true ↔
          G.finkProfile (germ.finkPointAt ht)
            e.2.1 e.1 e.2.2 ≠ 0) :
    ∑ e : Σ who : ι, G.State × G.Act who,
      germ.rawFinkActionCoordinate t e *
        germ.rawFinkObstructionMass supported H K t
          (Sum.inr e) = 0 := by
  rw [germ.rawFinkObstructionMass_eq_finkPointAt
    supported H K ht hsupported]
  simpa only [germ.rawFinkActionCoordinate_eq_finkPointAt ht] using
    G.finkProfile_weighted_finkObstructionMass_action_sum_eq_zero
      (germ.finkPointAt ht) H K

/-- Replace an unsupported action coordinate by the neutral product factor
one. On the stabilized support this is the raw prescribed probability. -/
def rawFinkSupportFactor
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (t : ℝ) (e : Σ who : ι, G.State × G.Act who) : ℝ :=
  if supported e then germ.rawFinkActionCoordinate t e else 1

/-- Product of all stabilized supported action coordinates. -/
def rawFinkSupportProduct
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (t : ℝ) : ℝ :=
  ∏ e, germ.rawFinkSupportFactor supported t e

/-- Product of every supported action coordinate except one. -/
def rawFinkSupportCofactor
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (t : ℝ) (e : Σ who : ι, G.State × G.Act who) : ℝ :=
  ∏ f ∈ Finset.univ.erase e,
    germ.rawFinkSupportFactor supported t f

/-- One analytic profile shift that simultaneously dominates every
negative signed action coefficient after multiplication by the common
support product.

The quadratic `w² + 1` avoids absolute values and sign choices:
`w² + w + 1` is strictly positive for every real `w`. -/
def rawFinkActionRepairShift
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (signed : ℝ → FinkObstructionColumn G → ℝ)
    (t : ℝ) : ℝ :=
  ∑ e, if supported e then
    (signed t (Sum.inr e) ^ 2 + 1) *
      germ.rawFinkSupportCofactor supported t e
  else 0

/-- Pole-cleared signed Fink weights after the action part has been made
operationally nonnegative. The residual part is only multiplied by the
common support product; residual/occupation repair is a later step. -/
def rawActionRepairedFinkObstructionWeight
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (signed : ℝ → FinkObstructionColumn G → ℝ) :
    ℝ → FinkObstructionColumn G → ℝ
  | t, Sum.inl residual =>
      germ.rawFinkSupportProduct supported t *
        signed t (Sum.inl residual)
  | t, Sum.inr e =>
      germ.rawFinkSupportProduct supported t *
          signed t (Sum.inr e) +
        germ.rawFinkActionRepairShift supported signed t *
          germ.rawFinkActionCoordinate t e

omit [DecidableEq G.State] in
theorem analytic_rawFinkSupportFactor
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (e : Σ who : ι, G.State × G.Act who) :
    AnalyticAt ℝ
      (fun t => germ.rawFinkSupportFactor supported t e) 0 := by
  by_cases hsupported : supported e
  · simpa only [rawFinkSupportFactor, hsupported, if_true] using
      germ.analytic_rawFinkActionCoordinate e
  · simpa [rawFinkSupportFactor, hsupported] using
      (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) 0)

omit [DecidableEq G.State] in
theorem analytic_rawFinkSupportProduct
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool) :
    AnalyticAt ℝ
      (fun t => germ.rawFinkSupportProduct supported t) 0 := by
  exact Finset.univ.analyticAt_fun_prod fun e _ =>
    germ.analytic_rawFinkSupportFactor supported e

omit [DecidableEq G.State] in
/-- On a valid parameter where the frozen support is correct, the common
support product is strictly positive. -/
theorem rawFinkSupportProduct_pos
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hsupported :
      ∀ e : Σ who : ι, G.State × G.Act who,
        supported e = true ↔
          G.finkProfile (germ.finkPointAt ht)
            e.2.1 e.1 e.2.2 ≠ 0) :
    0 < germ.rawFinkSupportProduct supported t := by
  apply Finset.prod_pos
  intro e _
  by_cases he : supported e = true
  · have hprofile :
        G.finkProfile (germ.finkPointAt ht)
          e.2.1 e.1 e.2.2 ≠ 0 :=
      (hsupported e).1 he
    simp only [rawFinkSupportFactor, he, if_true]
    rw [germ.rawFinkActionCoordinate_eq_finkPointAt ht]
    exact ENNReal.toReal_pos hprofile (PMF.apply_ne_top _ _)
  · have hfalse : supported e = false :=
      Bool.eq_false_of_not_eq_true he
    simp [rawFinkSupportFactor, hfalse]

theorem analytic_rawFinkSupportCofactor
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (e : Σ who : ι, G.State × G.Act who) :
    AnalyticAt ℝ
      (fun t => germ.rawFinkSupportCofactor supported t e) 0 := by
  exact (Finset.univ.erase e).analyticAt_fun_prod fun f _ =>
    germ.analytic_rawFinkSupportFactor supported f

theorem analytic_rawFinkActionRepairShift
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (signed : ℝ → FinkObstructionColumn G → ℝ)
    (hsigned : AnalyticAt ℝ signed 0) :
    AnalyticAt ℝ
      (fun t => germ.rawFinkActionRepairShift supported signed t) 0 := by
  apply Finset.univ.analyticAt_fun_sum
  intro e _
  by_cases hsupported : supported e = true
  · simp only [hsupported, if_true]
    exact
      (((analyticAt_pi_iff.mp hsigned (Sum.inr e)).pow 2).add
        analyticAt_const).mul
        (germ.analytic_rawFinkSupportCofactor supported e)
  · have hfalse : supported e = false :=
      Bool.eq_false_of_not_eq_true hsupported
    simpa [hfalse] using
      (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) 0)

theorem analytic_rawActionRepairedFinkObstructionWeight
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (signed : ℝ → FinkObstructionColumn G → ℝ)
    (hsigned : AnalyticAt ℝ signed 0) :
    AnalyticAt ℝ
      (germ.rawActionRepairedFinkObstructionWeight supported signed) 0 := by
  rw [analyticAt_pi_iff]
  intro column
  cases column with
  | inl residual =>
      exact
        (germ.analytic_rawFinkSupportProduct supported).mul
          (analyticAt_pi_iff.mp hsigned (Sum.inl residual))
  | inr e =>
      exact
        ((germ.analytic_rawFinkSupportProduct supported).mul
            (analyticAt_pi_iff.mp hsigned (Sum.inr e))).add
          ((germ.analytic_rawFinkActionRepairShift
              supported signed hsigned).mul
            (germ.analytic_rawFinkActionCoordinate e))

/-- Every stabilized supported action coefficient is strictly positive
after the analytic repair, independently of the original signed
orientation. -/
theorem rawActionRepairedFinkObstructionWeight_action_pos
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (signed : ℝ → FinkObstructionColumn G → ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hsupported :
      ∀ e : Σ who : ι, G.State × G.Act who,
        supported e = true ↔
          G.finkProfile (germ.finkPointAt ht)
            e.2.1 e.1 e.2.2 ≠ 0)
    (e : Σ who : ι, G.State × G.Act who)
    (he : supported e = true) :
    0 <
      germ.rawActionRepairedFinkObstructionWeight
        supported signed t (Sum.inr e) := by
  let probability := germ.rawFinkActionCoordinate t e
  let product := germ.rawFinkSupportProduct supported t
  let cofactor := germ.rawFinkSupportCofactor supported t e
  let weight := signed t (Sum.inr e)
  let shift := germ.rawFinkActionRepairShift supported signed t
  have hprofile :
      G.finkProfile (germ.finkPointAt ht)
        e.2.1 e.1 e.2.2 ≠ 0 :=
    (hsupported e).1 he
  have hprobability :
      0 < probability := by
    dsimp only [probability]
    rw [germ.rawFinkActionCoordinate_eq_finkPointAt ht]
    exact ENNReal.toReal_pos hprofile (PMF.apply_ne_top _ _)
  have hfactor_nonneg :
      ∀ f : Σ who : ι, G.State × G.Act who,
        0 ≤ germ.rawFinkSupportFactor supported t f := by
    intro f
    by_cases hf : supported f = true
    · simp only [rawFinkSupportFactor, hf, if_true]
      rw [germ.rawFinkActionCoordinate_eq_finkPointAt ht]
      exact ENNReal.toReal_nonneg
    · have hfalse : supported f = false :=
        Bool.eq_false_of_not_eq_true hf
      simp [rawFinkSupportFactor, hfalse]
  have hfactor_pos :
      ∀ f : Σ who : ι, G.State × G.Act who,
        0 < germ.rawFinkSupportFactor supported t f := by
    intro f
    by_cases hf : supported f = true
    · have hprofile_f :
          G.finkProfile (germ.finkPointAt ht)
            f.2.1 f.1 f.2.2 ≠ 0 :=
        (hsupported f).1 hf
      simp only [rawFinkSupportFactor, hf, if_true]
      rw [germ.rawFinkActionCoordinate_eq_finkPointAt ht]
      exact ENNReal.toReal_pos hprofile_f (PMF.apply_ne_top _ _)
    · have hfalse : supported f = false :=
        Bool.eq_false_of_not_eq_true hf
      simp [rawFinkSupportFactor, hfalse]
  have hproduct_pos : 0 < product := by
    dsimp only [product, rawFinkSupportProduct]
    exact Finset.prod_pos fun f _ => hfactor_pos f
  have hcofactor_nonneg : 0 ≤ cofactor := by
    dsimp only [cofactor, rawFinkSupportCofactor]
    exact Finset.prod_nonneg fun f _ => hfactor_nonneg f
  have hfactorization :
      probability * cofactor = product := by
    dsimp only [probability, cofactor, product,
      rawFinkSupportProduct, rawFinkSupportCofactor]
    have h :=
      Finset.mul_prod_erase
        (s := (Finset.univ :
          Finset (Σ who : ι, G.State × G.Act who)))
        (f := fun f =>
          germ.rawFinkSupportFactor supported t f)
        (a := e) (Finset.mem_univ e)
    simpa only [rawFinkSupportFactor, he, if_true] using h
  have hterm_nonneg :
      ∀ f : Σ who : ι, G.State × G.Act who,
        0 ≤
          if supported f then
            (signed t (Sum.inr f) ^ 2 + 1) *
              germ.rawFinkSupportCofactor supported t f
          else 0 := by
    intro f
    by_cases hf : supported f = true
    · simp only [hf, if_true]
      exact mul_nonneg (by positivity)
        (Finset.prod_nonneg fun g _ => hfactor_nonneg g)
    · have hfalse : supported f = false :=
        Bool.eq_false_of_not_eq_true hf
      simp [hfalse]
  have hterm_le :
      (weight ^ 2 + 1) * cofactor ≤ shift := by
    dsimp only [shift, rawFinkActionRepairShift]
    have hsingle :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun f :
          Σ who : ι, G.State × G.Act who =>
          if supported f then
            (signed t (Sum.inr f) ^ 2 + 1) *
              germ.rawFinkSupportCofactor supported t f
          else 0)
        (fun f _ => hterm_nonneg f)
        (Finset.mem_univ e)
    simpa only [weight, cofactor, he, if_true] using hsingle
  have hshift_bound :
      product * (weight ^ 2 + 1) ≤
        shift * probability := by
    have hmul :=
      mul_le_mul_of_nonneg_right hterm_le hprobability.le
    calc
      product * (weight ^ 2 + 1) =
          ((weight ^ 2 + 1) * cofactor) * probability := by
            rw [← hfactorization]
            ring
      _ ≤ shift * probability := hmul
  have hquadratic : 0 < weight ^ 2 + weight + 1 := by
    nlinarith [sq_nonneg (weight + 1 / 2)]
  change 0 < product * weight + shift * probability
  calc
    0 < product * (weight ^ 2 + weight + 1) :=
      mul_pos hproduct_pos hquadratic
    _ = product * weight + product * (weight ^ 2 + 1) := by ring
    _ ≤ product * weight + shift * probability := by
      linarith

/-- The analytic action repair preserves the raw homogeneous Fink balance
at every valid parameter where `supported` is the decoded support. -/
theorem rawFinkObstructionBalance_mulVec_rawActionRepaired_eq_zero
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (signed : ℝ → FinkObstructionColumn G → ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hsupported :
      ∀ e : Σ who : ι, G.State × G.Act who,
        supported e = true ↔
          G.finkProfile (germ.finkPointAt ht)
            e.2.1 e.1 e.2.2 ≠ 0)
    (hbalance :
      Matrix.mulVec
        (germ.rawFinkObstructionBalance supported t)
        (signed t) = 0) :
    Matrix.mulVec
        (germ.rawFinkObstructionBalance supported t)
        (germ.rawActionRepairedFinkObstructionWeight
          supported signed t) = 0 := by
  funext row
  let product := germ.rawFinkSupportProduct supported t
  let shift := germ.rawFinkActionRepairShift supported signed t
  have hrow :
      Matrix.mulVec
          (germ.rawFinkObstructionBalance supported t)
          (signed t) row = 0 := by
    simpa only [Pi.zero_apply] using congrFun hbalance row
  have hneutral :=
    germ.sum_rawFinkActionCoordinate_mul_rawFinkObstructionBalance_eq_zero
      supported ht hsupported row
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    rawActionRepairedFinkObstructionWeight] at hrow ⊢
  have hresidual :
      (∑ residual,
        germ.rawFinkObstructionBalance supported t row
            (Sum.inl residual) *
          (product * signed t (Sum.inl residual))) =
        product *
          ∑ residual,
            germ.rawFinkObstructionBalance supported t row
                (Sum.inl residual) *
              signed t (Sum.inl residual) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro residual _
    ring
  have haction :
      (∑ e,
        germ.rawFinkObstructionBalance supported t row (Sum.inr e) *
          (product * signed t (Sum.inr e) +
            shift * germ.rawFinkActionCoordinate t e)) =
        product *
            ∑ e,
              germ.rawFinkObstructionBalance supported t row (Sum.inr e) *
                signed t (Sum.inr e) +
          shift *
            ∑ e,
              germ.rawFinkActionCoordinate t e *
                germ.rawFinkObstructionBalance supported t row
                  (Sum.inr e) := by
    calc
      (∑ e,
        germ.rawFinkObstructionBalance supported t row (Sum.inr e) *
          (product * signed t (Sum.inr e) +
            shift * germ.rawFinkActionCoordinate t e)) =
          ∑ e,
            (product *
                (germ.rawFinkObstructionBalance supported t row
                    (Sum.inr e) * signed t (Sum.inr e)) +
              shift *
                (germ.rawFinkActionCoordinate t e *
                  germ.rawFinkObstructionBalance supported t row
                    (Sum.inr e))) := by
              apply Finset.sum_congr rfl
              intro e _
              ring
      _ =
          (∑ e,
            product *
              (germ.rawFinkObstructionBalance supported t row
                  (Sum.inr e) * signed t (Sum.inr e))) +
            ∑ e,
              shift *
                (germ.rawFinkActionCoordinate t e *
                  germ.rawFinkObstructionBalance supported t row
                    (Sum.inr e)) := Finset.sum_add_distrib
      _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hresidual, haction]
  rw [hneutral, mul_zero, add_zero]
  rw [← mul_add, hrow, mul_zero]
  simp

/-- The action repair changes the raw target only by the common positive
support product. The added profile direction has exactly zero target
mass. -/
theorem sum_rawFinkObstructionMass_mul_rawActionRepaired_eq
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (H K : G.State → Payoff ι)
    (signed : ℝ → FinkObstructionColumn G → ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hsupported :
      ∀ e : Σ who : ι, G.State × G.Act who,
        supported e = true ↔
          G.finkProfile (germ.finkPointAt ht)
            e.2.1 e.1 e.2.2 ≠ 0) :
    (∑ column,
      germ.rawFinkObstructionMass supported H K t column *
        germ.rawActionRepairedFinkObstructionWeight
          supported signed t column) =
      germ.rawFinkSupportProduct supported t *
        ∑ column,
          germ.rawFinkObstructionMass supported H K t column *
            signed t column := by
  let product := germ.rawFinkSupportProduct supported t
  let shift := germ.rawFinkActionRepairShift supported signed t
  have hneutral :=
    germ.sum_rawFinkActionCoordinate_mul_rawFinkObstructionMass_eq_zero
      supported H K ht hsupported
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [rawActionRepairedFinkObstructionWeight]
  have hresidual :
      (∑ residual,
        germ.rawFinkObstructionMass supported H K t
            (Sum.inl residual) *
          (product * signed t (Sum.inl residual))) =
        product *
          ∑ residual,
            germ.rawFinkObstructionMass supported H K t
                (Sum.inl residual) *
              signed t (Sum.inl residual) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro residual _
    ring
  have haction :
      (∑ e,
        germ.rawFinkObstructionMass supported H K t (Sum.inr e) *
          (product * signed t (Sum.inr e) +
            shift * germ.rawFinkActionCoordinate t e)) =
        product *
            ∑ e,
              germ.rawFinkObstructionMass supported H K t (Sum.inr e) *
                signed t (Sum.inr e) +
          shift *
            ∑ e,
              germ.rawFinkActionCoordinate t e *
                germ.rawFinkObstructionMass supported H K t
                  (Sum.inr e) := by
    calc
      (∑ e,
        germ.rawFinkObstructionMass supported H K t (Sum.inr e) *
          (product * signed t (Sum.inr e) +
            shift * germ.rawFinkActionCoordinate t e)) =
          ∑ e,
            (product *
                (germ.rawFinkObstructionMass supported H K t
                    (Sum.inr e) * signed t (Sum.inr e)) +
              shift *
                (germ.rawFinkActionCoordinate t e *
                  germ.rawFinkObstructionMass supported H K t
                    (Sum.inr e))) := by
              apply Finset.sum_congr rfl
              intro e _
              ring
      _ =
          (∑ e,
            product *
              (germ.rawFinkObstructionMass supported H K t
                  (Sum.inr e) * signed t (Sum.inr e))) +
            ∑ e,
              shift *
                (germ.rawFinkActionCoordinate t e *
                  germ.rawFinkObstructionMass supported H K t
                    (Sum.inr e)) := Finset.sum_add_distrib
      _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hresidual, haction, hneutral, mul_zero, add_zero]
  change
    product *
        (∑ residual,
            germ.rawFinkObstructionMass supported H K t
                (Sum.inl residual) *
              signed t (Sum.inl residual)) +
      product *
        (∑ e,
            germ.rawFinkObstructionMass supported H K t
                (Sum.inr e) *
              signed t (Sum.inr e)) =
    product *
      ((∑ residual,
          germ.rawFinkObstructionMass supported H K t
              (Sum.inl residual) *
            signed t (Sum.inl residual)) +
        ∑ e,
          germ.rawFinkObstructionMass supported H K t
              (Sum.inr e) *
            signed t (Sum.inr e))
  ring

/-- An eventual analytic signed Fink obstruction admits one fixed analytic
action repair.

The repaired coefficients preserve the exact raw homogeneous balance. Their
target is the original positive monomial multiplied by the strictly positive
support product, and every action in the stabilized support receives a
strictly positive coefficient. Residual coefficients remain signed; repairing
them into an occupation flow is a separate construction. -/
theorem exists_analytic_actionRepaired_eventual_finkObstructionFlow
    (germ : G.AnalyticBellmanGerm)
    (H K : G.State → Payoff ι)
    (hflow :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          Nonempty
            (G.NormalizedFinkSupportTangentObstructionFlow
              (germ.finkPointAt ht) H K)) :
    ∃ (supported :
          (Σ who : ι, G.State × G.Act who) → Bool)
        (poleOrder : ℕ)
        (repaired : ℝ → FinkObstructionColumn G → ℝ),
      AnalyticAt ℝ repaired 0 ∧
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            (∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
              ∀ e : Σ who : ι, G.State × G.Act who,
                supported e = true ↔
                  G.finkProfile (germ.finkPointAt ht)
                    e.2.1 e.1 e.2.2 ≠ 0) ∧
            Matrix.mulVec
                (germ.rawFinkObstructionBalance supported t)
                (repaired t) = 0 ∧
            (∑ column,
                germ.rawFinkObstructionMass supported H K t column *
                  repaired t column) =
              germ.rawFinkSupportProduct supported t *
                t ^ poleOrder ∧
            (∀ e : Σ who : ι, G.State × G.Act who,
              supported e = true →
                0 < repaired t (Sum.inr e)) ∧
            0 <
              germ.rawFinkSupportProduct supported t *
                t ^ poleOrder := by
  classical
  obtain ⟨supported, poleOrder, signed, hsigned, hsignedFlow⟩ :=
    germ.exists_analytic_scaled_signed_eventual_finkObstructionFlow_withSupport
      H K hflow
  let repaired :=
    germ.rawActionRepairedFinkObstructionWeight supported signed
  have hrepaired : AnalyticAt ℝ repaired 0 := by
    exact
      germ.analytic_rawActionRepairedFinkObstructionWeight
        supported signed hsigned
  refine ⟨supported, poleOrder, repaired, hrepaired, ?_⟩
  filter_upwards [hsignedFlow] with t ht
  have hvalid : t ∈ Ioo (0 : ℝ) germ.radius := ht.1
  have hsupport :
      ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
        ∀ e : Σ who : ι, G.State × G.Act who,
          supported e = true ↔
            G.finkProfile (germ.finkPointAt ht)
              e.2.1 e.1 e.2.2 ≠ 0 :=
    ht.2.1
  have hbalance :
      Matrix.mulVec
          (germ.rawFinkObstructionBalance supported t)
          (repaired t) = 0 := by
    exact
      germ.rawFinkObstructionBalance_mulVec_rawActionRepaired_eq_zero
        supported signed hvalid (hsupport hvalid) ht.2.2.1
  have htarget :
      (∑ column,
          germ.rawFinkObstructionMass supported H K t column *
            repaired t column) =
        germ.rawFinkSupportProduct supported t *
          t ^ poleOrder := by
    rw [germ.sum_rawFinkObstructionMass_mul_rawActionRepaired_eq
      supported H K signed hvalid (hsupport hvalid)]
    rw [ht.2.2.2]
  have haction :
      ∀ e : Σ who : ι, G.State × G.Act who,
        supported e = true →
          0 < repaired t (Sum.inr e) := by
    intro e he
    exact
      germ.rawActionRepairedFinkObstructionWeight_action_pos
        supported signed hvalid (hsupport hvalid) e he
  have htargetPos :
      0 <
        germ.rawFinkSupportProduct supported t *
          t ^ poleOrder :=
    mul_pos
      (germ.rawFinkSupportProduct_pos
        supported hvalid (hsupport hvalid))
      (pow_pos hvalid.1 poleOrder)
  exact
    ⟨hvalid, hsupport, hbalance, htarget, haction, htargetPos⟩

end AnalyticBellmanGerm

end StochasticGame
end GameTheory
