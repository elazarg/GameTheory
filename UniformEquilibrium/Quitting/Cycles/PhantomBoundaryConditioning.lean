/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanQuitEndpointLimit

/-!
# Conditioning a positive-survival quitting tail on eventual absorption

A bounded exact quitting tail with positive probability of never absorbing
may carry a nonzero phantom boundary.  Conditioning the tail on eventual
absorption removes that boundary without losing chronology.

The remaining eventual-absorption probability is the correct projective
scale.  Unlike the ratio of two consecutive one-stage absorption masses, its
successive ratio is automatically in the unit interval.  The conditioned
value satisfies an exact affine recurrence between consecutive conditioned
states: its absorbing coefficient is the current one-stage absorption divided
by remaining eventual absorption, and its continuation coefficient is the
complementary surviving share.

This is an accounting theorem, not a strategic compiler.  Conditioning need
not preserve the punishment floor.  The last estimate records the precise
support gate: an active owner's conditioned state is close to its singleton
payoff when its opponent-absorption mass is small relative to the remaining
eventual-absorption scale.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Probability of eventual absorption in the root tail starting at `time`. -/
def quittingTailEventualAbsorption
    (roots : ℕ → ι → PMF Bool) (time : ℕ) : ℝ :=
  1 - quittingJointSurvivalLimit roots time

/-- The annotation conditioned on eventual absorption, with the surviving
phantom boundary removed before normalization. -/
def quittingTailConditionedValue
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (time : ℕ) : Payoff ι :=
  fun who ↦
    (value time who -
      quittingJointSurvivalLimit roots time * boundary who) /
        quittingTailEventualAbsorption roots time

/-- Current one-stage absorption as a share of all eventual absorption still
available in the tail. -/
def quittingTailConditionedAbsorptionWeight
    (roots : ℕ → ι → PMF Bool) (time : ℕ) : ℝ :=
  quittingRootAbsorptionMass (roots time) /
    quittingTailEventualAbsorption roots time

/-- Surviving eventual-absorption mass transported to the next conditioned
state. -/
def quittingTailConditionedContinuationWeight
    (roots : ℕ → ι → PMF Bool) (time : ℕ) : ℝ :=
  quittingStationaryContinueMass (roots time) *
      quittingTailEventualAbsorption roots (time + 1) /
    quittingTailEventualAbsorption roots time

omit [DecidableEq ι] in
/-- The joint survival limit splits at its first root. -/
theorem quittingJointSurvivalLimit_eq_continue_mul_succ
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    quittingJointSurvivalLimit roots time =
      quittingStationaryContinueMass (roots time) *
        quittingJointSurvivalLimit roots (time + 1) := by
  let jointContinue := quittingStationaryContinueMass (roots time)
  have hleft : Tendsto
      (fun fuel ↦ quittingJointSurvivalWeight roots time (fuel + 1))
      atTop (nhds (quittingJointSurvivalLimit roots time)) := by
    simpa [Function.comp_def] using
      (tendsto_quittingJointSurvivalLimit roots time).comp
        (tendsto_add_atTop_nat 1)
  have hright : Tendsto
      (fun fuel ↦ jointContinue *
        quittingJointSurvivalWeight roots (time + 1) fuel)
      atTop
      (nhds (jointContinue * quittingJointSurvivalLimit roots (time + 1))) :=
    tendsto_const_nhds.mul
      (tendsto_quittingJointSurvivalLimit roots (time + 1))
  have heq : (fun fuel ↦ quittingJointSurvivalWeight roots time (fuel + 1)) =
      fun fuel ↦ jointContinue *
        quittingJointSurvivalWeight roots (time + 1) fuel := by
    funext fuel
    rw [show fuel + 1 = 1 + fuel by omega,
      quittingJointSurvivalWeight_add]
    simp [jointContinue, quittingJointSurvivalWeight,
      quittingFiniteContinueWeight]
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

omit [DecidableEq ι] in
/-- Remaining eventual absorption obeys the exact first-stage decomposition. -/
theorem quittingTailEventualAbsorption_eq_absorption_add_continue_mul_succ
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    quittingTailEventualAbsorption roots time =
      quittingRootAbsorptionMass (roots time) +
        quittingStationaryContinueMass (roots time) *
          quittingTailEventualAbsorption roots (time + 1) := by
  rw [quittingTailEventualAbsorption,
    quittingJointSurvivalLimit_eq_continue_mul_succ]
  unfold quittingRootAbsorptionMass quittingTailEventualAbsorption
  ring

omit [DecidableEq ι] in
/-- The conditioned absorption and continuation coefficients sum to one. -/
theorem quittingTailConditionedWeights_add
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailConditionedAbsorptionWeight roots time +
        quittingTailConditionedContinuationWeight roots time = 1 := by
  unfold quittingTailConditionedAbsorptionWeight
    quittingTailConditionedContinuationWeight
  rw [← add_div,
    ← quittingTailEventualAbsorption_eq_absorption_add_continue_mul_succ]
  exact div_self hpositive.ne'

omit [DecidableEq ι] in
/-- The conditioned absorption coefficient is nonnegative. -/
theorem quittingTailConditionedAbsorptionWeight_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    0 ≤ quittingTailConditionedAbsorptionWeight roots time := by
  exact div_nonneg
    (sub_nonneg.mpr (quittingStationaryContinueMass_le_one (roots time)))
    hpositive.le

omit [DecidableEq ι] in
/-- The conditioned continuation coefficient is nonnegative. -/
theorem quittingTailConditionedContinuationWeight_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hnext : 0 ≤ quittingTailEventualAbsorption roots (time + 1))
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    0 ≤ quittingTailConditionedContinuationWeight roots time := by
  unfold quittingTailConditionedContinuationWeight
  exact div_nonneg
    (mul_nonneg (quittingStationaryContinueMass_nonneg _) hnext)
    hpositive.le

omit [DecidableEq ι] in
/-- Both conditioned coefficients lie in the unit interval. -/
theorem quittingTailConditionedWeights_mem_unitInterval
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hnext : 0 ≤ quittingTailEventualAbsorption roots (time + 1))
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailConditionedAbsorptionWeight roots time ∈ Set.Icc 0 1 ∧
      quittingTailConditionedContinuationWeight roots time ∈ Set.Icc 0 1 := by
  have habs := quittingTailConditionedAbsorptionWeight_nonneg
    roots time hpositive
  have hcont := quittingTailConditionedContinuationWeight_nonneg
    roots time hnext hpositive
  have hsum := quittingTailConditionedWeights_add roots time hpositive
  exact ⟨⟨habs, by linarith⟩, ⟨hcont, by linarith⟩⟩

/-- One-stage absorbing delivery conditional on absorption at that stage. -/
def quittingRootConditionalAbsorbingDelivery
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) : Payoff ι :=
  fun who ↦ quittingRootAbsorbingContribution reward root who /
    quittingRootAbsorptionMass root

omit [DecidableEq ι] in
/-- **Exact conditioned chronology.**  A live Bellman step becomes an affine
step between consecutive conditioned values.  Its two coefficients are the
conditioned absorption and continuation weights and add to one. -/
theorem quittingTailConditionedValue_step
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (time : ℕ)
    (habsorption : 0 < quittingRootAbsorptionMass (roots time))
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1)) :
    quittingTailConditionedValue roots value boundary time =
      fun who ↦
        quittingTailConditionedAbsorptionWeight roots time *
            quittingRootConditionalAbsorbingDelivery reward (roots time) who +
          quittingTailConditionedContinuationWeight roots time *
            quittingTailConditionedValue roots value boundary
              (time + 1) who := by
  funext who
  have hstep := congrFun (hpolicy time) who
  rw [quittingRootSuccessorPayoff_apply_eq_affine] at hstep
  have hsurvival :=
    quittingJointSurvivalLimit_eq_continue_mul_succ roots time
  unfold quittingTailConditionedValue
    quittingTailConditionedAbsorptionWeight
    quittingTailConditionedContinuationWeight
    quittingRootConditionalAbsorbingDelivery
  rw [hstep, hsurvival]
  field_simp [habsorption.ne', hcurrent.ne', hnext.ne']
  ring

omit [DecidableEq ι] in
/-- **State-matched projective increment.**  After conditioning away the
phantom boundary, the displacement between two consecutive states is the
current conditioned absorption weight times the displacement from the next
state to the current conditional absorbing delivery.  Thus the same
chronology, rather than merely a collection of tangent directions, survives
the normalization. -/
theorem quittingTailConditionedValue_sub_succ
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (time : ℕ)
    (habsorption : 0 < quittingRootAbsorptionMass (roots time))
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1)) :
    quittingTailConditionedValue roots value boundary time -
        quittingTailConditionedValue roots value boundary (time + 1) =
      fun who ↦
        quittingTailConditionedAbsorptionWeight roots time *
          (quittingRootConditionalAbsorbingDelivery reward (roots time) who -
            quittingTailConditionedValue roots value boundary
              (time + 1) who) := by
  funext who
  have hstep := congrFun
    (quittingTailConditionedValue_step roots value boundary hpolicy time
      habsorption hcurrent hnext) who
  have hweights := quittingTailConditionedWeights_add roots time hcurrent
  have hcontinuation :
      quittingTailConditionedContinuationWeight roots time =
        1 - quittingTailConditionedAbsorptionWeight roots time := by
    linarith
  change quittingTailConditionedValue roots value boundary time who -
      quittingTailConditionedValue roots value boundary (time + 1) who = _
  rw [hstep, hcontinuation]
  ring

omit [DecidableEq ι] in
/-- The phantom-boundary identity identifies the conditioned annotation with
the actual terminal payoff divided by eventual-absorption probability. -/
theorem quittingTailConditionedValue_eq_terminalValue_div
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hboundary : ∀ who,
      Tendsto (fun time ↦ value time who) atTop (nhds (boundary who)))
    (time : ℕ) :
    quittingTailConditionedValue roots value boundary time =
      fun who ↦
        quittingRootSequenceTerminalValue reward roots who time /
          quittingTailEventualAbsorption roots time := by
  funext who
  have hdecomposition := congrFun
    (quittingValuePath_eq_terminalValue_add_survivalLimit_mul
      reward roots value hpolicy boundary hM hreward hboundary time) who
  unfold quittingTailConditionedValue
  rw [hdecomposition]
  ring

omit [DecidableEq ι] in
/-- Conditioned values remain in the original reward box. -/
theorem abs_quittingTailConditionedValue_le
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hboundary : ∀ who,
      Tendsto (fun time ↦ value time who) atTop (nhds (boundary who)))
    (time : ℕ) (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (who : ι) :
    |quittingTailConditionedValue roots value boundary time who| ≤ M := by
  rw [quittingTailConditionedValue_eq_terminalValue_div
    roots value boundary hpolicy hM hreward hboundary time]
  rw [abs_div, abs_of_pos hpositive]
  exact (div_le_iff₀ hpositive).2 <| by
    simpa [quittingTailEventualAbsorption] using
      abs_quittingRootSequenceTerminalValue_le_one_sub_survivalLimit
        reward roots who time hreward

/-- **Active support gate after conditioning.**  If the boundary coordinate
is the owner's singleton payoff, exact mixing bounds the conditioned owner's
pinning error by opponent absorption divided by remaining eventual
absorption.  This is the scale ratio that a projective strategic compiler
must make small. -/
theorem abs_quittingTailConditionedValue_sub_singleton_le
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {M : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (time : ℕ) (owner : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (hquit : 0 < (roots time owner true).toReal)
    (hpin : boundary owner =
      reward (quittingSingletonTerminal owner) owner) :
    |quittingTailConditionedValue roots value boundary time owner -
        reward (quittingSingletonTerminal owner) owner| ≤
      (2 * M * quittingRootOpponentAbsorptionMass (roots time) owner) /
        quittingTailEventualAbsorption roots time := by
  have hcurrent : value time owner =
      quittingRootQuitPayoff reward (value (time + 1)) (roots time) owner := by
    rw [congrFun (hpolicy time) owner]
    have hgapNonneg : 0 ≤ quittingRootEndpointDifference reward
        (value (time + 1)) (roots time) owner :=
      nonneg_of_mul_nonneg_right (by simpa using (hnash time owner).2) hquit
    have hcontinueNonneg : 0 ≤ (roots time owner false).toReal :=
      ENNReal.toReal_nonneg
    have hproduct : (roots time owner false).toReal *
        quittingRootEndpointDifference reward
          (value (time + 1)) (roots time) owner = 0 := by
      apply le_antisymm
      · simpa using (hnash time owner).1
      · exact mul_nonneg hcontinueNonneg hgapNonneg
    have hsum := quittingRoot_continueProbability_add_quitProbability
      (roots time) owner
    have hquitProbability : (roots time owner true).toReal =
        1 - (roots time owner false).toReal := by
      linarith
    rw [quittingRootSuccessorPayoff_eq_endpointMix]
    rw [hquitProbability]
    unfold quittingRootEndpointDifference at hproduct
    nlinarith
  have hendpoint :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (value (time + 1)) (roots time) owner M hreward
  unfold quittingTailConditionedValue
  rw [hpin, hcurrent]
  have hsurvival : quittingJointSurvivalLimit roots time =
      1 - quittingTailEventualAbsorption roots time := by
    unfold quittingTailEventualAbsorption
    ring
  rw [hsurvival]
  have halgebra :
      (quittingRootQuitPayoff reward (value (time + 1)) (roots time) owner -
            (1 - quittingTailEventualAbsorption roots time) *
              reward (quittingSingletonTerminal owner) owner) /
          quittingTailEventualAbsorption roots time -
          reward (quittingSingletonTerminal owner) owner =
        (quittingRootQuitPayoff reward (value (time + 1)) (roots time) owner -
          reward (quittingSingletonTerminal owner) owner) /
            quittingTailEventualAbsorption roots time := by
    field_simp [hpositive.ne']
    ring
  rw [halgebra, abs_div, abs_of_pos hpositive]
  exact div_le_div_of_nonneg_right hendpoint hpositive.le

/-- The active-support gate is controlled by the conditioned one-stage
absorption weight itself.  Consequently the diffuse-clock branch, in which
that weight tends to zero, pins every persistently active owner to its
singleton face after conditioning. -/
theorem abs_quittingTailConditionedValue_sub_singleton_le_weight
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (time : ℕ) (owner : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (hquit : 0 < (roots time owner true).toReal)
    (hpin : boundary owner =
      reward (quittingSingletonTerminal owner) owner) :
    |quittingTailConditionedValue roots value boundary time owner -
        reward (quittingSingletonTerminal owner) owner| ≤
      2 * M * quittingTailConditionedAbsorptionWeight roots time := by
  have hgate := abs_quittingTailConditionedValue_sub_singleton_le
    roots value boundary hpolicy hnash hreward time owner hpositive hquit hpin
  apply hgate.trans
  unfold quittingTailConditionedAbsorptionWeight
  calc
    2 * M * quittingRootOpponentAbsorptionMass (roots time) owner /
        quittingTailEventualAbsorption roots time ≤
      (2 * M * quittingRootAbsorptionMass (roots time)) /
        quittingTailEventualAbsorption roots time :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (quittingRootOpponentAbsorptionMass_le_absorptionMass
            (roots time) owner)
          (mul_nonneg (by norm_num) hM))
        hpositive.le
    _ = 2 * M *
        (quittingRootAbsorptionMass (roots time) /
          quittingTailEventualAbsorption roots time) := by ring

end GameTheory
