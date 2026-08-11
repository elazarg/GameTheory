/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.HazardScaledResidualCompiler
import UniformEquilibrium.Quitting.Paths.JointSurvivalSelection

/-!
# Joint-policy and deleted-strategy residual compiler

An approximately evaluated infinite product path has two different clocks.
Policy-evaluation error is transported by the joint all-Continue mass, while
a player's refusal incentive is transported by that player's deleted
(opponent-only) Continue mass.

This module keeps the clocks separate.  A one-step policy defect bounded by
`policyCoefficient * joint absorption` changes the selected terminal value
by at most `policyCoefficient`.  A refusal defect bounded by
`refusalCoefficient * opponent absorption` changes the unilateral cap by at
most `refusalCoefficient`.  A uniform immediate-Quit defect is paid once as
well.  Thus the three coefficients add, with no calendar-time summability
assumption.

The result is suited to diffuse product purification.  Quadratic collision
error is of the form `O(mesh) * joint absorption`; exact conditioned
complementarity is expected to leave a refusal error of the form
`O(mesh) * opponent absorption`.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Finite stability of an approximately evaluated policy path.  Joint
absorption charges the local defect and the final joint survival weight
transports the unresolved boundary discrepancy. -/
theorem abs_value_sub_rootSequenceTerminalValue_le_jointPolicyCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    {policyCoefficient bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hpolicyError : ∀ time who,
      |value time who -
          quittingRootSuccessorPayoff reward (value (time + 1))
            (roots time) who| ≤
        policyCoefficient * quittingRootAbsorptionMass (roots time)) :
    ∀ start fuel who,
      |value start who -
          quittingRootSequenceTerminalValue reward roots who start| ≤
        policyCoefficient *
            (1 - quittingJointSurvivalWeight roots start fuel) +
          quittingJointSurvivalWeight roots start fuel * (2 * bound) := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro who
      simp only [quittingJointSurvivalWeight,
        quittingFiniteContinueWeight, sub_self, mul_zero, one_mul]
      have hvalue := hvalueBound start who
      have hterminal := abs_quittingTerminalPayoff_le reward
        (quittingRootSequenceProfile reward roots start) who
        hbound hreward
      change |quittingRootSequenceTerminalValue reward roots who start| ≤
        bound at hterminal
      exact (abs_sub _ _).trans (by linarith)
  | succ fuel ih =>
      intro who
      let terminal : ℕ → ℝ := fun time ↦
        quittingRootSequenceTerminalValue reward roots who time
      let difference : ℕ → ℝ := fun time ↦ value time who - terminal time
      let continueMass := quittingStationaryContinueMass (roots start)
      let tailSurvival :=
        quittingJointSurvivalWeight roots (start + 1) fuel
      have hmass0 : 0 ≤ continueMass :=
        quittingStationaryContinueMass_nonneg (roots start)
      have hmass1 : continueMass ≤ 1 :=
        quittingStationaryContinueMass_le_one (roots start)
      have hterminalStep :=
        quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff
          reward roots who start
      have hsplit : difference start =
          (value start who -
            quittingRootSuccessorPayoff reward (value (start + 1))
              (roots start) who) +
          (quittingRootSuccessorPayoff reward (value (start + 1))
              (roots start) who -
            quittingRootSuccessorPayoff reward
              (fun _ ↦ terminal (start + 1)) (roots start) who) := by
        dsimp only [difference, terminal]
        rw [hterminalStep]
        ring
      have htail := ih (start + 1) who
      change |difference (start + 1)| ≤
          policyCoefficient * (1 - tailSurvival) +
            tailSurvival * (2 * bound) at htail
      have hstep : |difference start| ≤
          policyCoefficient * (1 - continueMass) +
            continueMass * |difference (start + 1)| := by
        rw [hsplit]
        refine (abs_add_le _ _).trans (add_le_add
          (hpolicyError start who) ?_)
        rw [quittingRootSuccessorPayoff_sub_eq_continueMass_mul,
          abs_mul, abs_of_nonneg hmass0]
      have hscaled := mul_le_mul_of_nonneg_left htail hmass0
      have hsurvival :
          quittingJointSurvivalWeight roots start (fuel + 1) =
            continueMass * tailSurvival := by
        rw [show fuel + 1 = 1 + fuel by omega,
          quittingJointSurvivalWeight_add]
        simp [quittingJointSurvivalWeight,
          quittingFiniteContinueWeight, continueMass, tailSurvival]
      change |difference start| ≤
        policyCoefficient *
            (1 - quittingJointSurvivalWeight roots start (fuel + 1)) +
          quittingJointSurvivalWeight roots start (fuel + 1) * (2 * bound)
      calc
        |difference start| ≤
            policyCoefficient * (1 - continueMass) +
              continueMass * |difference (start + 1)| := hstep
        _ ≤ policyCoefficient * (1 - continueMass) +
            continueMass *
              (policyCoefficient * (1 - tailSurvival) +
                tailSurvival * (2 * bound)) :=
          add_le_add (le_refl _) hscaled
        _ = policyCoefficient *
              (1 - quittingJointSurvivalWeight roots start (fuel + 1)) +
            quittingJointSurvivalWeight roots start (fuel + 1) *
              (2 * bound) := by
          rw [hsurvival]
          ring

omit [DecidableEq ι] in
/-- A joint-absorption-scaled policy defect changes the terminally selected
value by at most its coefficient once joint survival vanishes. -/
theorem abs_value_sub_rootSequenceTerminalValue_le_of_jointPolicyError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    {policyCoefficient bound : ℝ}
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hpolicyError : ∀ time who,
      |value time who -
          quittingRootSuccessorPayoff reward (value (time + 1))
            (roots time) who| ≤
        policyCoefficient * quittingRootAbsorptionMass (roots time))
    (hsurvival : ∀ start,
      Tendsto (quittingJointSurvivalWeight roots start) atTop (nhds 0)) :
    ∀ start who,
      |value start who -
          quittingRootSequenceTerminalValue reward roots who start| ≤
        policyCoefficient := by
  intro start who
  have hfinite :=
    abs_value_sub_rootSequenceTerminalValue_le_jointPolicyCharge
      reward roots value hbound hreward hvalueBound
        hpolicyError start
  have hlimit : Tendsto (fun fuel ↦
      policyCoefficient *
          (1 - quittingJointSurvivalWeight roots start fuel) +
        quittingJointSurvivalWeight roots start fuel * (2 * bound))
      atTop (nhds (policyCoefficient * (1 - 0) + 0 * (2 * bound))) :=
    (tendsto_const_nhds.mul
        (tendsto_const_nhds.sub (hsurvival start))).add
      ((hsurvival start).mul_const (2 * bound))
  have hselected := ge_of_tendsto' hlimit (fun fuel ↦ hfinite fuel who)
  simpa using hselected

/-- An approximately evaluated product path with separated strategic errors.
The policy coefficient uses the joint clock; the refusal coefficient uses
each player's deleted clock. -/
structure QuittingInfinitePathJointPolicySeparatedErrorCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (policyCoefficient quitError refusalCoefficient bound : ℝ) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  value_zero : value 0 = target
  joint_survival : ∀ start,
    Tendsto (quittingJointSurvivalWeight roots start) atTop (nhds 0)
  opponent_survival : ∀ who start,
    Tendsto (quittingOpponentSurvivalWeight roots who start) atTop (nhds 0)
  value_bound : ∀ time who, |value time who| ≤ bound
  policy_error : ∀ time who,
    |value time who -
        quittingRootSuccessorPayoff reward (value (time + 1))
          (roots time) who| ≤
      policyCoefficient * quittingRootAbsorptionMass (roots time)
  quit_le : ∀ time who,
    quittingStationaryFixedOpponentsQuitValue reward (roots time) who ≤
      value time who + quitError
  continue_le : ∀ time who,
    quittingStationaryFixedOpponentsContinueReward reward
          (roots time) who +
        quittingStationaryFixedOpponentsContinueMass (roots time) who *
          value (time + 1) who ≤
      value time who + refusalCoefficient *
        (1 - quittingStationaryFixedOpponentsContinueMass
          (roots time) who)

/-- **Two-clock approximate compiler.**  The policy, immediate-Quit, and
refusal coefficients are each paid once.  The generated product profile is
terminal `(policyCoefficient + quitError + refusalCoefficient)`-Nash and its
terminal payoff is coordinatewise within `policyCoefficient` of the target.
-/
theorem
    QuittingInfinitePathJointPolicySeparatedErrorCertificate.isεAsymptoticNash_and_approximates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) {policyCoefficient quitError refusalCoefficient bound : ℝ}
    (certificate : QuittingInfinitePathJointPolicySeparatedErrorCertificate
      reward target policyCoefficient quitError refusalCoefficient bound)
    (_hpolicyCoefficient : 0 ≤ policyCoefficient)
    (hquitError : 0 ≤ quitError)
    (hrefusal : 0 ≤ refusalCoefficient)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        (policyCoefficient + quitError + refusalCoefficient)
        (quittingInfinitePathProfile reward certificate.roots) ∧
      ∀ who,
        |quittingTerminalPayoff reward
            (quittingInfinitePathProfile reward certificate.roots) who -
          target who| ≤ policyCoefficient := by
  have hselection : ∀ time who,
      |certificate.value time who -
          quittingRootSequenceTerminalValue reward certificate.roots who time| ≤
        policyCoefficient :=
    abs_value_sub_rootSequenceTerminalValue_le_of_jointPolicyError
      reward certificate.roots certificate.value hbound
        hreward certificate.value_bound certificate.policy_error
        certificate.joint_survival
  have hdelivery : ∀ who,
      |quittingTerminalPayoff reward
          (quittingInfinitePathProfile reward certificate.roots) who -
        target who| ≤ policyCoefficient := by
    intro who
    rw [quittingTerminalPayoff_infinitePathProfile]
    have hzero := hselection 0 who
    rw [certificate.value_zero] at hzero
    simpa [abs_sub_comm] using hzero
  constructor
  · intro player deviation
    have hhazard :=
      quittingRootSequenceHazardTerminalValue_le_add_of_separatedError
        reward certificate.roots certificate.value player
          (quittingBehaviorLiveHazard reward deviation)
          hquitError hrefusal hbound hreward certificate.value_bound
          certificate.quit_le certificate.continue_le
          (certificate.opponent_survival player 0)
    have hdeviation :=
      quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
        reward (quittingInfinitePathProfile reward certificate.roots)
          player deviation
    rw [quittingProfileLiveRoot_infinitePathProfile] at hdeviation
    rw [hdeviation]
    have hzero := hselection 0 player
    rw [certificate.value_zero] at hzero
    have hprescribed :
        quittingTerminalPayoff reward
            (quittingInfinitePathProfile reward certificate.roots) player =
          quittingRootSequenceTerminalValue reward certificate.roots player 0 :=
      rfl
    rw [hprescribed]
    rw [abs_le] at hzero
    change quittingRootSequenceHazardTerminalValue reward certificate.roots
        player (quittingBehaviorLiveHazard reward deviation) 0 ≤
      quittingRootSequenceTerminalValue reward certificate.roots player 0 +
        (policyCoefficient + quitError + refusalCoefficient)
    have htarget := congrFun certificate.value_zero player
    linarith
  · exact hdelivery

end GameTheory
