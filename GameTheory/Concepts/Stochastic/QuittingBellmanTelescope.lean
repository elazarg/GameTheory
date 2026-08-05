/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingPureTimeExtremality
import GameTheory.Concepts.Stochastic.QuittingExceptionalHazard
import Math.SurvivalProduct

/-!
# Bellman residual telescope along a quitting live path

Fix a sequence of product roots along the unique live path and one player.
The player's one-step Bellman operator compares quitting now with continuing
now and using a supplied value at the next live stage.  This file records the
prescribed residual, the gap to a Bellman cap, and their finite weighted
telescope.

The finite statements make no tail-contraction claim.  In particular, a
zero opponent-survival factor before the starting time is never used to infer
contraction after that time.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The one-step pure-action Bellman value against the supplied opponent
marginals at a live stage. -/
def quittingLiveBellmanValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (value : ℕ → ℝ) (time : ℕ) : ℝ :=
  max (quittingFixedOpponentsQuitValue reward roots who time)
    (quittingFixedOpponentsContinueReward reward roots who time +
      quittingFixedOpponentsContinueMass roots who time * value (time + 1))

/-- Loss of the prescribed continuation value relative to the best pure
action at the current live stage. -/
def quittingPrescribedOneStepResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) : ℝ :=
  quittingLiveBellmanValue reward roots who prescribed time - prescribed time

/-- Pointwise difference between a Bellman cap and the prescribed value. -/
def quittingBellmanCapGap
    (prescribed cap : ℕ → ℝ) (time : ℕ) : ℝ :=
  cap time - prescribed time

/-- A supplied value sequence solves the pure-action Bellman maximum
recursion along the live path.  Its terminal selection is deliberately a
separate issue. -/
def IsQuittingLiveBellmanCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (cap : ℕ → ℝ) : Prop :=
  ∀ time, cap time = quittingLiveBellmanValue reward roots who cap time

/-- The prescribed values are obtained by using the supplied product root
at the current stage and the next prescribed value after all continue. -/
def IsQuittingLivePrescribedValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) : Prop :=
  ∀ time,
    prescribed time = quittingRootSuccessorPayoff reward
      (fun _ => prescribed (time + 1)) (roots time) who

/-- The pure-Quit endpoint is exactly the fixed-opponent quit value and does
not depend on the declared all-continue tail. -/
theorem quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (tail : Payoff ι) (time : ℕ) :
    quittingRootQuitPayoff reward tail (roots time) who =
      quittingFixedOpponentsQuitValue reward roots who time := by
  unfold quittingRootQuitPayoff quittingFixedOpponentsQuitValue
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingStationaryContinueMass_update_pure_true_eq_zero]
  simp

/-- The pure-Continue endpoint splits into current opponent absorption plus
opponent survival times the declared tail. -/
theorem quittingRootContinuePayoff_eq_fixedOpponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (tail : Payoff ι) (time : ℕ) :
    quittingRootContinuePayoff reward tail (roots time) who =
      quittingFixedOpponentsContinueReward reward roots who time +
        quittingFixedOpponentsContinueMass roots who time * tail who := by
  unfold quittingRootContinuePayoff
    quittingFixedOpponentsContinueReward
    quittingFixedOpponentsContinueMass
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]

/-- Policy evaluation is below its one-step pure-action maximum. -/
theorem quittingRootSuccessorPayoff_le_liveBellmanValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (time : ℕ) :
    quittingRootSuccessorPayoff reward
        (fun _ => prescribed (time + 1)) (roots time) who ≤
      quittingLiveBellmanValue reward roots who prescribed time := by
  let quitValue := quittingFixedOpponentsQuitValue reward roots who time
  let continueValue :=
    quittingFixedOpponentsContinueReward reward roots who time +
      quittingFixedOpponentsContinueMass roots who time * prescribed (time + 1)
  have hquit := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    reward roots who (fun _ => prescribed (time + 1)) time
  have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents
    reward roots who (fun _ => prescribed (time + 1)) time
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (roots time) who
  rw [quittingRootSuccessorPayoff_eq_endpointMix, hquit, hcontinue]
  change
    (roots time who true).toReal * quitValue +
        (roots time who false).toReal * continueValue ≤
      max quitValue continueValue
  calc
    (roots time who true).toReal * quitValue +
          (roots time who false).toReal * continueValue ≤
        (roots time who true).toReal * max quitValue continueValue +
          (roots time who false).toReal * max quitValue continueValue := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ENNReal.toReal_nonneg)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) ENNReal.toReal_nonneg)
    _ = max quitValue continueValue := by
      rw [← add_mul]
      have : (roots time who true).toReal +
          (roots time who false).toReal = 1 := by linarith
      rw [this, one_mul]

/-- A genuinely prescribed policy value has a nonnegative one-step
residual. -/
theorem quittingPrescribedOneStepResidual_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    (time : ℕ) :
    0 ≤ quittingPrescribedOneStepResidual
      reward roots who prescribed time := by
  unfold quittingPrescribedOneStepResidual
  rw [hprescribed time]
  exact sub_nonneg.mpr
    (quittingRootSuccessorPayoff_le_liveBellmanValue
      reward roots who prescribed time)

/-- One Bellman step: the cap gap is at most the prescribed local residual
plus opponent survival times the next cap gap. -/
theorem quittingBellmanCapGap_le_residual_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed cap : ℕ → ℝ)
    (hcap : IsQuittingLiveBellmanCap reward roots who cap)
    (time : ℕ)
    (hnext : 0 ≤ quittingBellmanCapGap prescribed cap (time + 1)) :
    quittingBellmanCapGap prescribed cap time ≤
      quittingPrescribedOneStepResidual reward roots who prescribed time +
        quittingFixedOpponentsContinueMass roots who time *
          quittingBellmanCapGap prescribed cap (time + 1) := by
  let quitValue := quittingFixedOpponentsQuitValue reward roots who time
  let continueValue :=
    quittingFixedOpponentsContinueReward reward roots who time +
      quittingFixedOpponentsContinueMass roots who time * prescribed (time + 1)
  let continueMass := quittingFixedOpponentsContinueMass roots who time
  let nextGap := quittingBellmanCapGap prescribed cap (time + 1)
  have hmass : 0 ≤ continueMass := by
    exact quittingStationaryContinueMass_nonneg
      (Function.update (roots time) who (PMF.pure false))
  have hscaled : 0 ≤ continueMass * nextGap :=
    mul_nonneg hmass hnext
  have hcontinue :
      quittingFixedOpponentsContinueReward reward roots who time +
          continueMass * cap (time + 1) =
        continueValue + continueMass * nextGap := by
    dsimp [continueValue, nextGap, quittingBellmanCapGap]
    ring
  have hmax :
      max quitValue (continueValue + continueMass * nextGap) ≤
        max quitValue continueValue + continueMass * nextGap := by
    apply max_le
    · linarith [le_max_left quitValue continueValue]
    · linarith [le_max_right quitValue continueValue]
  unfold quittingBellmanCapGap quittingPrescribedOneStepResidual
  rw [hcap time]
  unfold quittingLiveBellmanValue
  change
    max quitValue
          (quittingFixedOpponentsContinueReward reward roots who time +
            continueMass * cap (time + 1)) - prescribed time ≤
      (max quitValue continueValue - prescribed time) +
        continueMass * nextGap
  rw [hcontinue]
  linarith

/-! ## Finite weighted iteration -/

/-- Opponent survival for `fuel` stages starting from a supplied live time. -/
def quittingOpponentSurvivalWeight
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (start fuel : ℕ) : ℝ :=
  ∏ offset ∈ Finset.range fuel,
    quittingFixedOpponentsContinueMass roots who (start + offset)

/-- **Bridge to the canonical survival product.**  `quittingOpponentSurvivalWeight`
is `Math.survivalProduct` at the *deleted* (opponent-restricted) continue mass
-- the genuinely distinct sibling of the joint-side names, not another name
for the same number -- see the module docstring of `Math.SurvivalProduct` for
the full census this bridges into. -/
theorem quittingOpponentSurvivalWeight_eq_survivalProduct
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingOpponentSurvivalWeight roots who start fuel =
      Math.survivalProduct (quittingFixedOpponentsContinueMass roots who) start fuel :=
  rfl

/-- Every finite opponent-survival weight is nonnegative. -/
theorem quittingOpponentSurvivalWeight_nonneg
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (start fuel : ℕ) :
    0 ≤ quittingOpponentSurvivalWeight roots who start fuel := by
  apply Finset.prod_nonneg
  intro offset _
  exact quittingStationaryContinueMass_nonneg
    (Function.update (roots (start + offset)) who (PMF.pure false))

/-- Adding one stage multiplies survival by that stage's opponent continue
mass. -/
theorem quittingOpponentSurvivalWeight_succ
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (start fuel : ℕ) :
    quittingOpponentSurvivalWeight roots who start (fuel + 1) =
      quittingOpponentSurvivalWeight roots who start fuel *
        quittingFixedOpponentsContinueMass roots who (start + fuel) := by
  simp [quittingOpponentSurvivalWeight, Finset.prod_range_succ]

/-- Finite Bellman iteration with the exact opponent-survival weights.  The
last term is retained, so this theorem requires no asymptotic or
zero-factor hypothesis. -/
theorem quittingBellmanCapGap_le_sum_residual_add_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed cap : ℕ → ℝ)
    (hcap : IsQuittingLiveBellmanCap reward roots who cap)
    (hgap : ∀ time, 0 ≤ quittingBellmanCapGap prescribed cap time)
    (start fuel : ℕ) :
    quittingBellmanCapGap prescribed cap start ≤
      (∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            quittingPrescribedOneStepResidual reward roots who prescribed
              (start + offset)) +
        quittingOpponentSurvivalWeight roots who start fuel *
          quittingBellmanCapGap prescribed cap (start + fuel) := by
  induction fuel with
  | zero =>
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hstep := quittingBellmanCapGap_le_residual_add
        reward roots who prescribed cap hcap (start + fuel)
          (hgap (start + fuel + 1))
      have hscaled := mul_le_mul_of_nonneg_left hstep
        (quittingOpponentSurvivalWeight_nonneg roots who start fuel)
      calc
        quittingBellmanCapGap prescribed cap start ≤
            (∑ offset ∈ Finset.range fuel,
                quittingOpponentSurvivalWeight roots who start offset *
                  quittingPrescribedOneStepResidual reward roots who prescribed
                    (start + offset)) +
              quittingOpponentSurvivalWeight roots who start fuel *
                quittingBellmanCapGap prescribed cap (start + fuel) := ih
        _ ≤ (∑ offset ∈ Finset.range fuel,
                quittingOpponentSurvivalWeight roots who start offset *
                  quittingPrescribedOneStepResidual reward roots who prescribed
                    (start + offset)) +
              quittingOpponentSurvivalWeight roots who start fuel *
                (quittingPrescribedOneStepResidual reward roots who prescribed
                    (start + fuel) +
                  quittingFixedOpponentsContinueMass roots who (start + fuel) *
                    quittingBellmanCapGap prescribed cap (start + fuel + 1)) := by
              exact add_le_add le_rfl hscaled
        _ = (∑ offset ∈ Finset.range (fuel + 1),
                quittingOpponentSurvivalWeight roots who start offset *
                  quittingPrescribedOneStepResidual reward roots who prescribed
                    (start + offset)) +
              quittingOpponentSurvivalWeight roots who start (fuel + 1) *
                quittingBellmanCapGap prescribed cap (start + (fuel + 1)) := by
              rw [Finset.sum_range_succ,
                quittingOpponentSurvivalWeight_succ]
              simp only [Nat.add_assoc]
              ring

/-! ## Hazard-scaled telescope -/

/-- Opponent hazard telescopes exactly against its preceding survival
weight. -/
theorem sum_quittingOpponentSurvivalWeight_mul_one_sub_continueMass
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (start fuel : ℕ) :
    (∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          (1 - quittingFixedOpponentsContinueMass roots who
            (start + offset))) =
      1 - quittingOpponentSurvivalWeight roots who start fuel := by
  induction fuel with
  | zero =>
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      rw [Finset.sum_range_succ, ih,
        quittingOpponentSurvivalWeight_succ]
      ring

/-- If each local residual is scaled by the current opponent hazard, finite
Bellman iteration charges at most `η` times the loss of opponent survival,
plus the exact surviving boundary gap. -/
theorem quittingBellmanCapGap_le_hazardScaled_add_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed cap : ℕ → ℝ)
    (hcap : IsQuittingLiveBellmanCap reward roots who cap)
    (hgap : ∀ time, 0 ≤ quittingBellmanCapGap prescribed cap time)
    (η : ℝ)
    (hresidual : ∀ time,
      quittingPrescribedOneStepResidual reward roots who prescribed time ≤
        η * (1 - quittingFixedOpponentsContinueMass roots who time))
    (start fuel : ℕ) :
    quittingBellmanCapGap prescribed cap start ≤
      η * (1 - quittingOpponentSurvivalWeight roots who start fuel) +
        quittingOpponentSurvivalWeight roots who start fuel *
          quittingBellmanCapGap prescribed cap (start + fuel) := by
  have hiterate := quittingBellmanCapGap_le_sum_residual_add_tail
    reward roots who prescribed cap hcap hgap start fuel
  have hsum :
      (∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            quittingPrescribedOneStepResidual reward roots who prescribed
              (start + offset)) ≤
        ∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            (η * (1 - quittingFixedOpponentsContinueMass roots who
              (start + offset))) := by
    apply Finset.sum_le_sum
    intro offset _
    exact mul_le_mul_of_nonneg_left (hresidual (start + offset))
      (quittingOpponentSurvivalWeight_nonneg roots who start offset)
  calc
    quittingBellmanCapGap prescribed cap start ≤
        (∑ offset ∈ Finset.range fuel,
            quittingOpponentSurvivalWeight roots who start offset *
              quittingPrescribedOneStepResidual reward roots who prescribed
                (start + offset)) +
          quittingOpponentSurvivalWeight roots who start fuel *
            quittingBellmanCapGap prescribed cap (start + fuel) := hiterate
    _ ≤ (∑ offset ∈ Finset.range fuel,
            quittingOpponentSurvivalWeight roots who start offset *
              (η * (1 - quittingFixedOpponentsContinueMass roots who
                (start + offset)))) +
          quittingOpponentSurvivalWeight roots who start fuel *
            quittingBellmanCapGap prescribed cap (start + fuel) :=
      add_le_add hsum le_rfl
    _ = η * (1 - quittingOpponentSurvivalWeight roots who start fuel) +
          quittingOpponentSurvivalWeight roots who start fuel *
            quittingBellmanCapGap prescribed cap (start + fuel) := by
      rw [show (∑ offset ∈ Finset.range fuel,
            quittingOpponentSurvivalWeight roots who start offset *
              (η * (1 - quittingFixedOpponentsContinueMass roots who
                (start + offset)))) =
          η * ∑ offset ∈ Finset.range fuel,
            quittingOpponentSurvivalWeight roots who start offset *
              (1 - quittingFixedOpponentsContinueMass roots who
                (start + offset)) by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro offset _
            ring]
      rw [sum_quittingOpponentSurvivalWeight_mul_one_sub_continueMass]

/-- In the hazard-scaled regime, any future cap gap already below `η`
propagates backward with the same sharp constant. -/
theorem quittingBellmanCapGap_le_of_hazardScaled_of_tail_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed cap : ℕ → ℝ)
    (hcap : IsQuittingLiveBellmanCap reward roots who cap)
    (hgap : ∀ time, 0 ≤ quittingBellmanCapGap prescribed cap time)
    (η : ℝ)
    (hresidual : ∀ time,
      quittingPrescribedOneStepResidual reward roots who prescribed time ≤
        η * (1 - quittingFixedOpponentsContinueMass roots who time))
    (start fuel : ℕ)
    (htail : quittingBellmanCapGap prescribed cap (start + fuel) ≤ η) :
    quittingBellmanCapGap prescribed cap start ≤ η := by
  have hfinite := quittingBellmanCapGap_le_hazardScaled_add_tail
    reward roots who prescribed cap hcap hgap η hresidual start fuel
  have hscaled := mul_le_mul_of_nonneg_left htail
    (quittingOpponentSurvivalWeight_nonneg roots who start fuel)
  linarith

/-- If the opponent-survival clock contracts from the chosen start and the
cap gap is uniformly bounded, the surviving boundary term vanishes.  This
is the nonexceptional hazard-scaled conclusion; contraction is assumed at
the actual start, so an earlier zero factor is irrelevant. -/
theorem quittingBellmanCapGap_le_hazardScaled_of_survival_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed cap : ℕ → ℝ)
    (hcap : IsQuittingLiveBellmanCap reward roots who cap)
    (hgap : ∀ time, 0 ≤ quittingBellmanCapGap prescribed cap time)
    (η bound : ℝ)
    (hresidual : ∀ time,
      quittingPrescribedOneStepResidual reward roots who prescribed time ≤
        η * (1 - quittingFixedOpponentsContinueMass roots who time))
    (hbound : ∀ time,
      quittingBellmanCapGap prescribed cap time ≤ bound)
    (start : ℕ)
    (hsurvival : Filter.Tendsto (fun fuel =>
      quittingOpponentSurvivalWeight roots who start fuel)
      Filter.atTop (nhds 0)) :
    quittingBellmanCapGap prescribed cap start ≤ η := by
  let weight : ℕ → ℝ := fun fuel =>
    quittingOpponentSurvivalWeight roots who start fuel
  have hlimit : Filter.Tendsto (fun fuel =>
      η * (1 - weight fuel) + weight fuel * bound)
      Filter.atTop (nhds η) := by
    have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
        Filter.atTop (nhds 1) := tendsto_const_nhds
    have hleft := (hone.sub hsurvival).const_mul η
    have hright := hsurvival.mul_const bound
    simpa [weight] using hleft.add hright
  apply ge_of_tendsto' hlimit
  intro fuel
  dsimp [weight]
  have hfinite := quittingBellmanCapGap_le_hazardScaled_add_tail
    reward roots who prescribed cap hcap hgap η hresidual start fuel
  have htail := mul_le_mul_of_nonneg_left (hbound (start + fuel))
    (quittingOpponentSurvivalWeight_nonneg roots who start fuel)
  linarith

/-! ## Behavior-profile and exceptional-hazard bridge -/

/-- The product root prescribed by a behavior profile at the unique live
history of a given stage. -/
def quittingProfileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (time : ℕ) : ι → PMF Bool :=
  fun player => profile player time (quittingLiveHist reward time)

/-- The fixed-root opponent continue coefficient is the existing
opponent-only conditional live mass. -/
theorem quittingFixedOpponentsContinueMass_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) :
    quittingFixedOpponentsContinueMass
        (quittingProfileLiveRoot reward profile) who time =
      quittingJointContinueMass reward
        (quittingOpponentOnlyProfile reward profile who) time := by
  unfold quittingFixedOpponentsContinueMass
    quittingStationaryContinueMass quittingJointContinueMass
    StochasticGame.stageActionDist quittingOpponentOnlyProfile
    quittingProfileLiveRoot
  congr 3
  funext player
  by_cases hp : player = who
  · subst player
    simp only [Function.update_self, quittingAlwaysContinueStrategy]
    rfl
  · simp [Function.update_of_ne hp]

/-- Starting from time zero, the finite survival weights used by the
Bellman telescope are exactly the existing opponent-only live masses. -/
theorem quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) :
    ∀ fuel,
      quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward profile) who 0 fuel =
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) fuel := by
  intro fuel
  induction fuel with
  | zero =>
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      calc
        quittingOpponentSurvivalWeight
              (quittingProfileLiveRoot reward profile) who 0 (fuel + 1) =
            quittingOpponentSurvivalWeight
                (quittingProfileLiveRoot reward profile) who 0 fuel *
              quittingFixedOpponentsContinueMass
                (quittingProfileLiveRoot reward profile) who fuel := by
                  simpa only [Nat.zero_add] using
                    (quittingOpponentSurvivalWeight_succ
                      (quittingProfileLiveRoot reward profile) who 0 fuel)
        _ = quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) fuel *
            quittingFixedOpponentsContinueMass
              (quittingProfileLiveRoot reward profile) who fuel := by rw [ih]
        _ = quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) fuel *
            quittingJointContinueMass reward
              (quittingOpponentOnlyProfile reward profile who) fuel := by
                rw [quittingFixedOpponentsContinueMass_profileLiveRoot]
        _ = quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) (fuel + 1) :=
                (quittingLiveMass_succ reward
                  (quittingOpponentOnlyProfile reward profile who) fuel).symm

/-- Under total almost-sure absorption, for any two distinct players at
least one Bellman opponent-survival clock contracts to zero.  This is the
finite-weight form of the already established exceptional-player theorem. -/
theorem tendsto_zero_quittingOpponentSurvivalWeight_or
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (htotal : Filter.Tendsto (quittingLiveMass reward profile)
      Filter.atTop (nhds 0))
    {first second : ι} (hne : first ≠ second) :
    Filter.Tendsto (fun fuel =>
        quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward profile) first 0 fuel)
        Filter.atTop (nhds 0) ∨
      Filter.Tendsto (fun fuel =>
        quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward profile) second 0 fuel)
        Filter.atTop (nhds 0) := by
  rcases tendsto_zero_quittingOpponentLiveMass_or
      reward profile htotal hne with hfirst | hsecond
  · left
    simpa only [quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass]
      using hfirst
  · right
    simpa only [quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass]
      using hsecond

/-- Equivalently, two noncontracting Bellman opponent clocks must belong to
the same player. -/
theorem eq_of_quittingOpponentSurvivalWeight_not_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (htotal : Filter.Tendsto (quittingLiveMass reward profile)
      Filter.atTop (nhds 0))
    {first second : ι}
    (hfirst : ¬Filter.Tendsto (fun fuel =>
      quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) first 0 fuel)
      Filter.atTop (nhds 0))
    (hsecond : ¬Filter.Tendsto (fun fuel =>
      quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) second 0 fuel)
      Filter.atTop (nhds 0)) :
    first = second := by
  by_contra hne
  exact (tendsto_zero_quittingOpponentSurvivalWeight_or
    reward profile htotal hne).elim hfirst hsecond

end GameTheory
