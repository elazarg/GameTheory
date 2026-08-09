/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanQuitEndpointLimit
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart

/-!
# Limit geometry of a summable Nash--Bellman tail

A bounded Bellman path with summable joint absorption has a simultaneous
coordinatewise annotation limit.  Existing remaining-charge estimates give
an explicit modulus.  Exact one-stage Nash makes the limit dominate every
singleton reward, and every player active along a cofinal subsequence is
pinned exactly to that reward.

The final occupation theorem is intentionally abstract.  It consumes the
minimal bridge saying that a positive late occupation supplies an active date
after the same cutoff.  It does not construct a canonical normalized window,
divide by a possibly zero window mass, or identify a periodic refusal law with
an original occupation conditioned off the refusing player.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A bounded Bellman path with summable joint absorption has a simultaneous
coordinatewise limit and the `2 * M * tailCharge` modulus. -/
theorem exists_quittingAnnotationBoundary_of_summableAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : ∀ time who, |value time who| ≤ M)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time))) :
    ∃ boundary : Payoff ι,
      (∀ who, Tendsto (fun time ↦ value time who) atTop
        (nhds (boundary who))) ∧
      ∀ start who,
        |value start who - boundary who| ≤
          2 * M * ∑' offset : ℕ,
            quittingRootAbsorptionMass (roots (start + offset)) := by
  have hcoordinate : ∀ who, ∃ limit : ℝ,
      Tendsto (fun time ↦ value time who) atTop (nhds limit) := by
    intro who
    have hincrements : Summable (fun time ↦
        |value (time + 1) who - value time who|) := by
      apply Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _)
        (fun time ↦ abs_quittingPrescribedValue_succ_sub_le_absorptionMass
          reward roots who (fun time ↦ value time who) (fun time ↦ by
            have hcoordinate := congrFun (hpolicy time) who
            rw [quittingRootSuccessorPayoff_apply_eq_affine] at hcoordinate
            rw [quittingRootSuccessorPayoff_apply_eq_affine]
            exact hcoordinate)
          hreward (fun time ↦ hbound time who) time)
        (hcharge.mul_left (2 * M))
    have hdist : Summable (fun time ↦
        dist (value time who) (value time.succ who)) := by
      simpa [Real.dist_eq, abs_sub_comm, Nat.succ_eq_add_one] using hincrements
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  choose boundary hboundary using hcoordinate
  refine ⟨boundary, hboundary, ?_⟩
  intro start who
  exact abs_quittingValuePath_sub_limit_le_tailCharge
    reward roots value hpolicy boundary hM hreward hbound hcharge
      hboundary start who

/-- Exact Nash plus vanishing opponent absorption passes every singleton-Quit
lower bound to the annotation boundary. -/
theorem quittingSingletonReward_le_annotationBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time, IsεQuittingRootNash reward
      (value (time + 1)) 0 (roots time))
    (boundary : Payoff ι)
    (hboundary : ∀ who, Tendsto (fun time ↦ value time who) atTop
      (nhds (boundary who)))
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (who : ι) :
    reward (quittingSingletonTerminal who) who ≤ boundary who := by
  have htotalZero : Tendsto (fun time ↦
      quittingRootAbsorptionMass (roots time)) atTop (nhds 0) :=
    hcharge.tendsto_atTop_zero
  have hopponentZero : Tendsto (fun time ↦
      quittingRootOpponentAbsorptionMass (roots time) who) atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun _ ↦ quittingOpponentClockCharge_nonneg roots who _
    · exact fun time ↦ quittingRootOpponentAbsorptionMass_le_absorptionMass
        (roots time) who
    · exact htotalZero
  have hlower : Tendsto (fun time ↦
      reward (quittingSingletonTerminal who) who -
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass (roots time) who)
      atTop (nhds (reward (quittingSingletonTerminal who) who)) := by
    simpa using tendsto_const_nhds.sub
      (hopponentZero.const_mul (2 * quittingRewardBound reward))
  apply le_of_tendsto_of_tendsto' hlower (hboundary who)
  intro time
  have hestimate :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (value (time + 1)) (roots time) who
      (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward)
  have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
    reward (value (time + 1)) (roots time) who (hnash time)
  rw [← congrFun (hpolicy time) who] at hquit
  linarith [abs_le.mp hestimate |>.1]

/-- A cofinal subsequence of positive own-Quit hazards pins the limiting
annotation exactly to the singleton reward. -/
theorem quittingAnnotationBoundary_eq_singleton_of_activeSubsequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (boundary : Payoff ι)
    (hboundary : ∀ who, Tendsto (fun time ↦ value time who) atTop
      (nhds (boundary who)))
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (who : ι) (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hactive : ∀ index, 0 < (roots (time index) who true).toReal) :
    boundary who = reward (quittingSingletonTerminal who) who := by
  have htotalZero : Tendsto (fun index ↦
      quittingRootAbsorptionMass (roots (time index))) atTop (nhds 0) :=
    hcharge.tendsto_atTop_zero.comp htime
  have hopponentZero : Tendsto (fun index ↦
      quittingRootOpponentAbsorptionMass (roots (time index)) who)
      atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun _ ↦ quittingOpponentClockCharge_nonneg roots who _
    · exact fun index ↦ quittingRootOpponentAbsorptionMass_le_absorptionMass
        (roots (time index)) who
    · exact htotalZero
  have hdistanceZero : Tendsto (fun index ↦
      |value (time index) who -
        reward (quittingSingletonTerminal who) who|) atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun _ ↦ abs_nonneg _
    · exact fun index ↦ hspine.abs_value_sub_singleton_le_of_quit_pos
        reward value roots who (time index) (hactive index)
    · change Tendsto (fun index ↦
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass (roots (time index)) who)
        atTop (nhds 0)
      simpa only [mul_zero] using
        hopponentZero.const_mul (2 * quittingRewardBound reward)
  have hdistanceBoundary : Tendsto (fun index ↦
      |value (time index) who -
        reward (quittingSingletonTerminal who) who|) atTop
      (nhds |boundary who -
        reward (quittingSingletonTerminal who) who|) :=
    ((hboundary who).comp htime).sub tendsto_const_nhds |>.abs
  have habs : |boundary who -
      reward (quittingSingletonTerminal who) who| = 0 :=
    tendsto_nhds_unique hdistanceBoundary hdistanceZero
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

/-- Positive limiting occupation pins a player whenever every positive late
occupation supplies a positive-hazard date beyond the same cutoff. -/
theorem quittingAnnotationBoundary_eq_singleton_of_positiveOccupation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (boundary : Payoff ι)
    (hboundary : ∀ who, Tendsto (fun time ↦ value time who) atTop
      (nhds (boundary who)))
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (occupation : ℕ → ι → ℝ) (limitOccupation : ι → ℝ)
    (hoccupation : ∀ who, Tendsto (fun cutoff ↦ occupation cutoff who)
      atTop (nhds (limitOccupation who)))
    (hactiveAfter : ∀ cutoff who, 0 < occupation cutoff who →
      ∃ time, cutoff ≤ time ∧ 0 < (roots time who true).toReal)
    (who : ι) (hpositive : 0 < limitOccupation who) :
    boundary who = reward (quittingSingletonTerminal who) who := by
  have heventually : ∀ᶠ cutoff : ℕ in atTop,
      0 < occupation cutoff who :=
    (hoccupation who).eventually (Ioi_mem_nhds hpositive)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 heventually
  have hexists : ∀ index, ∃ time,
      index ≤ time ∧ 0 < (roots time who true).toReal := by
    intro index
    let cutoff := max threshold index
    have hocc : 0 < occupation cutoff who := hthreshold cutoff
      (le_max_left threshold index)
    obtain ⟨time, hcutoff, hactive⟩ := hactiveAfter cutoff who hocc
    exact ⟨time, (le_max_right threshold index).trans hcutoff, hactive⟩
  choose time htime hactive using hexists
  have htendsto : Tendsto time atTop atTop :=
    Filter.tendsto_atTop_mono htime tendsto_id
  exact quittingAnnotationBoundary_eq_singleton_of_activeSubsequence
    reward roots value hspine boundary hboundary hcharge who time htendsto
      hactive

end GameTheory
