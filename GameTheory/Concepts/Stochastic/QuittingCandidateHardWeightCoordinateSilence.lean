/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingJointComplementarity
import GameTheory.Concepts.Stochastic.QuittingCandidateHardWeightCycle

/-!
# Coordinate `2` is silent in every jointly complementary sequence

Deliverable 1 for the candidate hard weight (`QuittingCandidateHardWeightCycle.lean`):
every jointly complementary sequence (`IsQuittingJointComplementary`) for that weight
has coordinate `2` (`true`) quitting with probability zero at every time.

## Contents

* `reward_true_le`, `le_reward_true`, `reward_false_le`, `le_reward_false`:
  the reward table is bounded in `[0,1]` at coordinate `2` and in `[-1,-α]`
  at coordinate `1`.
* `quittingRootAbsorbingContribution_le_of`,
  `le_quittingRootAbsorbingContribution_of`: general one-sided companions of
  `abs_quittingRootAbsorbingContribution_le`.
* `quittingComplementarityTailValue_le_of_tendsto_zero`,
  `le_quittingComplementarityTailValue_of_tendsto_zero`: general one-sided
  tail-value bounds under vanishing joint survival.
* the closed forms for `quittingFixedOpponentsQuitValue`,
  `quittingFixedOpponentsContinueReward`, `quittingFixedOpponentsContinueMass`
  at both coordinates, for an arbitrary two-marginal root.
* `quitProbability_true_eq_zero_of_isQuittingJointComplementary`: **Deliverable 1**.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

namespace QuittingCandidateHardWeightCoordinateSilence

open Filter Math.Probability Math.PMFProduct QuittingCandidateHardWeightCycle

/-! ## Reward-table bounds for this weight -/

/-- Coordinate `1`'s reward is never above `-α`. -/
theorem reward_false_le (α : ℝ) (hα1 : α < 1) (S : {S : Finset Bool // S.Nonempty}) :
    reward α S false ≤ -α := by
  unfold reward
  split_ifs <;> simp_all
  linarith

/-- Coordinate `1`'s reward is never below `-1`. -/
theorem le_reward_false (α : ℝ) (hα1 : α < 1) (S : {S : Finset Bool // S.Nonempty}) :
    -1 ≤ reward α S false := by
  unfold reward
  split_ifs <;> simp_all <;> linarith

/-- Coordinate `2`'s reward is never above `1`. -/
theorem reward_true_le (α : ℝ) (S : {S : Finset Bool // S.Nonempty}) :
    reward α S true ≤ 1 := by
  unfold reward
  split_ifs <;> simp_all

/-- Coordinate `2`'s reward is never below `0`. -/
theorem le_reward_true (α : ℝ) (S : {S : Finset Bool // S.Nonempty}) :
    0 ≤ reward α S true := by
  unfold reward
  split_ifs <;> simp_all

/-! ## General one-sided companions to `abs_quittingRootAbsorbingContribution_le` -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- One-sided upper companion to `abs_quittingRootAbsorbingContribution_le`. -/
theorem quittingRootAbsorbingContribution_le_of
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (maxR : ℝ)
    (hreward : ∀ S, reward S who ≤ maxR) :
    quittingRootAbsorbingContribution reward root who ≤
      maxR * quittingRootAbsorptionMass root := by
  let absorbingBound : (ι → Bool) → ℝ := fun action ↦
    if (quittingQuitters action).Nonempty then maxR else 0
  have hpointUpper (action : ι → Bool) :
      quittingRootPayoff reward (0 : Payoff ι) action who ≤
        absorbingBound action := by
    by_cases hquit : (quittingQuitters action).Nonempty
    · simp only [quittingRootPayoff, dif_pos hquit, absorbingBound, if_pos hquit]
      exact hreward _
    · simp only [quittingRootPayoff, dif_neg hquit, Pi.zero_apply, absorbingBound,
        if_neg hquit, le_refl]
  have hupper :
      quittingRootAbsorbingContribution reward root who ≤
        expect (pmfPi root) absorbingBound := by
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    exact expect_mono _ _ _ hpointUpper
  have hboundExpectation :
      expect (pmfPi root) absorbingBound = maxR * quittingRootAbsorptionMass root := by
    unfold absorbingBound
    rw [show (fun action : ι → Bool ↦
        if (quittingQuitters action).Nonempty then maxR else 0) =
        fun action ↦ maxR *
          (if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) by
      funext action
      split <;> simp_all]
    rw [expect_const_mul, expect_quittingNonemptyIndicator_eq_absorptionMass]
  rwa [hboundExpectation] at hupper

omit [DecidableEq ι] in
/-- One-sided lower companion to `abs_quittingRootAbsorbingContribution_le`. -/
theorem le_quittingRootAbsorbingContribution_of
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (minR : ℝ)
    (hreward : ∀ S, minR ≤ reward S who) :
    minR * quittingRootAbsorptionMass root ≤
      quittingRootAbsorbingContribution reward root who := by
  let absorbingBound : (ι → Bool) → ℝ := fun action ↦
    if (quittingQuitters action).Nonempty then minR else 0
  have hpointLower (action : ι → Bool) :
      absorbingBound action ≤
        quittingRootPayoff reward (0 : Payoff ι) action who := by
    by_cases hquit : (quittingQuitters action).Nonempty
    · simp only [quittingRootPayoff, dif_pos hquit, absorbingBound, if_pos hquit]
      exact hreward _
    · simp only [quittingRootPayoff, dif_neg hquit, Pi.zero_apply, absorbingBound,
        if_neg hquit, le_refl]
  have hlower :
      expect (pmfPi root) absorbingBound ≤
        quittingRootAbsorbingContribution reward root who := by
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    exact expect_mono _ _ _ hpointLower
  have hboundExpectation :
      expect (pmfPi root) absorbingBound = minR * quittingRootAbsorptionMass root := by
    unfold absorbingBound
    rw [show (fun action : ι → Bool ↦
        if (quittingQuitters action).Nonempty then minR else 0) =
        fun action ↦ minR *
          (if (quittingQuitters action).Nonempty then (1 : ℝ) else 0) by
      funext action
      split <;> simp_all]
    rw [expect_const_mul, expect_quittingNonemptyIndicator_eq_absorptionMass]
  rwa [hboundExpectation] at hlower

/-! ## General one-sided tail-value bounds under vanishing joint survival -/

omit [DecidableEq ι] in
/-- Upper one-sided bound on the tail value, from a pointwise reward-table
upper bound and a joint survival weight vanishing from `start`.  A tight
companion to `abs_quittingComplementarityTailValue_le_of_tendsto`, avoided
there because that lemma is symmetric and needs no survival hypothesis. -/
theorem quittingComplementarityTailValue_le_of_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) (maxR : ℝ)
    (hreward : ∀ S, reward S who ≤ maxR)
    (hsurvival : Tendsto (quittingJointSurvivalWeight x start) atTop (nhds 0)) :
    quittingComplementarityTailValue reward x who start ≤ maxR := by
  have hsummable :=
    summable_quittingJointSurvivalWeight_mul_quittingRootAbsorbingContribution
      reward x who start
  have hpartial : ∀ fuel, (∑ offset ∈ Finset.range fuel,
      quittingJointSurvivalWeight x start offset *
        quittingRootAbsorbingContribution reward (x (start + offset)) who) ≤
      maxR * (1 - quittingJointSurvivalWeight x start fuel) := by
    intro fuel
    calc (∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight x start offset *
          quittingRootAbsorbingContribution reward (x (start + offset)) who) ≤
        ∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight x start offset *
            (maxR * (1 - quittingStationaryContinueMass (x (start + offset)))) := by
          apply Finset.sum_le_sum
          intro offset _
          apply mul_le_mul_of_nonneg_left _
            (quittingJointSurvivalWeight_nonneg x start offset)
          have hbound := quittingRootAbsorbingContribution_le_of reward
            (x (start + offset)) who maxR hreward
          rwa [quittingRootAbsorptionMass] at hbound
      _ = maxR * ∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight x start offset *
              (1 - quittingStationaryContinueMass (x (start + offset))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro offset _
          ring
      _ = maxR * (1 - quittingJointSurvivalWeight x start fuel) := by
          rw [sum_quittingJointSurvivalWeight_mul_one_sub_continueMass]
  have hlhs : Tendsto (fun fuel => ∑ offset ∈ Finset.range fuel,
      quittingJointSurvivalWeight x start offset *
        quittingRootAbsorbingContribution reward (x (start + offset)) who)
      atTop (nhds (quittingComplementarityTailValue reward x who start)) := by
    unfold quittingComplementarityTailValue
    exact hsummable.hasSum.tendsto_sum_nat
  have hrhs : Tendsto (fun fuel =>
      maxR * (1 - quittingJointSurvivalWeight x start fuel)) atTop (nhds maxR) := by
    have h1 : Tendsto (fun fuel : ℕ => (1 : ℝ) - quittingJointSurvivalWeight x start fuel)
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hsurvival
    simpa using h1.const_mul maxR
  exact le_of_tendsto_of_tendsto' hlhs hrhs hpartial

omit [DecidableEq ι] in
/-- Lower one-sided bound on the tail value, from a pointwise reward-table
lower bound and a joint survival weight vanishing from `start`. -/
theorem le_quittingComplementarityTailValue_of_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) (minR : ℝ)
    (hreward : ∀ S, minR ≤ reward S who)
    (hsurvival : Tendsto (quittingJointSurvivalWeight x start) atTop (nhds 0)) :
    minR ≤ quittingComplementarityTailValue reward x who start := by
  have hsummable :=
    summable_quittingJointSurvivalWeight_mul_quittingRootAbsorbingContribution
      reward x who start
  have hpartial : ∀ fuel, minR * (1 - quittingJointSurvivalWeight x start fuel) ≤
      (∑ offset ∈ Finset.range fuel,
        quittingJointSurvivalWeight x start offset *
          quittingRootAbsorbingContribution reward (x (start + offset)) who) := by
    intro fuel
    calc minR * (1 - quittingJointSurvivalWeight x start fuel) =
        minR * ∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight x start offset *
              (1 - quittingStationaryContinueMass (x (start + offset))) := by
          rw [sum_quittingJointSurvivalWeight_mul_one_sub_continueMass]
      _ = ∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight x start offset *
              (minR * (1 - quittingStationaryContinueMass (x (start + offset)))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro offset _
          ring
      _ ≤ ∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalWeight x start offset *
              quittingRootAbsorbingContribution reward (x (start + offset)) who := by
          apply Finset.sum_le_sum
          intro offset _
          apply mul_le_mul_of_nonneg_left _
            (quittingJointSurvivalWeight_nonneg x start offset)
          have hbound := le_quittingRootAbsorbingContribution_of reward
            (x (start + offset)) who minR hreward
          rwa [quittingRootAbsorptionMass] at hbound
  have hlhs : Tendsto (fun fuel =>
      minR * (1 - quittingJointSurvivalWeight x start fuel)) atTop (nhds minR) := by
    have h1 : Tendsto (fun fuel : ℕ => (1 : ℝ) - quittingJointSurvivalWeight x start fuel)
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hsurvival
    simpa using h1.const_mul minR
  have hrhs : Tendsto (fun fuel => ∑ offset ∈ Finset.range fuel,
      quittingJointSurvivalWeight x start offset *
        quittingRootAbsorbingContribution reward (x (start + offset)) who)
      atTop (nhds (quittingComplementarityTailValue reward x who start)) := by
    unfold quittingComplementarityTailValue
    exact hsummable.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto' hlhs hrhs hpartial

/-! ## Closed forms for the fixed-opponent quantities, both coordinates -/

/-- Player `1`'s reward at the joint-quit terminal, the companion to
`collisionReward_false_true`. -/
theorem collisionReward_true_false (α : ℝ) :
    quittingSingletonCollisionReward (reward α) true false = -α := by
  have h1 : ({true, false} : Finset Bool) ≠ {false} := by decide
  have h2 : ({true, false} : Finset Bool) ≠ {true} := by decide
  simp [quittingSingletonCollisionReward, reward, h1, h2]

/-- Coordinate `2`'s pure-Quit payoff: quitting alone (`r_2({2}) = 1`) if
opponent `1` continues, or colliding (`r_2({1,2}) = 0`) if opponent `1` also
quits.  Independent of `tail`, since quitting absorbs immediately. -/
theorem quitPayoff_true (α : ℝ) (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff (reward α) tail root true =
      (root false false).toReal := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp only [Function.update_apply, if_true, Bool.false_eq_true, if_false]
  simp only [expect_pure]
  rw [expect_eq_sum, Fintype.sum_bool]
  simp +decide [quittingRootPayoff, reward]

/-- Coordinate `1`'s pure-Quit payoff is the constant `-α`: both quitting
alone (`r_1({1}) = -α`) and colliding (`r_1({1,2}) = -α`) give the same
value, regardless of opponent `2`'s marginal.  Independent of `tail`. -/
theorem quitPayoff_false (α : ℝ) (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootQuitPayoff (reward α) tail root false = -α := by
  have hsum := quittingRoot_continueProbability_add_quitProbability root true
  have heq : (root true true).toReal = 1 - (root true false).toReal := by linarith
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp only [Function.update_apply]
  norm_num
  rw [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, heq]
  ring

/-- Coordinate `2`'s pure-Continue payoff: colliding never happens (`2`
continues), so it is opponent `1`'s solo-quit contribution
(`r_2({1}) = 1`) plus the surviving-together mass times `tail`. -/
theorem continuePayoff_true (α : ℝ) (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootContinuePayoff (reward α) tail root true =
      (root false false).toReal * tail true + (root false true).toReal * 1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp only [Function.update_apply]
  norm_num
  rw [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward]
  ring

/-- Coordinate `1`'s pure-Continue payoff: opponent `2`'s solo-quit
contribution (`r_1({2}) = -1`) plus the surviving-together mass times
`tail`. -/
theorem continuePayoff_false (α : ℝ) (tail : Payoff Bool) (root : Bool → PMF Bool) :
    quittingRootContinuePayoff (reward α) tail root false =
      (root true false).toReal * tail false + (root true true).toReal * (-1) := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp only [Function.update_apply]
  norm_num
  rw [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward]
  ring

/-- Coordinate `2`'s deleted continue mass, forcing `2` to continue, is
exactly opponent `1`'s own continue probability. -/
theorem continueMass_true (root : Bool → PMF Bool) :
    quittingStationaryContinueMass (Function.update root true (PMF.pure false)) =
      (root false false).toReal := by
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply]
  simp [quittingAllContinueAction, Function.update_apply]

/-- Coordinate `1`'s deleted continue mass, forcing `1` to continue, is
exactly opponent `2`'s own continue probability. -/
theorem continueMass_false (root : Bool → PMF Bool) :
    quittingStationaryContinueMass (Function.update root false (PMF.pure false)) =
      (root true false).toReal := by
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply]
  simp [quittingAllContinueAction, Function.update_apply]

/-! ## The fixed-opponent closed forms along a sequence -/

/-- Coordinate `2`'s fixed-opponents quit value at `t` is opponent `1`'s
continue probability at `t`. -/
theorem fixedOpponentsQuitValue_true (α : ℝ) (x : ℕ → Bool → PMF Bool) (t : ℕ) :
    quittingFixedOpponentsQuitValue (reward α) x true t =
      (x t false false).toReal := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue (reward α) x true
    (0 : Payoff Bool) t]
  exact quitPayoff_true α 0 (x t)

/-- Coordinate `1`'s fixed-opponents quit value at `t` is the constant
`-α`. -/
theorem fixedOpponentsQuitValue_false (α : ℝ) (x : ℕ → Bool → PMF Bool) (t : ℕ) :
    quittingFixedOpponentsQuitValue (reward α) x false t = -α := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue (reward α) x false
    (0 : Payoff Bool) t]
  exact quitPayoff_false α 0 (x t)

/-- Coordinate `2`'s fixed-opponents continue reward at `t` is opponent
`1`'s quit probability at `t`. -/
theorem fixedOpponentsContinueReward_true (α : ℝ) (x : ℕ → Bool → PMF Bool) (t : ℕ) :
    quittingFixedOpponentsContinueReward (reward α) x true t =
      (x t false true).toReal := by
  have hbridge := quittingRootContinuePayoff_eq_fixedOpponents (reward α) x true
    (0 : Payoff Bool) t
  have hclosed := continuePayoff_true α (0 : Payoff Bool) (x t)
  rw [hbridge] at hclosed
  simpa using hclosed

/-- Coordinate `1`'s fixed-opponents continue reward at `t` is `-1` times
opponent `2`'s quit probability at `t`. -/
theorem fixedOpponentsContinueReward_false (α : ℝ) (x : ℕ → Bool → PMF Bool) (t : ℕ) :
    quittingFixedOpponentsContinueReward (reward α) x false t =
      -(x t true true).toReal := by
  have hbridge := quittingRootContinuePayoff_eq_fixedOpponents (reward α) x false
    (0 : Payoff Bool) t
  have hclosed := continuePayoff_false α (0 : Payoff Bool) (x t)
  rw [hbridge] at hclosed
  simpa using hclosed

/-- Coordinate `2`'s fixed-opponents continue mass at `t` is opponent `1`'s
continue probability at `t`. -/
theorem fixedOpponentsContinueMass_true (x : ℕ → Bool → PMF Bool) (t : ℕ) :
    quittingFixedOpponentsContinueMass x true t = (x t false false).toReal := by
  unfold quittingFixedOpponentsContinueMass
  exact continueMass_true (x t)

/-- Coordinate `1`'s fixed-opponents continue mass at `t` is opponent `2`'s
continue probability at `t`. -/
theorem fixedOpponentsContinueMass_false (x : ℕ → Bool → PMF Bool) (t : ℕ) :
    quittingFixedOpponentsContinueMass x false t = (x t true false).toReal := by
  unfold quittingFixedOpponentsContinueMass
  exact continueMass_false (x t)

/-! ## Deliverable 1 -/

/-- **Deliverable 1.**  Every jointly complementary sequence for the
candidate hard weight has coordinate `2` quitting with probability zero at
every time.  Route: `r_2({2}) = 1 > 0` forces total absorption from every
time (the general absorption theorem, applied at coordinate `2`); this pins
coordinate `1`'s next-stage tail value to the tight interval `[-1, -α]`.
Coordinate `1`'s own stage gap is then nonnegative unconditionally (from
that interval), so joint complementarity forces it to equal zero whenever
`1` does not quit for sure, and solving that equation forces coordinate
`2`'s own quit probability to `0`.  When `1` *does* quit for sure,
coordinate `2`'s own stage gap is exactly `-1`, forcing the same
conclusion directly. -/
theorem quitProbability_true_eq_zero_of_isQuittingJointComplementary
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (x : ℕ → Bool → PMF Bool)
    (hcomplementary : IsQuittingJointComplementary (reward α) x)
    (t : ℕ) :
    (x t true true).toReal = 0 := by
  have hsolo : 0 < reward α (quittingSingletonTerminal true) true := by
    rw [soloReward_true_true]; norm_num
  have hsurvival :=
    quittingJointSurvivalWeight_tendsto_zero_of_isQuittingJointComplementary_of_solo_pos
      (reward α) x hcomplementary true hsolo (t + 1)
  have hV1le : quittingComplementarityTailValue (reward α) x false (t + 1) ≤ -α :=
    quittingComplementarityTailValue_le_of_tendsto_zero (reward α) x false (t + 1) (-α)
      (reward_false_le α hα1) hsurvival
  have hleV1 : -1 ≤ quittingComplementarityTailValue (reward α) x false (t + 1) :=
    le_quittingComplementarityTailValue_of_tendsto_zero (reward α) x false (t + 1) (-1)
      (le_reward_false α hα1) hsurvival
  have hp2nonneg : 0 ≤ (x t true true).toReal := ENNReal.toReal_nonneg
  have hp1le1 : (x t false true).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _) |>.trans_eq (by norm_num)
  rcases eq_or_lt_of_le hp1le1 with hp1eq | hp1lt
  · -- Opponent `1` quits for sure at `t`: coordinate `2`'s stage gap is `-1`.
    have hsum1 := quittingRoot_continueProbability_add_quitProbability (x t) false
    have hc1 : (x t false false).toReal = 0 := by linarith
    have hgap : quittingComplementarityStageGap (reward α) x true t = -1 := by
      unfold quittingComplementarityStageGap
      rw [fixedOpponentsQuitValue_true, fixedOpponentsContinueReward_true,
        fixedOpponentsContinueMass_true, hc1, hp1eq]
      ring
    by_contra hne
    have hpos : 0 < (x t true true).toReal := lt_of_le_of_ne hp2nonneg (Ne.symm hne)
    have hge := (hcomplementary t true).1 hpos
    rw [hgap] at hge
    linarith
  · -- Opponent `1` does not quit for sure: coordinate `1`'s own stage gap
    -- vanishes, and solving that equation forces coordinate `2`'s quit
    -- probability to zero.
    have hsum2 := quittingRoot_continueProbability_add_quitProbability (x t) true
    have hc2eq : (x t true false).toReal = 1 - (x t true true).toReal := by linarith
    have hunfold : quittingComplementarityStageGap (reward α) x false t =
        -α + (x t true true).toReal -
          (x t true false).toReal *
            quittingComplementarityTailValue (reward α) x false (t + 1) := by
      unfold quittingComplementarityStageGap
      rw [fixedOpponentsQuitValue_false, fixedOpponentsContinueReward_false,
        fixedOpponentsContinueMass_false]
      ring
    have hgapnonneg : 0 ≤ quittingComplementarityStageGap (reward α) x false t := by
      rw [hunfold, hc2eq]
      nlinarith [mul_nonneg hp2nonneg (show (0:ℝ) ≤
        1 + quittingComplementarityTailValue (reward α) x false (t + 1) by linarith),
        hV1le]
    have hgapnonpos := (hcomplementary t false).2 hp1lt
    have hgapeq : quittingComplementarityStageGap (reward α) x false t = 0 := by linarith
    rw [hunfold, hc2eq] at hgapeq
    have hkey : (x t true true).toReal *
        (1 + quittingComplementarityTailValue (reward α) x false (t + 1)) =
        α + quittingComplementarityTailValue (reward α) x false (t + 1) := by nlinarith [hgapeq]
    have hprodnonneg : 0 ≤ (x t true true).toReal *
        (1 + quittingComplementarityTailValue (reward α) x false (t + 1)) :=
      mul_nonneg hp2nonneg (by linarith)
    have hprodnonpos : (x t true true).toReal *
        (1 + quittingComplementarityTailValue (reward α) x false (t + 1)) ≤ 0 := by
      rw [hkey]; linarith
    have hprodzero : (x t true true).toReal *
        (1 + quittingComplementarityTailValue (reward α) x false (t + 1)) = 0 :=
      le_antisymm hprodnonpos hprodnonneg
    have hV1ne1 : (1 : ℝ) +
        quittingComplementarityTailValue (reward α) x false (t + 1) ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hkey
      linarith [hkey, hzero]
    rcases mul_eq_zero.mp hprodzero with h | h
    · exact h
    · exact absurd h hV1ne1

end QuittingCandidateHardWeightCoordinateSilence

end GameTheory
