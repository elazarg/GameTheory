/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ThreePlayer.SingletonAlternative
import UniformEquilibrium.Quitting.Classification.ThreePlayer.SingletonMixtureCompiler
import UniformEquilibrium.Quitting.Classification.ThreePlayer.CyclicCompiler

/-!
# Dispatching a three-player singleton source packet

This module is the semantic adapter between the analytic packet and the finite
three-by-three alternative.  The support-sensitive diagonal hypothesis is
important: only owners occurring in the source packet are initially known to
be pinned.  The finite alternative preserves that fact in its complementary
output and records a full zero diagonal in either strict-cycle output.
-/

noncomputable section

namespace GameTheory

open StochasticGame

/-- The three singleton payoff columns of a quitting reward. -/
def threeSingletonTable (reward : QuittingReward3) :
    ThreePlayer → ThreePlayer → ℝ :=
  fun owner who => reward (quittingSingletonTerminal owner) who

@[simp] theorem singletonMixed_threeSingletonTable
    (reward : QuittingReward3) (nu : ThreePlayer → ℝ) :
    singletonMixed (threeSingletonTable reward) nu =
      quittingSingletonMixture reward nu := by
  funext who
  rfl

/-- A normalized feasible singleton source packet satisfies the excess-matrix
feasibility inequalities. -/
theorem threeMixed_singletonExcess_nonneg
    (reward : QuittingReward3) (target : Payoff ThreePlayer)
    (mu : ThreePlayer → ℝ) (hmu : ThreeProbability mu)
    (hmix : ∀ who, target who ≤ quittingSingletonMixture reward mu who) :
    ∀ who, 0 ≤ threeMixed
      (singletonExcess (threeSingletonTable reward) target) mu who := by
  intro who
  have hsum :
      threeMixed (singletonExcess (threeSingletonTable reward) target) mu who =
        quittingSingletonMixture reward mu who - target who := by
    unfold threeMixed singletonExcess threeSingletonTable
      quittingSingletonMixture
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hmu.total]
    simp only [mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  exact sub_nonneg.mpr (hmix who)

/-- Source-owner pinning is precisely the active zero-diagonal condition for
the singleton excess matrix. -/
theorem singletonExcess_active_diagonal
    (reward : QuittingReward3) (target : Payoff ThreePlayer)
    (mu : ThreePlayer → ℝ)
    (hpin : ∀ who, 0 < mu who →
      target who = reward (quittingSingletonTerminal who) who) :
    ∀ who, 0 < mu who →
      singletonExcess (threeSingletonTable reward) target who who = 0 := by
  intro who hwho
  unfold singletonExcess threeSingletonTable
  rw [← hpin who hwho]
  ring

private theorem rightCycle_of_excess
    (reward : QuittingReward3) (target : Payoff ThreePlayer)
    (c : ThreeRightStrictCycle
      (singletonExcess (threeSingletonTable reward) target)) :
    RightSingletonCycle reward := by
  have hd0 := c.diagonal 0
  have hd1 := c.diagonal 1
  have hd2 := c.diagonal 2
  have hc01 := c.h01
  have hc02 := c.h02
  have hc10 := c.h10
  have hc12 := c.h12
  have hc20 := c.h20
  have hc21 := c.h21
  have hp :
      quittingSoloReward reward 0 0 - quittingSoloReward reward 1 0 = c.p := by
    change quittingSoloReward reward 1 0 - target 0 = -c.p at hc01
    change quittingSoloReward reward 0 0 - target 0 = 0 at hd0
    linarith
  have hq :
      quittingSoloReward reward 2 0 - quittingSoloReward reward 0 0 = c.q := by
    change quittingSoloReward reward 2 0 - target 0 = c.q at hc02
    change quittingSoloReward reward 0 0 - target 0 = 0 at hd0
    linarith
  have hr :
      quittingSoloReward reward 1 1 - quittingSoloReward reward 2 1 = c.r := by
    change quittingSoloReward reward 2 1 - target 1 = -c.r at hc12
    change quittingSoloReward reward 1 1 - target 1 = 0 at hd1
    linarith
  have hs :
      quittingSoloReward reward 0 1 - quittingSoloReward reward 1 1 = c.s := by
    change quittingSoloReward reward 0 1 - target 1 = c.s at hc10
    change quittingSoloReward reward 1 1 - target 1 = 0 at hd1
    linarith
  have ht :
      quittingSoloReward reward 2 2 - quittingSoloReward reward 0 2 = c.t := by
    change quittingSoloReward reward 0 2 - target 2 = -c.t at hc20
    change quittingSoloReward reward 2 2 - target 2 = 0 at hd2
    linarith
  have hu :
      quittingSoloReward reward 1 2 - quittingSoloReward reward 2 2 = c.u := by
    change quittingSoloReward reward 1 2 - target 2 = c.u at hc21
    change quittingSoloReward reward 2 2 - target 2 = 0 at hd2
    linarith
  refine {
    h01 := ?_
    h02 := ?_
    h21 := ?_
    h10 := ?_
    h02' := ?_
    h12 := ?_
    hdet := ?_ }
  · linarith [hp, c.hp]
  · linarith [hq, c.hq]
  · linarith [hr, c.hr]
  · linarith [hs, c.hs]
  · linarith [ht, c.ht]
  · linarith [hu, c.hu]
  · rw [hq, hs, hu, hp, hr, ht]
    linarith [c.determinant]

private theorem leftCycle_of_excess
    (reward : QuittingReward3) (target : Payoff ThreePlayer)
    (c : ThreeLeftStrictCycle
      (singletonExcess (threeSingletonTable reward) target)) :
    LeftSingletonCycle reward := by
  have hd0 := c.diagonal 0
  have hd1 := c.diagonal 1
  have hd2 := c.diagonal 2
  have hc01 := c.h01
  have hc02 := c.h02
  have hc10 := c.h10
  have hc12 := c.h12
  have hc20 := c.h20
  have hc21 := c.h21
  have hp :
      quittingSoloReward reward 1 0 - quittingSoloReward reward 0 0 = c.p := by
    change quittingSoloReward reward 1 0 - target 0 = c.p at hc01
    change quittingSoloReward reward 0 0 - target 0 = 0 at hd0
    linarith
  have hq :
      quittingSoloReward reward 0 0 - quittingSoloReward reward 2 0 = c.q := by
    change quittingSoloReward reward 2 0 - target 0 = -c.q at hc02
    change quittingSoloReward reward 0 0 - target 0 = 0 at hd0
    linarith
  have hr :
      quittingSoloReward reward 2 1 - quittingSoloReward reward 1 1 = c.r := by
    change quittingSoloReward reward 2 1 - target 1 = c.r at hc12
    change quittingSoloReward reward 1 1 - target 1 = 0 at hd1
    linarith
  have hs :
      quittingSoloReward reward 1 1 - quittingSoloReward reward 0 1 = c.s := by
    change quittingSoloReward reward 0 1 - target 1 = -c.s at hc10
    change quittingSoloReward reward 1 1 - target 1 = 0 at hd1
    linarith
  have ht :
      quittingSoloReward reward 0 2 - quittingSoloReward reward 2 2 = c.t := by
    change quittingSoloReward reward 0 2 - target 2 = c.t at hc20
    change quittingSoloReward reward 2 2 - target 2 = 0 at hd2
    linarith
  have hu :
      quittingSoloReward reward 2 2 - quittingSoloReward reward 1 2 = c.u := by
    change quittingSoloReward reward 1 2 - target 2 = -c.u at hc21
    change quittingSoloReward reward 2 2 - target 2 = 0 at hd2
    linarith
  refine {
    h00 := ?_
    h01 := ?_
    h10 := ?_
    h11 := ?_
    h20 := ?_
    h21 := ?_
    hdet := ?_ }
  · linarith [hq, c.hq]
  · linarith [hp, c.hp]
  · linarith [hs, c.hs]
  · linarith [hr, c.hr]
  · linarith [hu, c.hu]
  · linarith [ht, c.ht]
  · rw [hp, ht, hr, hq, hu, hs]
    linarith [c.determinant]

/-- **Finite singleton dispatch.**  Every three-player singleton source
packet satisfying the rationality and punishment floors compiles to an
ordinary uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_threeSingletonSource
    (reward : QuittingReward3) (target : Payoff ThreePlayer)
    (mu : ThreePlayer → ℝ)
    (hmu : ThreeProbability mu)
    (hmix : ∀ who, target who ≤ quittingSingletonMixture reward mu who)
    (hsourcePin : ∀ who, 0 < mu who →
      target who = reward (quittingSingletonTerminal who) who)
    (hsolo : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ target who)
    (hpunishment : ∀ who,
      quittingPunishmentValue reward who ≤ target who) :
    ∃ payoff : Payoff ThreePlayer,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let M := singletonExcess (threeSingletonTable reward) target
  have hfeas : ∀ who, 0 ≤ threeMixed M mu who := by
    exact threeMixed_singletonExcess_nonneg reward target mu hmu hmix
  have hactive : ∀ who, 0 < mu who → M who who = 0 := by
    exact singletonExcess_active_diagonal reward target mu hsourcePin
  have halt := three_singleton_source_alternative M mu hmu hfeas hactive
  cases halt with
  | complementary c =>
      have packet := complementary_of_excess_certificate
        (threeSingletonTable reward) target c
      apply exists_uniformEquilibriumPayoff_of_complementarySingletonMixture
        reward packet.mass target
      · exact packet.probability.nonneg
      · exact packet.probability.total
      · intro who
        simpa [singletonMixed_threeSingletonTable] using
          packet.mixed_ge_target who
      · intro who hwho
        simpa [singletonMixed_threeSingletonTable, threeSingletonTable] using
          packet.active_pins who hwho
      · exact hsolo
      · exact hpunishment
  | right c =>
      exact ⟨rightCoarse reward 0,
        rightSingletonCycle_isUniformEquilibriumPayoff reward
          (rightCycle_of_excess reward target c)⟩
  | left c =>
      exact ⟨leftCoarse reward 0,
        leftSingletonCycle_isUniformEquilibriumPayoff reward
          (leftCycle_of_excess reward target c)⟩

end GameTheory
