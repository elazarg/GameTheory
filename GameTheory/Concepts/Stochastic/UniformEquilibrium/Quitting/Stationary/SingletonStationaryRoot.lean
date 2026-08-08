/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Circulation.SingletonFlowMesh
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback

/-!
# Stationary singleton roots for subdivision meshes

This file connects the scalar singleton-flow mesh algebra to actual product
roots of a quitting game.  At a root where only `owner` quits, the prescribed
Bellman equation is the singleton arc mixture.  If another player quits, the
only two outcomes are that player's singleton and a collision with `owner`;
this gives exactly the local `h * (collision - solo)⁺` error used by the
cyclic supersolution compiler.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The inactive player's Quit endpoint -/

/-- Pure action where `other` quits and `owner`'s action is supplied
separately. -/
def quittingSingletonPairAction
    (owner other : ι) (ownerQuits : Bool) : ι → Bool :=
  Function.update (quittingSoloAction owner ownerQuits) other true

omit [Fintype ι] in
@[simp] theorem quittingSingletonPairAction_false
    (owner other : ι) :
    quittingSingletonPairAction owner other false =
      quittingSoloAction other true := by
  funext player
  by_cases hp : player = other
  · subst player
    simp [quittingSingletonPairAction, quittingSoloAction]
  · simp [quittingSingletonPairAction, quittingSoloAction, hp]

@[simp] theorem quittingQuitters_singletonPairAction_true
    {owner other : ι} (hne : other ≠ owner) :
    quittingQuitters (quittingSingletonPairAction owner other true) =
      {owner, other} := by
  ext player
  by_cases hpOwner : player = owner
  · subst player
    simp [quittingSingletonPairAction, quittingSoloAction,
      quittingQuitters, hne.symm]
  by_cases hpOther : player = other
  · subst player
    simp [quittingSingletonPairAction, quittingSoloAction,
      quittingQuitters]
  · simp [quittingSingletonPairAction, quittingSoloAction,
      quittingQuitters, hpOwner, hpOther]

/-- Payoff to `other` when `owner` and `other` quit together. -/
def quittingSingletonCollisionReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner other : ι) : ℝ :=
  reward ⟨{owner, other}, by simp⟩ other

theorem quittingRootPayoff_singletonPairAction_true
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) :
    quittingRootPayoff reward (0 : Payoff ι)
        (quittingSingletonPairAction owner other true) other =
      quittingSingletonCollisionReward reward owner other := by
  have hnonempty :
      (quittingQuitters
        (quittingSingletonPairAction owner other true)).Nonempty := by
    rw [quittingQuitters_singletonPairAction_true hne]
    simp
  unfold quittingRootPayoff quittingSingletonCollisionReward
  rw [dif_pos hnonempty]
  congr
  exact quittingQuitters_singletonPairAction_true hne

/-- Product law when `other` quits surely against a singleton root. -/
theorem pmfPi_update_quittingSoloStationaryRoot_other_true
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool) :
    pmfPi (Function.update
        (quittingSoloStationaryRoot owner hazard) other (PMF.pure true)) =
      hazard.bind (fun ownerQuits ↦
        PMF.pure
          (quittingSingletonPairAction owner other ownerQuits)) := by
  unfold quittingSoloStationaryRoot
  rw [Function.update_comm (f := fun _ : ι ↦ PMF.pure false)
      (a := owner) (b := other) hne.symm hazard (PMF.pure true),
    pmfPi_update_bind]
  apply congrArg (PMF.bind hazard)
  funext ownerQuits
  have hpure :
      Function.update
          (Function.update (fun _ : ι ↦ PMF.pure false)
            other (PMF.pure true)) owner (PMF.pure ownerQuits) =
        fun player ↦ PMF.pure
          (quittingSingletonPairAction owner other ownerQuits player) := by
    funext player
    by_cases hpOwner : player = owner
    · subst player
      simp [quittingSingletonPairAction, quittingSoloAction,
        hne.symm]
    by_cases hpOther : player = other
    · subst player
      simp [quittingSingletonPairAction, quittingSoloAction, hne]
    · simp [quittingSingletonPairAction, quittingSoloAction,
        hpOwner, hpOther]
  rw [hpure, pmfPi_pure]

/-- Exact inactive-Quit mixture: with probability `owner` continues, `other`
quits alone; with the complementary probability they collide. -/
theorem quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool) :
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingSoloStationaryRoot owner hazard) other =
      (hazard false).toReal * quittingSoloReward reward other other +
        (hazard true).toReal *
          quittingSingletonCollisionReward reward owner other := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue
    quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [pmfPi_update_quittingSoloStationaryRoot_other_true hne,
    expect_bind]
  simp only [expect_pure]
  rw [expect_eq_sum, Fintype.sum_bool,
    quittingSingletonPairAction_false]
  have hsolo : quittingRootPayoff reward (0 : Payoff ι)
      (quittingSoloAction other true) other =
        quittingSoloReward reward other other := by
    unfold quittingRootPayoff quittingSoloReward
    simp
  rw [hsolo, quittingRootPayoff_singletonPairAction_true reward hne]
  ring

/-! ## Prescribed singleton Bellman mixture -/

/-- A singleton stationary root mixes its singleton reward and its declared
all-continue successor with the owner's two action probabilities. -/
theorem quittingRootSuccessorPayoff_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) (next : Payoff ι) :
    quittingRootSuccessorPayoff reward next
        (quittingSoloStationaryRoot owner hazard) =
      fun who ↦
        (hazard true).toReal * quittingSoloReward reward owner who +
          (hazard false).toReal * next who := by
  funext who
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_solo,
    quittingStationaryContinueMass_solo]

/-! ## One subdivided stationary-root certificate -/

/-- Boolean law that quits with probability `h`. -/
def quittingHazardCoin (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : PMF Bool :=
  PMF.ofFintype
    (fun quit ↦ if quit then ENNReal.ofReal h else ENNReal.ofReal (1 - h))
    (by
      rw [Fintype.sum_bool]
      simp only [if_true, if_false, Bool.false_eq_true]
      rw [← ENNReal.ofReal_add hh0 (by linarith)]
      norm_num)

@[simp] theorem quittingHazardCoin_true_toReal
    (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    (quittingHazardCoin h hh0 hh1 true).toReal = h := by
  simp [quittingHazardCoin, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal hh0]

@[simp] theorem quittingHazardCoin_false_toReal
    (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    (quittingHazardCoin h hh0 hh1 false).toReal = 1 - h := by
  simp [quittingHazardCoin, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hh1)]

/-- The rpow subdivision hazard is strictly below one whenever its coarse
hazard is strictly below one. -/
theorem quittingMeshHazard_lt_one {p : ℝ} (hp1 : p < 1) (m : ℕ) :
    quittingMeshHazard p m < 1 := by
  unfold quittingMeshHazard
  have hpositive := Real.rpow_pos_of_pos (sub_pos.mpr hp1)
    ((m : ℝ)⁻¹ : ℝ)
  linarith

/-- Bernoulli realization of the logarithmically subdivided hazard. -/
def quittingMeshHazardCoin
    (p : ℝ) (m : ℕ) (hp0 : 0 ≤ p) (hp1 : p < 1) : PMF Bool :=
  quittingHazardCoin (quittingMeshHazard p m)
    (quittingMeshHazard_nonneg m hp0 hp1.le)
    (quittingMeshHazard_le_one m hp1.le)

@[simp] theorem quittingMeshHazardCoin_true_toReal
    (p : ℝ) (m : ℕ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (quittingMeshHazardCoin p m hp0 hp1 true).toReal =
      quittingMeshHazard p m := by
  simp [quittingMeshHazardCoin]

@[simp] theorem quittingMeshHazardCoin_false_toReal
    (p : ℝ) (m : ℕ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (quittingMeshHazardCoin p m hp0 hp1 false).toReal =
      1 - quittingMeshHazard p m := by
  simp [quittingMeshHazardCoin]

/-- A single stationary singleton-root microstage supplies all three inputs
of the quit-only cyclic supersolution compiler.

The prescribed root equation and every prescribed-Continue equation are
exact.  The active coordinate is exact because it is constant along the arc.
For an inactive player, the only Quit loss is `h` times the positive surplus
of colliding with the active owner over quitting alone. -/
theorem singletonStationaryRoot_interpolant_certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) {h : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h < 1)
    (htrue : (hazard true).toReal = h)
    (hfalse : (hazard false).toReal = 1 - h)
    (root start : Payoff ι) (k : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hroot : root = quittingSoloReward reward owner)
    (hactive : start owner = root owner)
    (hsolo : ∀ who,
      quittingSoloReward reward who who ≤
        quittingMeshPayoffInterpolant root start (1 - h) k who)
    (hcollision : ∀ other, other ≠ owner →
      max (quittingSingletonCollisionReward reward owner other -
        quittingSoloReward reward other other) 0 ≤ D) :
    let current := quittingMeshPayoffInterpolant root start (1 - h) k
    let next := quittingMeshPayoffInterpolant root start (1 - h) (k + 1)
    current = quittingRootSuccessorPayoff reward next
        (quittingSoloStationaryRoot owner hazard) ∧
      (∀ who,
        quittingStationaryFixedOpponentsContinueReward reward
              (quittingSoloStationaryRoot owner hazard) who +
            quittingStationaryFixedOpponentsContinueMass
                (quittingSoloStationaryRoot owner hazard) who * next who =
          current who) ∧
      ∀ who,
        quittingStationaryFixedOpponentsQuitValue reward
            (quittingSoloStationaryRoot owner hazard) who ≤
          current who + D * h := by
  dsimp only
  have ha : 1 - h ≠ 0 := by linarith
  have hstep :
      quittingMeshPayoffInterpolant root start (1 - h) k =
        fun who ↦ h * root who +
          (1 - h) *
            quittingMeshPayoffInterpolant root start (1 - h) (k + 1) who := by
    rw [quittingMeshPayoffInterpolant_eq_mix_succ ha]
    funext who
    ring
  constructor
  · rw [quittingRootSuccessorPayoff_solo, htrue, hfalse]
    rw [← hroot]
    exact hstep
  constructor
  · intro who
    by_cases howner : who = owner
    · subst who
      rw [quittingStationaryFixedOpponentsContinueReward_solo_owner,
        quittingStationaryFixedOpponentsContinueMass_solo_owner]
      have hcurrent := quittingMeshPayoffInterpolant_eq_root_of_eq
        (a := 1 - h) hactive k
      have hnext := quittingMeshPayoffInterpolant_eq_root_of_eq
        (a := 1 - h) hactive (k + 1)
      rw [hcurrent, hnext]
      ring
    · rw [quittingStationaryFixedOpponentsContinueReward_solo_other
          reward howner hazard,
        quittingStationaryFixedOpponentsContinueMass_solo_other
          howner hazard,
        htrue, hfalse]
      rw [← hroot]
      exact (congrFun hstep who).symm
  · intro who
    by_cases howner : who = owner
    · subst who
      rw [quittingStationaryFixedOpponentsQuitValue_solo_owner]
      have hcurrent := quittingMeshPayoffInterpolant_eq_root_of_eq
        (a := 1 - h) hactive k
      rw [hcurrent, ← congrFun hroot owner]
      exact le_add_of_nonneg_right (mul_nonneg hD hh0)
    · rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
          reward howner hazard,
        htrue, hfalse]
      have hlocal := singletonQuitMix_le_value_add_hazard_mul
        hh0 (hsolo who) (hcollision who howner)
      calc
        (1 - h) * quittingSoloReward reward who who +
              h * quittingSingletonCollisionReward reward owner who ≤
            quittingMeshPayoffInterpolant root start (1 - h) k who +
              h * D := hlocal
        _ = quittingMeshPayoffInterpolant root start (1 - h) k who +
              D * h := by ring

/-- Rpow-instantiated form of
`singletonStationaryRoot_interpolant_certificate`.  No abstract probability
law remains: the owner's stationary marginal is the Bernoulli law with
hazard `1 - (1-p)^(1/m)`. -/
theorem singletonMeshStationaryRoot_interpolant_certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {p : ℝ} (m : ℕ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (root start : Payoff ι) (k : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hroot : root = quittingSoloReward reward owner)
    (hactive : start owner = root owner)
    (hsolo : ∀ who,
      quittingSoloReward reward who who ≤
        quittingMeshPayoffInterpolant root start
          (1 - quittingMeshHazard p m) k who)
    (hcollision : ∀ other, other ≠ owner →
      max (quittingSingletonCollisionReward reward owner other -
        quittingSoloReward reward other other) 0 ≤ D) :
    let current := quittingMeshPayoffInterpolant root start
      (1 - quittingMeshHazard p m) k
    let next := quittingMeshPayoffInterpolant root start
      (1 - quittingMeshHazard p m) (k + 1)
    current = quittingRootSuccessorPayoff reward next
        (quittingSoloStationaryRoot owner
          (quittingMeshHazardCoin p m hp0 hp1)) ∧
      (∀ who,
        quittingStationaryFixedOpponentsContinueReward reward
              (quittingSoloStationaryRoot owner
                (quittingMeshHazardCoin p m hp0 hp1)) who +
            quittingStationaryFixedOpponentsContinueMass
                (quittingSoloStationaryRoot owner
                  (quittingMeshHazardCoin p m hp0 hp1)) who * next who =
          current who) ∧
      ∀ who,
        quittingStationaryFixedOpponentsQuitValue reward
            (quittingSoloStationaryRoot owner
              (quittingMeshHazardCoin p m hp0 hp1)) who ≤
          current who + D * quittingMeshHazard p m := by
  exact singletonStationaryRoot_interpolant_certificate
    reward owner (quittingMeshHazardCoin p m hp0 hp1)
    (quittingMeshHazard_nonneg m hp0 hp1.le)
    (quittingMeshHazard_lt_one hp1 m)
    (quittingMeshHazardCoin_true_toReal p m hp0 hp1)
    (quittingMeshHazardCoin_false_toReal p m hp0 hp1)
    root start k hD hroot hactive hsolo hcollision

end GameTheory
