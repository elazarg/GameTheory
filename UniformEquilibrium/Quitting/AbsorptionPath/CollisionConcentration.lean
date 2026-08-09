/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.PMFProduct.CollisionMass
import Math.Probability.WeightedCollisionConcentration
import UniformEquilibrium.Quitting.AbsorptionPath.RealizedMarkedAbsorptionCylinder

/-!
# Collision concentration along finite quitting windows

This module connects the independent-product collision estimate to quitting
roots.  `quittingRootCollisionMass` is the exact one-stage probability of a
quitter set containing at least two players, expressed through the existing
`quittingRootCoalitionMass` semantics.

For a finite survival-weighted window whose one-stage absorption is at most
`rho`, conditional collision mass is at most

`choose (card ι) 2 * rho`.

The theorem separates the zero-absorption case, where collision mass is also
zero and no quotient is formed.  A companion estimate transfers this bound
to any bounded payoff decomposition into singleton and collision parts.
-/

noncomputable section

namespace GameTheory

open Math.PMFProduct Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One-stage probability of simultaneous quitting by at least two players. -/
def quittingRootCollisionMass (root : ι → PMF Bool) : ℝ :=
  collisionMass (quittingRootQuitRates root)

/-- Collision mass is exactly the sum of the existing product-law coalition
masses over quitter sets of cardinality at least two. -/
theorem quittingRootCollisionMass_eq_sum_coalitionMass
    (root : ι → PMF Bool) :
    quittingRootCollisionMass root =
      ∑ coalition ∈ Finset.univ.filter
          (fun coalition : Finset ι => 2 ≤ coalition.card),
        quittingRootCoalitionMass root coalition := by
  rfl

omit [DecidableEq ι] in
/-- The all-continue mass computed from quit rates agrees with the quitting
root's stationary all-Continue probability. -/
theorem continueMass_quittingRootQuitRates (root : ι → PMF Bool) :
    continueMass (quittingRootQuitRates root) =
      quittingStationaryContinueMass root := by
  classical
  rw [continueMass, quittingStationaryContinueMass_eq_prod_continueProbability]
  congr 1
  funext who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  change 1 - (root who true).toReal = (root who false).toReal
  linarith

omit [DecidableEq ι] in
/-- Root absorption is nonnegative. -/
theorem quittingRootAbsorptionMass_nonneg
    (root : ι → PMF Bool) :
    0 ≤ quittingRootAbsorptionMass root := by
  exact sub_nonneg.mpr (quittingStationaryContinueMass_le_one root)

/-- Root collision mass is nonnegative. -/
theorem quittingRootCollisionMass_nonneg
    (root : ι → PMF Bool) :
    0 ≤ quittingRootCollisionMass root := by
  apply collisionMass_nonneg
  · exact fun _ => ENNReal.toReal_nonneg
  · exact fun who => by
      unfold quittingRootQuitRates
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (root who) true)

/-- Sharp intermediate pair-union bound for a quitting root. -/
theorem quittingRootCollisionMass_le_pairMulSum
    (root : ι → PMF Bool) :
    quittingRootCollisionMass root ≤
      Math.pairMulSum (quittingRootQuitRates root) Finset.univ := by
  apply collisionMass_le_pairMulSum
  · exact fun _ => ENNReal.toReal_nonneg
  · exact fun who => by
      unfold quittingRootQuitRates
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (root who) true)

/-- Stagewise product-law collision estimate.  The constant is the number of
unordered pairs of players. -/
theorem quittingRootCollisionMass_le_choose_card_mul_absorption_sq
    (root : ι → PMF Bool) :
    quittingRootCollisionMass root ≤
      (Fintype.card ι).choose 2 * quittingRootAbsorptionMass root ^ 2 := by
  have h := collisionMass_le_choose_card_mul_absorption_sq
    (quittingRootQuitRates root)
    (fun _ => ENNReal.toReal_nonneg)
    (fun who => by
      unfold quittingRootQuitRates
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (root who) true))
  rw [continueMass_quittingRootQuitRates] at h
  simpa [quittingRootCollisionMass, quittingRootAbsorptionMass] using h

/-- A survival-weighted finite quitting window either has no absorption (and
hence no collision), or its conditional collision mass is at most
`choose (card ι) 2 * rho`.

The weight may be any nonnegative finite-window weight; in applications it
is the live mass before the corresponding row. -/
theorem finiteQuittingRootCollisionConcentration_or_zero
    {κ : Type} [Fintype κ]
    (weight : κ → ℝ) (roots : κ → ι → PMF Bool) (rho : ℝ)
    (hweight : ∀ phase, 0 ≤ weight phase)
    (hcap : ∀ phase, quittingRootAbsorptionMass (roots phase) ≤ rho) :
    ((∑ phase, weight phase * quittingRootAbsorptionMass (roots phase)) = 0 ∧
        (∑ phase, weight phase * quittingRootCollisionMass (roots phase)) = 0) ∨
      (0 < ∑ phase, weight phase * quittingRootAbsorptionMass (roots phase) ∧
        (∑ phase, weight phase * quittingRootCollisionMass (roots phase)) /
            (∑ phase, weight phase * quittingRootAbsorptionMass (roots phase)) ≤
          (Fintype.card ι).choose 2 * rho) := by
  let absorption : κ → ℝ := fun phase =>
    quittingRootAbsorptionMass (roots phase)
  let collision : κ → ℝ := fun phase =>
    quittingRootCollisionMass (roots phase)
  have h := finiteWeightedCollisionConcentration_or_zero (κ := κ)
    weight absorption collision ((Fintype.card ι).choose 2 : ℝ) rho
    hweight
    (fun phase => quittingRootAbsorptionMass_nonneg (roots phase))
    (fun phase => quittingRootCollisionMass_nonneg (roots phase))
    (Nat.cast_nonneg _) hcap
    (fun phase => by
      simpa [absorption, collision] using
        quittingRootCollisionMass_le_choose_card_mul_absorption_sq
          (roots phase))
  exact h

/-- Payoff consequence of finite-window collision concentration.  The full
absorbing contribution is split into singleton contribution `X` and
collision contribution `b`; `S` is singleton mass.  If both reward parts are
bounded by `M` times their corresponding masses, the conditional payoff is
within `2 * M * choose (card ι) 2 * rho` of the normalized singleton
mixture. -/
theorem abs_finiteQuittingRootConditionalPayoff_sub_singletonMixture_le
    {κ : Type} [Fintype κ]
    (weight : κ → ℝ) (roots : κ → ι → PMF Bool) (rho : ℝ)
    {S X b actual mixture M : ℝ}
    (hweight : ∀ phase, 0 ≤ weight phase)
    (hcap : ∀ phase, quittingRootAbsorptionMass (roots phase) ≤ rho)
    (hdecomposition :
      (∑ phase, weight phase * quittingRootAbsorptionMass (roots phase)) =
        S + ∑ phase, weight phase * quittingRootCollisionMass (roots phase))
    (habsorption :
      0 < ∑ phase, weight phase * quittingRootAbsorptionMass (roots phase))
    (hsingleton : 0 < S) (hM : 0 ≤ M)
    (hX : |X| ≤ M * S)
    (hb : |b| ≤ M *
      ∑ phase, weight phase * quittingRootCollisionMass (roots phase))
    (hactual : actual =
      (X + b) /
        ∑ phase, weight phase * quittingRootAbsorptionMass (roots phase))
    (hmixture : mixture = X / S) :
    |actual - mixture| ≤
      2 * M * ((Fintype.card ι).choose 2 * rho) := by
  have hconcentration := finiteQuittingRootCollisionConcentration_or_zero
    weight roots rho hweight hcap
  rcases hconcentration with hzero | hpositive
  · linarith [hzero.1]
  · have happrox := abs_conditionalPayoff_sub_singletonMixture_le
      hdecomposition habsorption hsingleton
      (Finset.sum_nonneg fun phase _ =>
        mul_nonneg (hweight phase)
          (quittingRootCollisionMass_nonneg (roots phase)))
      hM hX hb hactual hmixture
    calc
      |actual - mixture| ≤
          2 * M *
              (∑ phase, weight phase *
                quittingRootCollisionMass (roots phase)) /
            (∑ phase, weight phase *
              quittingRootAbsorptionMass (roots phase)) := happrox
      _ = 2 * M *
          ((∑ phase, weight phase *
              quittingRootCollisionMass (roots phase)) /
            (∑ phase, weight phase *
              quittingRootAbsorptionMass (roots phase))) := by ring
      _ ≤ 2 * M * ((Fintype.card ι).choose 2 * rho) := by
        exact mul_le_mul_of_nonneg_left hpositive.2
          (mul_nonneg (by norm_num) hM)

end GameTheory
