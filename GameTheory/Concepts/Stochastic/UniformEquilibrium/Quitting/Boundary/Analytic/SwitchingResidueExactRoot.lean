/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Stationary.EndpointCompiler
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Analytic.SwitchingResidueRegressionBridge

/-!
# Exact stationary solutions of the switching-residue regression table

`QuittingSwitchingResidueRegression` defines the `L = 0` member of the
parametric family in `QuittingLocalMechanismResidueWitness`.  The table is not
zero-solo, has no sure exit set, has no one-owner stationary repair, and
defeats every fixed sure-blocker collision repair.  This module gives its
exact stationary solutions.

It has two distinct exact stationary solutions.

* `residueRoot = (1, 2/7, 1)` has two sure quitters.  Its displayed value is
  `residueValue = (5/7, 0, 2/7)`, its Quit-minus-Continue vector is
  `(1/7, 0, 0)`, and every playerwise opponent survival mass is zero.
* `enlargedRoot = (1/2, 1, 1/3)` is the support-enlarged two-owner row.  Its
  displayed value is `enlargedValue = (2/3, 1/2, 1/2)`, its endpoint vector is
  `(0, 1/5, 0)`, and its playerwise opponent survival masses are
  `(0, 1/3, 0)`.

Both rows are absorbing fixed points and exact endpoint Nash.  The general
stationary endpoint compiler therefore proves that their stationary profiles
are exact terminal Nash against all behavioral deviations, that their exact
behavioral caps equal their displayed values, and that both displayed vectors
are uniform-equilibrium payoffs.

The capstone combines this with the no-sure-exit theorem.  Thus
failure of the local branch map on this table is not equilibrium nonexistence:
the table has no sure exit set and nevertheless has two distinct exact
stationary uniform-equilibrium payoffs.
-/

noncomputable section

namespace GameTheory
namespace QuittingSwitchingResidueExactRoot

open StochasticGame Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction
open QuittingSwitchingResidueRegression
open QuittingSwitchingResidueRegressionBridge

/-! ## Boolean coins and a three-coordinate product expansion -/

/-- Quit with probability `2/7`. -/
def twoSeventhsCoin : PMF Bool :=
  quittingHazardCoin (2 / 7) (by norm_num) (by norm_num)

/-- Quit with probability `1/2`. -/
def halfCoin : PMF Bool :=
  quittingHazardCoin (1 / 2) (by norm_num) (by norm_num)

/-- Quit with probability `1/3`. -/
def thirdCoin : PMF Bool :=
  quittingHazardCoin (1 / 3) (by norm_num) (by norm_num)

@[simp] theorem twoSeventhsCoin_true_toReal :
    (twoSeventhsCoin true).toReal = 2 / 7 := by
  norm_num [twoSeventhsCoin]

@[simp] theorem twoSeventhsCoin_false_toReal :
    (twoSeventhsCoin false).toReal = 5 / 7 := by
  norm_num [twoSeventhsCoin]

@[simp] theorem halfCoin_true_toReal :
    (halfCoin true).toReal = 1 / 2 := by
  norm_num [halfCoin]

@[simp] theorem halfCoin_false_toReal :
    (halfCoin false).toReal = 1 / 2 := by
  norm_num [halfCoin]

@[simp] theorem thirdCoin_true_toReal :
    (thirdCoin true).toReal = 1 / 3 := by
  norm_num [thirdCoin]

@[simp] theorem thirdCoin_false_toReal :
    (thirdCoin false).toReal = 2 / 3 := by
  norm_num [thirdCoin]

@[simp] theorem expect_twoSeventhsCoin (f : Bool → ℝ) :
    expect twoSeventhsCoin f =
      2 / 7 * f true + 5 / 7 * f false := by
  rw [expect_eq_sum, Fintype.sum_bool,
    twoSeventhsCoin_true_toReal, twoSeventhsCoin_false_toReal]

@[simp] theorem expect_halfCoin (f : Bool → ℝ) :
    expect halfCoin f = 1 / 2 * f true + 1 / 2 * f false := by
  rw [expect_eq_sum, Fintype.sum_bool,
    halfCoin_true_toReal, halfCoin_false_toReal]

@[simp] theorem expect_thirdCoin (f : Bool → ℝ) :
    expect thirdCoin f = 1 / 3 * f true + 2 / 3 * f false := by
  rw [expect_eq_sum, Fintype.sum_bool,
    thirdCoin_true_toReal, thirdCoin_false_toReal]

/-- Fubini expansion of a product of three Boolean marginals. -/
theorem expect_pmfPi_fin3_bool (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) fun a ↦
        expect (sigma 1) fun b ↦
          expect (sigma 2) fun d ↦ f ![a, b, d] := by
  classical
  have h0 : Function.update sigma 0 (sigma 0) = sigma :=
    Function.update_eq_self 0 sigma
  rw [← h0, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 0))
  funext a
  have h1 : Function.update (Function.update sigma 0 (PMF.pure a)) 1 (sigma 1) =
      Function.update sigma 0 (PMF.pure a) := by
    funext who
    fin_cases who <;> simp
  rw [← h1, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 1))
  funext b
  have h2 : Function.update
      (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
      2 (sigma 2) =
      Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b) := by
    funext who
    fin_cases who <;> simp
  rw [← h2, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 2))
  funext d
  have hpure : Function.update
      (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
      2 (PMF.pure d) = fun who ↦ PMF.pure (![a, b, d] who) := by
    funext who
    fin_cases who <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

/-- The one-stage payoff of the regression table, with the quitter-set
presentation exposed. -/
theorem quittingRootPayoff_gameReward
    (tail : Payoff Player) (action : Player → Bool) (who : Player) :
    quittingRootPayoff gameReward tail action who =
      if (quittingQuitters action).Nonempty then
        QuittingSwitchingResidueRegression.reward
          (quittingQuitters action) who
      else tail who := by
  unfold quittingRootPayoff
  by_cases h : (quittingQuitters action).Nonempty
  · rw [dif_pos h, if_pos h]
    rfl
  · rw [dif_neg h, if_neg h]

/-- A displayed three-coordinate action row has a quitter exactly when one of
its coordinates is `true`. -/
theorem quittingQuitters_vec_nonempty (a b d : Bool) :
    (quittingQuitters ![a, b, d]).Nonempty ↔
      a = true ∨ b = true ∨ d = true := by
  constructor
  · rintro ⟨who, hwho⟩
    fin_cases who <;> simp_all [quittingQuitters]
  · rintro (ha | hb | hd)
    · exact ⟨0, by simp [quittingQuitters, ha]⟩
    · exact ⟨1, by simp [quittingQuitters, hb]⟩
    · exact ⟨2, by simp [quittingQuitters, hd]⟩

/-- The one-stage payoff of the regression table on an explicit Boolean row. -/
@[simp] theorem quittingRootPayoff_gameReward_vec
    (tail : Payoff Player) (a b d : Bool) (who : Player) :
    quittingRootPayoff gameReward tail ![a, b, d] who =
      if a || b || d then
        QuittingSwitchingResidueRegression.reward
          (quittingQuitters ![a, b, d]) who
      else tail who := by
  rw [quittingRootPayoff_gameReward]
  refine if_congr ?_ rfl rfl
  rw [quittingQuitters_vec_nonempty]
  cases a <;> cases b <;> cases d <;> simp

/-! ## The two-sure-quitter root `(1, 2/7, 1)` -/

/-- Players `0` and `2` quit surely; player `1` quits with probability `2/7`. -/
def residueRoot : Player → PMF Bool :=
  ![PMF.pure true, twoSeventhsCoin, PMF.pure true]

/-- The root's exact value. -/
def residueValue : Payoff Player :=
  ![(5 / 7 : ℝ), 0, 2 / 7]

/-- The root absorbs immediately, so its successor payoff is independent of
the supplied all-Continue continuation. -/
theorem quittingRootSuccessorPayoff_residueRoot (tail : Payoff Player) :
    quittingRootSuccessorPayoff gameReward tail residueRoot = residueValue := by
  funext who
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [residueRoot, residueValue, QuittingSwitchingResidueRegression.reward,
      quittingQuitters, Matrix.cons_val_two]

/-- Quit minus Continue is `(1/7, 0, 0)`. -/
theorem quittingRootEndpointDifference_residueRoot (who : Player) :
    quittingRootEndpointDifference gameReward residueValue residueRoot who =
      ![(1 / 7 : ℝ), 0, 0] who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool, expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [residueRoot, residueValue, QuittingSwitchingResidueRegression.reward,
      quittingQuitters, Matrix.cons_val_two]
  grind only

/-- The row is exact endpoint Nash: the only positive endpoint difference is
at player `0`, who quits surely. -/
theorem isZeroEndpointNash_residueRoot :
    IsεQuittingRootEndpointNash gameReward residueValue 0 residueRoot := by
  intro who
  rw [quittingRootEndpointDifference_residueRoot]
  fin_cases who <;> simp [residueRoot]

/-- The joint all-Continue mass is zero. -/
@[simp] theorem quittingStationaryContinueMass_residueRoot :
    quittingStationaryContinueMass residueRoot = 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_three]
  simp [residueRoot]

/-- Every player has a sure-quitting opponent, so every deleted survival mass
is zero. -/
@[simp] theorem fixedOpponentsContinueMass_residueRoot (who : Player) :
    quittingStationaryFixedOpponentsContinueMass residueRoot who = 0 := by
  change quittingStationaryContinueMass
    (Function.update residueRoot who (PMF.pure false)) = 0
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_three]
  fin_cases who <;> simp [residueRoot]

/-- The displayed value is a stationary fixed point. -/
theorem residueValue_fixedPoint :
    residueValue = quittingRootSuccessorPayoff
      gameReward residueValue residueRoot :=
  (quittingRootSuccessorPayoff_residueRoot residueValue).symm

/-- Exact terminal Nash against every unilateral behavioral deviation. -/
theorem isZeroAsymptoticNash_residueRoot :
    (quittingGame gameReward).IsεAsymptoticNash
      (quittingTerminalPayoff gameReward) 0
      (quittingStationaryProfile gameReward residueRoot) := by
  apply isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
    gameReward residueRoot residueValue
  · rw [quittingStationaryContinueMass_residueRoot]
    norm_num
  · exact residueValue_fixedPoint
  · exact isZeroEndpointNash_residueRoot
  · intro who
    rw [fixedOpponentsContinueMass_residueRoot]
    norm_num

/-- The stationary profile realizes exactly `(5/7, 0, 2/7)`. -/
theorem quittingTerminalPayoff_residueRoot :
    quittingTerminalPayoff gameReward
      (quittingStationaryProfile gameReward residueRoot) = residueValue := by
  apply quittingTerminalPayoff_stationary_eq_of_fixedPoint
  · rw [quittingStationaryContinueMass_residueRoot]
    norm_num
  · exact residueValue_fixedPoint

/-- Every exact behavioral unilateral cap equals the displayed value. -/
theorem fullRateUnilateralCap_residueRoot (who : Player) :
    quittingStationaryFullRateUnilateralCap gameReward residueRoot who =
      residueValue who := by
  apply quittingStationaryFullRateUnilateralCap_eq_of_fixedPoint_endpointNash
    gameReward residueRoot residueValue
  · rw [quittingStationaryContinueMass_residueRoot]
    norm_num
  · exact residueValue_fixedPoint
  · exact isZeroEndpointNash_residueRoot
  · exact isQuittingStationaryBoundaryAdmissible_of_contracts
      gameReward residueRoot residueValue (by
        intro player
        rw [fixedOpponentsContinueMass_residueRoot]
        norm_num)

/-- `(5/7, 0, 2/7)` is a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_residueValue :
    (quittingGame gameReward).IsUniformEquilibriumPayoff none residueValue := by
  apply isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
    gameReward residueRoot residueValue
  · rw [quittingStationaryContinueMass_residueRoot]
    norm_num
  · exact residueValue_fixedPoint
  · exact isZeroEndpointNash_residueRoot
  · intro who
    rw [fixedOpponentsContinueMass_residueRoot]
    norm_num

/-! ## The support-enlarged root `(1/2, 1, 1/3)` -/

/-- Player `1` quits surely; players `0` and `2` mix at rates `1/2` and `1/3`. -/
def enlargedRoot : Player → PMF Bool :=
  ![halfCoin, PMF.pure true, thirdCoin]

/-- The support-enlarged root's exact value. -/
def enlargedValue : Payoff Player :=
  ![(2 / 3 : ℝ), 1 / 2, 1 / 2]

/-- The sure middle quitter makes the successor payoff independent of the
all-Continue continuation. -/
theorem quittingRootSuccessorPayoff_enlargedRoot (tail : Payoff Player) :
    quittingRootSuccessorPayoff gameReward tail enlargedRoot = enlargedValue := by
  funext who
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [enlargedRoot, enlargedValue, QuittingSwitchingResidueRegression.reward,
      quittingQuitters, Matrix.cons_val_two] <;> norm_num

/-- Quit minus Continue is `(0, 1/5, 0)`. -/
theorem quittingRootEndpointDifference_enlargedRoot (who : Player) :
    quittingRootEndpointDifference gameReward enlargedValue enlargedRoot who =
      ![(0 : ℝ), 1 / 5, 0] who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool, expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [enlargedRoot, enlargedValue, QuittingSwitchingResidueRegression.reward,
      quittingQuitters, Matrix.cons_val_two] <;> norm_num

/-- The support-enlarged row is exact endpoint Nash.  The two mixing players
are indifferent, and the sure middle quitter has the positive endpoint gap. -/
theorem isZeroEndpointNash_enlargedRoot :
    IsεQuittingRootEndpointNash gameReward enlargedValue 0 enlargedRoot := by
  intro who
  rw [quittingRootEndpointDifference_enlargedRoot]
  fin_cases who <;> simp [enlargedRoot]

/-- The joint all-Continue mass is zero because player `1` quits surely. -/
@[simp] theorem quittingStationaryContinueMass_enlargedRoot :
    quittingStationaryContinueMass enlargedRoot = 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_three]
  simp [enlargedRoot]

/-- Deleted survival masses are `(0, 1/3, 0)`. -/
@[simp] theorem fixedOpponentsContinueMass_enlargedRoot (who : Player) :
    quittingStationaryFixedOpponentsContinueMass enlargedRoot who =
      ![(0 : ℝ), 1 / 3, 0] who := by
  change quittingStationaryContinueMass
    (Function.update enlargedRoot who (PMF.pure false)) = _
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_three]
  fin_cases who <;> simp [enlargedRoot]
  grind only

/-- The displayed support-enlarged value is a stationary fixed point. -/
theorem enlargedValue_fixedPoint :
    enlargedValue = quittingRootSuccessorPayoff
      gameReward enlargedValue enlargedRoot :=
  (quittingRootSuccessorPayoff_enlargedRoot enlargedValue).symm

/-- Exact terminal Nash against every unilateral behavioral deviation. -/
theorem isZeroAsymptoticNash_enlargedRoot :
    (quittingGame gameReward).IsεAsymptoticNash
      (quittingTerminalPayoff gameReward) 0
      (quittingStationaryProfile gameReward enlargedRoot) := by
  apply isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
    gameReward enlargedRoot enlargedValue
  · rw [quittingStationaryContinueMass_enlargedRoot]
    norm_num
  · exact enlargedValue_fixedPoint
  · exact isZeroEndpointNash_enlargedRoot
  · intro who
    rw [fixedOpponentsContinueMass_enlargedRoot]
    fin_cases who <;> norm_num

/-- The stationary profile realizes exactly `(2/3, 1/2, 1/2)`. -/
theorem quittingTerminalPayoff_enlargedRoot :
    quittingTerminalPayoff gameReward
      (quittingStationaryProfile gameReward enlargedRoot) = enlargedValue := by
  apply quittingTerminalPayoff_stationary_eq_of_fixedPoint
  · rw [quittingStationaryContinueMass_enlargedRoot]
    norm_num
  · exact enlargedValue_fixedPoint

/-- Every exact behavioral unilateral cap equals the displayed value. -/
theorem fullRateUnilateralCap_enlargedRoot (who : Player) :
    quittingStationaryFullRateUnilateralCap gameReward enlargedRoot who =
      enlargedValue who := by
  apply quittingStationaryFullRateUnilateralCap_eq_of_fixedPoint_endpointNash
    gameReward enlargedRoot enlargedValue
  · rw [quittingStationaryContinueMass_enlargedRoot]
    norm_num
  · exact enlargedValue_fixedPoint
  · exact isZeroEndpointNash_enlargedRoot
  · exact isQuittingStationaryBoundaryAdmissible_of_contracts
      gameReward enlargedRoot enlargedValue (by
        intro player
        rw [fixedOpponentsContinueMass_enlargedRoot]
        fin_cases player <;> norm_num)

/-- `(2/3, 1/2, 1/2)` is a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_enlargedValue :
    (quittingGame gameReward).IsUniformEquilibriumPayoff none enlargedValue := by
  apply isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
    gameReward enlargedRoot enlargedValue
  · rw [quittingStationaryContinueMass_enlargedRoot]
    norm_num
  · exact enlargedValue_fixedPoint
  · exact isZeroEndpointNash_enlargedRoot
  · intro who
    rw [fixedOpponentsContinueMass_enlargedRoot]
    fin_cases who <;> norm_num

/-! ## Capstone: no sure exit set, but two stationary uniform payoffs -/

/-- A complete exact stationary certificate for this concrete table: the
profile realizes the displayed value, is terminal Nash against every
behavioral deviation, has exact full-rate unilateral caps equal to the value,
and delivers the value uniformly. -/
def IsExactStationaryUniformCertificate
    (root : Player → PMF Bool) (value : Payoff Player) : Prop :=
  quittingTerminalPayoff gameReward
      (quittingStationaryProfile gameReward root) = value ∧
    (quittingGame gameReward).IsεAsymptoticNash
      (quittingTerminalPayoff gameReward) 0
      (quittingStationaryProfile gameReward root) ∧
    (∀ who, quittingStationaryFullRateUnilateralCap
      gameReward root who = value who) ∧
    (quittingGame gameReward).IsUniformEquilibriumPayoff none value

/-- The two-sure-quitter row carries the complete exact stationary
certificate. -/
theorem residueRoot_isExactStationaryUniformCertificate :
    IsExactStationaryUniformCertificate residueRoot residueValue := by
  exact ⟨quittingTerminalPayoff_residueRoot,
    isZeroAsymptoticNash_residueRoot,
    fullRateUnilateralCap_residueRoot,
    isUniformEquilibriumPayoff_residueValue⟩

/-- The support-enlarged row carries the complete exact stationary
certificate. -/
theorem enlargedRoot_isExactStationaryUniformCertificate :
    IsExactStationaryUniformCertificate enlargedRoot enlargedValue := by
  exact ⟨quittingTerminalPayoff_enlargedRoot,
    isZeroAsymptoticNash_enlargedRoot,
    fullRateUnilateralCap_enlargedRoot,
    isUniformEquilibriumPayoff_enlargedValue⟩

/-- The two displayed uniform-equilibrium payoffs are genuinely distinct. -/
theorem residueValue_ne_enlargedValue : residueValue ≠ enlargedValue := by
  intro h
  have h0 := congrFun h 0
  norm_num [residueValue, enlargedValue] at h0

/-- The regression table has no sure exit set, yet it has two distinct exact
stationary uniform-equilibrium payoffs.  This formally locates the failure in
the restricted local branch grammar rather than in equilibrium existence. -/
theorem noSureExitSet_but_two_distinct_stationary_uniformPayoffs :
    (∀ S : Finset Player, S.Nonempty →
      ¬ IsQuittingSureExitSet gameReward S) ∧
      residueValue ≠ enlargedValue ∧
      IsExactStationaryUniformCertificate residueRoot residueValue ∧
      IsExactStationaryUniformCertificate enlargedRoot enlargedValue := by
  exact ⟨not_isQuittingSureExitSet_gameReward, residueValue_ne_enlargedValue,
    residueRoot_isExactStationaryUniformCertificate,
    enlargedRoot_isExactStationaryUniformCertificate⟩

end QuittingSwitchingResidueExactRoot
end GameTheory
