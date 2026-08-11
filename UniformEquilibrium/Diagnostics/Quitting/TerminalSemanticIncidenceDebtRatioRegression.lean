/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPartialResetTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio

/-!
# Incidence--debt ratio regression

The marked collision regression has a literal half-reset which scales both
the reset player's best-response debt and total opponent incidence by exactly
`1 / 2` (there is only one opponent).  Thus minimizing debt per unit
incidence cannot force strict progress from the fractional-reset inequality
alone: its lower bound can be saturated.

The target remains a joint semantic/law carrier point with positive
incidence, but every exact Nash root against its displayed cap is
all-Continue.  This is a local route fence, not a counterexample to the
quitting-game conjecture.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

namespace QuittingIncidenceDebtRatioRegression

abbrev reward := QuittingResetIncidenceCapRegression.regressionReward

abbrev sourceRoot := QuittingResetIncidenceCapRegression.collisionRoot

abbrev continuation := QuittingResetIncidenceCapRegression.continuation

/-- Move player `true` halfway from sure Quit toward pure Continue. -/
def halfRoot : Bool → PMF Bool :=
  quittingPartialEndpointRoot sourceRoot true false (1 / 2 : ℝ)
    (by norm_num) (by norm_num)

def halfProfile : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward halfRoot continuation

def halfPair : QuittingTerminalSemanticPair Bool :=
  quittingTerminalSemanticPair reward halfProfile

def halfMass : QuittingTerminalOutcome Bool → ℝ :=
  quittingTerminalOutcomeMass reward halfProfile

/-- With two players, total opponent incidence has exactly one summand. -/
theorem totalOpponentIncidence_eq_displayed
    (mass : QuittingTerminalOutcome Bool → ℝ) :
    quittingTerminalTotalOpponentIncidenceMass false mass =
      quittingTerminalOpponentIncidenceMass false true mass := by
  unfold quittingTerminalTotalOpponentIncidenceMass
  rw [show (Finset.univ : Finset Bool).erase false = {true} by decide]
  simp

def explicitHalfRoot : Bool → PMF Bool := fun who =>
  if who then PMF.uniformOfFintype Bool else PMF.pure true

theorem halfRoot_eq_explicitHalfRoot : halfRoot = explicitHalfRoot := by
  funext who
  apply Math.ProbabilityMassFunction.toVector_injective
  funext action
  cases who <;> cases action <;>
    simp [Math.ProbabilityMassFunction.toVector, halfRoot,
      explicitHalfRoot, quittingPartialEndpointRoot, sourceRoot,
      QuittingResetIncidenceCapRegression.collisionRoot,
      QuittingMarkedExitNashificationRegression.markedCollisionRoot,
      PMF.uniformOfFintype_apply]
  all_goals norm_num

/-- The reset leaves the marked player at sure Quit and makes the other
player a fair Quit/Continue coin. -/
theorem halfRoot_probabilities :
    (halfRoot false true).toReal = 1 ∧
      (halfRoot true true).toReal = 1 / 2 ∧
      (halfRoot true false).toReal = 1 / 2 := by
  rw [halfRoot_eq_explicitHalfRoot]
  norm_num [explicitHalfRoot, PMF.uniformOfFintype_apply]

/-- The half-reset payoff is `(0, 1/2)`.  The unmarked player's behavioral
envelope remains `1`; the marked cap is intentionally left unevaluated. -/
theorem halfPair_coordinates :
    halfPair.1 false = 0 ∧ halfPair.1 true = 1 / 2 ∧
      halfPair.2 true = 1 := by
  have hprefix := quittingTerminalSemanticPair_rootThenContinuation
    reward halfRoot continuation (M := 1) (by norm_num)
      QuittingResetIncidenceCapRegression.reward_bound
  change quittingTerminalSemanticPair reward halfProfile =
      quittingTerminalSemanticPrefix reward halfRoot
        (quittingTerminalSemanticPair reward continuation) at hprefix
  rw [show halfPair = quittingTerminalSemanticPrefix reward halfRoot
      (quittingTerminalSemanticPair reward continuation) by exact hprefix]
  rcases halfRoot_probabilities with ⟨hfalse, htrue, htrueContinue⟩
  have hroot : halfRoot = explicitHalfRoot := halfRoot_eq_explicitHalfRoot
  simp only [quittingTerminalSemanticPrefix]
  constructor
  · rw [quittingRootSuccessorPayoff_eq_endpointMix]
    unfold quittingRootQuitPayoff quittingRootContinuePayoff
      quittingRootExpectedPayoff
    rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
    rw [hroot]
    norm_num [explicitHalfRoot, PMF.uniformOfFintype_apply,
      quittingRootPayoff, reward,
      QuittingResetIncidenceCapRegression.regressionReward,
      QuittingMarkedExitNashificationRegression.reward,
      hfalse, htrue, htrueContinue]
  constructor
  · rw [quittingRootSuccessorPayoff_eq_endpointMix]
    unfold quittingRootQuitPayoff quittingRootContinuePayoff
      quittingRootExpectedPayoff
    rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
    rw [hroot]
    rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
    norm_num [explicitHalfRoot, PMF.uniformOfFintype_apply,
      quittingRootPayoff, reward,
      QuittingResetIncidenceCapRegression.regressionReward,
      QuittingMarkedExitNashificationRegression.reward,
      hfalse, htrue, htrueContinue]
  · unfold quittingRootQuitPayoff quittingRootContinuePayoff
      quittingRootExpectedPayoff
    rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool,
      QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
    rw [hroot]
    norm_num [explicitHalfRoot, PMF.uniformOfFintype_apply,
      quittingRootPayoff, reward,
      QuittingResetIncidenceCapRegression.regressionReward,
      QuittingMarkedExitNashificationRegression.reward,
      hfalse, htrue, htrueContinue]

theorem halfPair_mass_mem_carrier :
    (halfPair, halfMass) ∈ quittingTerminalSemanticLawCarrier reward := by
  exact quittingTerminalSemanticLawPoint_mem_carrier reward halfProfile

/-- Debt and incidence are both exactly halved. -/
theorem half_debt_and_incidence :
    quittingTerminalSemanticDebt halfPair true = 1 / 2 ∧
      quittingTerminalOpponentIncidenceMass false true halfMass = 1 / 2 := by
  rcases halfPair_coordinates with ⟨_huFalse, huTrue, hbTrue⟩
  constructor
  · simp [quittingTerminalSemanticDebt, huTrue, hbTrue]
    norm_num
  · have hlaw : halfMass = quittingTerminalOutcomeLawPrefix halfRoot
        (quittingTerminalOutcomeMass reward continuation) := by
      exact (quittingTerminalOutcomeLawPrefix_outcomeMass
        reward halfRoot continuation).symm
    rw [hlaw, quittingTerminalOpponentIncidenceMass_lawPrefix]
    let fullTerminal : {S : Finset Bool // S.Nonempty} :=
      ⟨Finset.univ, by simp⟩
    have hfilter : Finset.univ.filter
        (fun terminal : {S : Finset Bool // S.Nonempty} =>
          true ∈ terminal.val ∧ true ≠ false) =
        {quittingSingletonTerminal true, fullTerminal} := by
      decide
    unfold quittingRootOpponentIncidenceMass
    rw [hfilter]
    have hne : quittingSingletonTerminal true ≠ fullTerminal := by decide
    rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
    rcases halfRoot_probabilities with ⟨hfalse, htrue, htrueContinue⟩
    have hsingle : quittingRootCoalitionMass halfRoot
        (quittingSingletonTerminal true).val = 0 := by
      change quittingRootCoalitionMass halfRoot {true} = 0
      unfold quittingRootCoalitionMass
      have hcomp : ({true} : Finset Bool)ᶜ = {false} := by decide
      rw [coalitionMass, hcomp]
      norm_num [quittingRootQuitRates, hfalse, htrue, htrueContinue]
    have hfull : quittingRootCoalitionMass halfRoot fullTerminal.val = 1 / 2 := by
      change quittingRootCoalitionMass halfRoot Finset.univ = 1 / 2
      unfold quittingRootCoalitionMass
      have hcomp : (Finset.univ : Finset Bool)ᶜ = ∅ := by decide
      rw [coalitionMass, hcomp]
      norm_num [quittingRootQuitRates, hfalse, htrue, htrueContinue]
    have hcontinue : quittingStationaryContinueMass halfRoot = 0 := by
      rw [halfRoot_eq_explicitHalfRoot]
      norm_num [quittingStationaryContinueMass, explicitHalfRoot,
        quittingAllContinueAction, pmfPi_apply,
        PMF.uniformOfFintype_apply]
    rw [hsingle, hfull, hcontinue]
    norm_num

/-- The original collision already realizes the strongest local residual of
the total-incidence quotient: positive total opponent incidence on a reset
face, but no absorbing exact cap--Nash selection at all. -/
theorem source_positiveTotalOpponentIncidence_but_onlyAllContinue_capNash :
    (QuittingResetIncidenceCapRegression.pair,
        QuittingResetIncidenceCapRegression.mass) ∈
      quittingTerminalSemanticLawCarrier reward ∧
    quittingTerminalSemanticDebt
        QuittingResetIncidenceCapRegression.pair false = 0 ∧
    quittingTerminalSemanticDebtSum
        QuittingResetIncidenceCapRegression.pair = 1 ∧
    quittingTerminalTotalOpponentIncidenceMass false
        QuittingResetIncidenceCapRegression.mass = 1 ∧
    ∀ root : Bool → PMF Bool,
      IsεQuittingRootNash reward
          QuittingResetIncidenceCapRegression.pair.2 0 root →
        root = (quittingAllContinueRoot : Bool → PMF Bool) := by
  rw [totalOpponentIncidence_eq_displayed]
  exact ⟨QuittingResetIncidenceCapRegression.pair_mass_mem_carrier,
    QuittingResetIncidenceCapRegression.reset_and_positiveDebt.1,
    QuittingResetIncidenceCapRegression.reset_and_positiveDebt.2.2,
    QuittingResetIncidenceCapRegression.opponentIncidence_eq_one,
    QuittingResetIncidenceCapRegression.exact_capNash_forces_allContinue⟩

theorem half_cap_quitPayoff_true (root : Bool → PMF Bool) :
    quittingRootQuitPayoff reward halfPair.2 root true = 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward,
    QuittingResetIncidenceCapRegression.regressionReward,
    QuittingMarkedExitNashificationRegression.reward]

theorem half_cap_continuePayoff_true (root : Bool → PMF Bool) :
    quittingRootContinuePayoff reward halfPair.2 root true = 1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  have hsum := quittingRoot_continueProbability_add_quitProbability root false
  have hc : (root false false).toReal = 1 - (root false true).toReal := by
    linarith
  have hb := halfPair_coordinates.2.2
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward,
    QuittingResetIncidenceCapRegression.regressionReward,
    QuittingMarkedExitNashificationRegression.reward, hc, hb]

theorem half_cap_endpointDifference_true (root : Bool → PMF Bool) :
    quittingRootEndpointDifference reward halfPair.2 root true = -1 := by
  rw [quittingRootEndpointDifference, half_cap_quitPayoff_true,
    half_cap_continuePayoff_true]
  norm_num

theorem half_cap_endpointDifference_false_of_true_continue
    (root : Bool → PMF Bool) (htrue : root true = PMF.pure false) :
    quittingRootEndpointDifference reward halfPair.2 root false =
      -1 - halfPair.2 false := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool,
    QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward,
    QuittingResetIncidenceCapRegression.regressionReward,
    QuittingMarkedExitNashificationRegression.reward, htrue]

theorem half_cap_false_nonneg : 0 ≤ halfPair.2 false := by
  have hmem : halfPair ∈ quittingTerminalSemanticCarrier reward := by
    apply subset_closure
    exact ⟨halfProfile, rfl⟩
  have hdebt := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
    reward (M := 1) (by norm_num)
      QuittingResetIncidenceCapRegression.reward_bound hmem false
  have hpayoff := halfPair_coordinates.1
  unfold quittingTerminalSemanticDebt at hdebt
  rw [hpayoff] at hdebt
  linarith

/-- The fractional reset does not open an absorbing cap--Nash branch. -/
theorem half_exact_capNash_forces_allContinue
    (root : Bool → PMF Bool)
    (hnash : IsεQuittingRootNash reward halfPair.2 0 root) :
    root = (quittingAllContinueRoot : Bool → PMF Bool) := by
  have hendpoint : IsεQuittingRootEndpointNash reward halfPair.2 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward halfPair.2 root).mpr hnash
  have htrueZero : (root true true).toReal = 0 := by
    have h := (hendpoint true).2
    rw [half_cap_endpointDifference_true] at h
    exact le_antisymm (by linarith) ENNReal.toReal_nonneg
  have htrue : root true = PMF.pure false :=
    pmf_eq_pure_false_of_apply_true_toReal_eq_zero (root true) htrueZero
  have hfalseDiff :=
    half_cap_endpointDifference_false_of_true_continue root htrue
  have hfalseZero : (root false true).toReal = 0 := by
    have h := (hendpoint false).2
    rw [hfalseDiff] at h
    exact le_antisymm (by
      nlinarith [half_cap_false_nonneg,
        ENNReal.toReal_nonneg (a := root false true)]) ENNReal.toReal_nonneg
  have hfalse : root false = PMF.pure false :=
    pmf_eq_pure_false_of_apply_true_toReal_eq_zero (root false) hfalseZero
  funext who
  cases who
  · simpa [quittingAllContinueRoot] using hfalse
  · simpa [quittingAllContinueRoot] using htrue

/-- **Sharp ratio fence.**  The literal half reset keeps positive incidence
and preserves the reset player's debt per incidence exactly (stated without division),
yet its exact cap correspondence contains only all-Continue. -/
theorem halfReset_saturates_incidenceDebt_ratio_but_capNash_is_allContinue :
    (halfPair, halfMass) ∈ quittingTerminalSemanticLawCarrier reward ∧
      0 < quittingTerminalTotalOpponentIncidenceMass false halfMass ∧
      quittingTerminalSemanticDebt
          QuittingResetIncidenceCapRegression.pair true *
          quittingTerminalTotalOpponentIncidenceMass false halfMass =
        quittingTerminalSemanticDebt halfPair true *
          quittingTerminalTotalOpponentIncidenceMass false
            QuittingResetIncidenceCapRegression.mass ∧
      quittingTerminalSemanticDebt halfPair true <
        quittingTerminalSemanticDebt
          QuittingResetIncidenceCapRegression.pair true ∧
      ∀ root : Bool → PMF Bool,
        IsεQuittingRootNash reward halfPair.2 0 root →
          root = (quittingAllContinueRoot : Bool → PMF Bool) := by
  have hsourceDebt :=
    QuittingResetIncidenceCapRegression.reset_and_positiveDebt.2.1
  have hsourceIncidence :=
    QuittingResetIncidenceCapRegression.opponentIncidence_eq_one
  rcases half_debt_and_incidence with ⟨hhalfDebt, hhalfIncidence⟩
  have hhalfTotal : quittingTerminalTotalOpponentIncidenceMass false halfMass =
      1 / 2 := by
    rw [totalOpponentIncidence_eq_displayed, hhalfIncidence]
  have hsourceTotal : quittingTerminalTotalOpponentIncidenceMass false
      QuittingResetIncidenceCapRegression.mass = 1 := by
    rw [totalOpponentIncidence_eq_displayed, hsourceIncidence]
  exact ⟨halfPair_mass_mem_carrier, by rw [hhalfTotal]; norm_num,
    by rw [hsourceDebt, hsourceTotal, hhalfDebt, hhalfTotal]; norm_num,
    by rw [hsourceDebt, hhalfDebt]; norm_num,
    half_exact_capNash_forces_allContinue⟩

end QuittingIncidenceDebtRatioRegression

end GameTheory
