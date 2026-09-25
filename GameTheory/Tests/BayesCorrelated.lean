/-
# Bayes-Nash and Bayes-correlated equilibrium probe

A fair true type is duplicated as a private signal. Matching it earns one;
recommending its opposite remains plausible but fails obedience.
-/

import GameTheory.Core.BayesCorrelated
import Mathlib.Probability.Distributions.Uniform

noncomputable section

namespace GameTheory.Tests.BayesCorrelated

open GameTheory GameTheory.Math.Probability

abbrev Player := Fin 1

def falseTypes : Player → Bool := fun _ => false

def trueTypes : Player → Bool := fun _ => true

def prior : PMF (Player → Bool) :=
  (PMF.uniformOfFintype Bool).map fun bit _ => bit

@[reducible]
def game : BayesianGame Player where
  Ty _ := Bool
  Act _ := Bool
  prior := prior
  payoff types actions who :=
    if actions who = types who then 1 else 0

@[simp]
theorem prior_prob_false : prior falseTypes = 1 / 2 := by
  have hne : (fun _ : Player => false) ≠ (fun _ : Player => true) := by
    intro h
    have hzero := congrFun h 0
    cases hzero
  simp [prior, PMF.map_apply, PMF.uniformOfFintype_apply]
  unfold falseTypes
  simp [hne]

@[simp]
theorem prior_prob_true : prior trueTypes = 1 / 2 := by
  have hne : (fun _ : Player => true) ≠ (fun _ : Player => false) := by
    intro h
    have hzero := congrFun h 0
    cases hzero
  simp [prior, PMF.map_apply, PMF.uniformOfFintype_apply]
  unfold trueTypes
  simp [hne]

@[reducible]
def information : BayesianGame.InformationStructure game (fun _ => Bool) where
  law := prior.map fun types => (types, types)
  isBayesPlausible := by
    rw [PMF.map_comp]
    exact PMF.map_id prior

def matchingPlan : Profile information.inducedBayesianGame.signature :=
  fun _ observed => observed.1

private theorem inducedUtility_bounded (who : Player)
    (outcome : information.inducedBayesianGame.signature.Outcome) :
    |information.inducedBayesianGame.utility outcome who| ≤ (1 : ℝ) := by
  simp [BayesianGame.utility, information, game]
  split <;> norm_num

theorem matchingPlan_isNash :
    IsNash information.inducedBayesianGame.toForm
      (euPreference information.inducedBayesianGame.utility)
      matchingPlan := by
  rw [isNash_iff]
  intro who replacement
  let dev := Profile.update matchingPlan who replacement
  have hmatch : UtilityIntegrable information.inducedBayesianGame.utility who
      (information.inducedBayesianGame.toForm.play matchingPlan) :=
    payoffIntegrable_of_bounded _ _ (inducedUtility_bounded who)
  have hdev : UtilityIntegrable information.inducedBayesianGame.utility who
      (information.inducedBayesianGame.toForm.play dev) :=
    payoffIntegrable_of_bounded _ _ (inducedUtility_bounded who)
  apply (euPreference_iff information.inducedBayesianGame.utility who
    (information.inducedBayesianGame.toForm.play matchingPlan)
    (information.inducedBayesianGame.toForm.play dev) hmatch hdev).2
  rw [information.inducedBayesianGame.expectedUtility_eq_prior
      who matchingPlan hmatch,
    information.inducedBayesianGame.expectedUtility_eq_prior who dev hdev]
  apply expect_mono
  intro observed _
  simp [BayesianGame.planPayoff, dev, matchingPlan, information, game,
    BayesianGame.actionsOf]
  split <;> norm_num

theorem outcomeLaw_isBayesCorrelatedEq :
    game.IsBayesCorrelatedEq (information.outcomeLaw matchingPlan) :=
  information.isBayesCorrelatedEq_outcomeLaw_of_isNash
    matchingPlan matchingPlan_isNash

/-- The fixture exercises the full guarded interim characterization. -/
theorem outcomeLaw_interim_obedience :
    game.IsBayesPlausible (information.outcomeLaw matchingPlan) ∧
      game.InterimObedienceTests (information.outcomeLaw matchingPlan) :=
  (game.isBayesCorrelatedEq_iff_interim_obedience
    (information.outcomeLaw matchingPlan)).1 outcomeLaw_isBayesCorrelatedEq

theorem outcomeLaw_isBayesCorrelatedEq_via_interim :
    game.IsBayesCorrelatedEq (information.outcomeLaw matchingPlan) :=
  (game.isBayesCorrelatedEq_iff_interim_obedience
    (information.outcomeLaw matchingPlan)).2 outcomeLaw_interim_obedience

def mismatchingPlan : Profile game.signature :=
  fun _ ownType => !ownType

def mismatchingRecommendation : game.RecommendationLaw :=
  game.strategyRecommendationLaw mismatchingPlan

theorem mismatchingRecommendation_isBayesPlausible :
    game.IsBayesPlausible mismatchingRecommendation :=
  game.strategyRecommendationLaw_isBayesPlausible mismatchingPlan

def flipDeviation : game.ObedienceDeviation 0 :=
  fun _ recommended => !recommended

private theorem gameUtility_bounded (who : Player)
    (outcome : game.signature.Outcome) :
    |game.utility outcome who| ≤ (1 : ℝ) := by
  simp [BayesianGame.utility, game]
  split <;> norm_num

/-- The recommendation law integrates the actual correlated payoff. -/
theorem hRecommended :
    UtilityIntegrable game.utility 0 mismatchingRecommendation :=
  payoffIntegrable_of_bounded _ _ (gameUtility_bounded 0)

/-- The deviating recommendation law integrates its mapped payoff. -/
theorem hDeviating :
    UtilityIntegrable game.utility 0
      (mismatchingRecommendation.map
        (game.recordDeviation 0 flipDeviation)) :=
  payoffIntegrable_of_bounded _ _ (gameUtility_bounded 0)

theorem mismatchingRecommendation_recommendedValue :
    game.recommendedValue mismatchingRecommendation 0 hRecommended = 0 := by
  have hplan : UtilityIntegrable game.utility 0
      (game.toForm.play mismatchingPlan) := hRecommended
  have hpoint : ∀ types, game.planPayoff 0 mismatchingPlan types = 0 := by
    intro types
    simp [BayesianGame.planPayoff, mismatchingPlan,
      BayesianGame.actionsOf]
  calc
    game.recommendedValue mismatchingRecommendation 0 hRecommended =
      expect game.prior (game.planPayoff 0 mismatchingPlan)
        (game.planPayoff_integrable 0 mismatchingPlan hplan) :=
      game.expectedUtility_eq_prior 0 mismatchingPlan hplan
    _ = expect game.prior (fun _ => 0)
        (payoffIntegrable_constant game.prior 0) :=
      expect_congr_on_support (fun types _ => hpoint types) _ _
    _ = 0 := expect_constant game.prior 0 _

theorem mismatchingRecommendation_deviatingValue :
    game.deviatingValue mismatchingRecommendation 0 flipDeviation
        hDeviating = 1 := by
  let devPlan := Profile.update mismatchingPlan 0
    (fun ownType => flipDeviation ownType (mismatchingPlan 0 ownType))
  have hplan : UtilityIntegrable game.utility 0 (game.toForm.play devPlan) :=
    payoffIntegrable_congr_law
      (game.recordDeviation_strategyRecommendationLaw
        mismatchingPlan 0 flipDeviation) hDeviating
  have hpoint : ∀ types, game.planPayoff 0 devPlan types = 1 := by
    intro types
    simp [BayesianGame.planPayoff, devPlan, game, mismatchingPlan,
      flipDeviation, BayesianGame.actionsOf]
  calc
    game.deviatingValue mismatchingRecommendation 0 flipDeviation
        hDeviating =
      expect game.prior (game.planPayoff 0 devPlan)
        (game.planPayoff_integrable 0 devPlan hplan) := by
          exact (game.deviatingValue_strategyRecommendationLaw
            mismatchingPlan 0 flipDeviation hDeviating).trans
            (game.expectedUtility_eq_prior 0 devPlan hplan)
    _ = expect game.prior (fun _ => 1)
        (payoffIntegrable_constant game.prior 1) :=
      expect_congr_on_support (fun types _ => hpoint types) _ _
    _ = 1 := expect_constant game.prior 1 _

theorem mismatchingRecommendation_not_isBayesCorrelatedEq :
    ¬ game.IsBayesCorrelatedEq mismatchingRecommendation := by
  intro hBCE
  have hobey := hBCE.2 0 flipDeviation
  have hle :
      game.deviatingValue mismatchingRecommendation 0 flipDeviation
          hDeviating ≤
        game.recommendedValue mismatchingRecommendation 0 hRecommended :=
    (euPreference_iff game.utility 0 mismatchingRecommendation
      (mismatchingRecommendation.map
        (game.recordDeviation 0 flipDeviation))
      hRecommended hDeviating).mp hobey
  rw [mismatchingRecommendation_deviatingValue,
    mismatchingRecommendation_recommendedValue] at hle
  norm_num at hle

theorem mismatchingRecommendation_not_interim_obedient :
    ¬ game.InterimObedienceTests mismatchingRecommendation := by
  intro hinterim
  apply mismatchingRecommendation_not_isBayesCorrelatedEq
  exact (game.isBayesCorrelatedEq_iff_interim_obedience
    mismatchingRecommendation).2
      ⟨mismatchingRecommendation_isBayesPlausible, hinterim⟩

end GameTheory.Tests.BayesCorrelated
