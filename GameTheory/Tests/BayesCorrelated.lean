/-
Nondegenerate Bayes-Nash-to-BCE probe.

One player has a fair Boolean type and receives one exactly when its action
matches that type. The private signal repeats the type, and the induced plan
chooses the true-type coordinate. Both types have positive probability, so the
outcome-law theorem is not a one-state or zero-payoff tautology.
-/

import GameTheory.Core.BayesCorrelated

noncomputable section

namespace GameTheory.Tests.BayesCorrelated

open GameTheory.Math.Probability

abbrev Player := Fin 1

def falseTypes : Player → Bool := fun _ => false

def trueTypes : Player → Bool := fun _ => true

def prior : FinDist (Player → Bool) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure falseTypes) (FinDist.pure trueTypes)

@[reducible]
def game : BayesianGame Player where
  Ty _ := Bool
  Act _ := Bool
  prior := prior
  payoff types actions who :=
    if actions who = types who then 1 else 0

@[simp]
theorem prior_prob_false : prior.prob falseTypes = 1 / 2 := by
  have hne : falseTypes ≠ trueTypes := by
    intro h
    have := congrFun h 0
    simp [falseTypes, trueTypes] at this
  rw [prior, FinDist.prob_mix]
  norm_num [FinDist.prob_pure_eq_ite, hne]

@[simp]
theorem prior_prob_true : prior.prob trueTypes = 1 / 2 := by
  have hne : trueTypes ≠ falseTypes := by
    intro h
    have := congrFun h 0
    simp [falseTypes, trueTypes] at this
  rw [prior, FinDist.prob_mix]
  norm_num [FinDist.prob_pure_eq_ite, hne]

/-- The signal profile repeats the true type profile. -/
@[reducible]
def information : BayesianGame.InformationStructure game (fun _ => Bool) where
  law := prior.map fun types => (types, types)
  isBayesPlausible := by
    rw [FinDist.map_comp]
    exact FinDist.map_id prior

/-- Choose the true-type coordinate; the duplicate signal is deliberately not
needed for optimality. -/
def matchingPlan : Profile information.inducedBayesianGame.signature :=
  fun _ observed => observed.1

theorem matchingPlan_isNash :
    IsNash information.inducedBayesianGame.toForm
      (euPreference information.inducedBayesianGame.utility)
      matchingPlan := by
  rw [information.inducedBayesianGame.isNash_iff_interim]
  intro who ownType respond
  unfold BayesianGame.interimValue
  apply FinDist.expect_mono
  intro types _
  by_cases htype : types who = ownType
  · subst ownType
    simp [matchingPlan, BayesianGame.InformationStructure.inducedBayesianGame,
      game]
    split <;> norm_num
  · simp [htype]

/-- Every positive own-type/recommendation cell of the induced law obeys: on
its support the recommendation equals the true type, while a replacement can
pay at most one. -/
theorem outcomeLaw_interim_obedience :
    ∀ who ownType recommended replacement,
      ∀ hObserved :
          ∃ rec ∈ game.obedienceEvent who ownType recommended,
            rec ∈ (information.outcomeLaw matchingPlan).support,
        game.interimDeviatingValue (information.outcomeLaw matchingPlan)
              who ownType recommended replacement hObserved ≤
          game.interimRecommendedValue (information.outcomeLaw matchingPlan)
            who ownType recommended hObserved := by
  intro who ownType recommended replacement hObserved
  unfold BayesianGame.interimDeviatingValue
    BayesianGame.interimRecommendedValue
  apply FinDist.expect_mono
  intro rec hrec
  have hsupported :=
    (FinDist.support_condOn (information.outcomeLaw matchingPlan)
      (game.obedienceEvent who ownType recommended) hObserved hrec).2
  rw [BayesianGame.InformationStructure.outcomeLaw, FinDist.support_map]
    at hsupported
  obtain ⟨types, _, rfl⟩ := hsupported
  simp [game, matchingPlan, Profile.update]
  split <;> norm_num

/-- The conditional characterization certifies the induced law without
enumerating deviations over all type/recommendation pairs at once. -/
theorem outcomeLaw_isBayesCorrelatedEq_via_interim :
    game.IsBayesCorrelatedEq (information.outcomeLaw matchingPlan) :=
  (game.isBayesCorrelatedEq_iff_interim_obedience
      (information.outcomeLaw matchingPlan)).2
    ⟨information.outcomeLaw_isBayesPlausible matchingPlan,
      outcomeLaw_interim_obedience⟩

/-- The Bayes-Nash plan induces a Bayes-plausible and obedient recommendation
law in the original game. -/
theorem outcomeLaw_isBayesCorrelatedEq :
    game.IsBayesCorrelatedEq (information.outcomeLaw matchingPlan) :=
  information.isBayesCorrelatedEq_outcomeLaw_of_isNash
    matchingPlan matchingPlan_isNash

/-- Recommend the action opposite the true type. The type marginal remains
correct, but following the recommendation is strictly suboptimal. -/
def mismatchingPlan : Profile game.signature :=
  fun _ ownType => !ownType

def mismatchingRecommendation : game.RecommendationLaw :=
  game.strategyRecommendationLaw mismatchingPlan

theorem mismatchingRecommendation_isBayesPlausible :
    game.IsBayesPlausible mismatchingRecommendation :=
  game.strategyRecommendationLaw_isBayesPlausible mismatchingPlan

def flipDeviation : game.ObedienceDeviation 0 :=
  fun _ recommended => !recommended

theorem mismatchingRecommendation_recommendedValue :
    game.recommendedValue mismatchingRecommendation 0 = 0 := by
  unfold BayesianGame.recommendedValue mismatchingRecommendation
    BayesianGame.strategyRecommendationLaw
  rw [FinDist.expect_map]
  convert FinDist.expect_const game.prior 0 using 1
  apply FinDist.expect_congr
  intro types _
  simp [mismatchingPlan, BayesianGame.actionsOf]

theorem mismatchingRecommendation_deviatingValue :
    game.deviatingValue mismatchingRecommendation 0 flipDeviation = 1 := by
  unfold BayesianGame.deviatingValue mismatchingRecommendation
    BayesianGame.strategyRecommendationLaw
  rw [FinDist.expect_map]
  convert FinDist.expect_const game.prior 1 using 1
  apply FinDist.expect_congr
  intro types _
  simp [game, mismatchingPlan, flipDeviation,
    BayesianGame.actionsOf, BayesianGame.applyObedienceDeviation]

/-- Bayes plausibility alone does not imply obedience. -/
theorem mismatchingRecommendation_not_isBayesCorrelatedEq :
    ¬ game.IsBayesCorrelatedEq mismatchingRecommendation := by
  rintro ⟨_, obedient⟩
  have hdeviation := obedient 0 flipDeviation
  rw [mismatchingRecommendation_deviatingValue,
    mismatchingRecommendation_recommendedValue] at hdeviation
  norm_num at hdeviation

/-- Therefore the mismatching recommendation cannot pass every positive-cell
interim check either.  Bayes plausibility is held fixed, so the failure is an
obedience failure rather than a marginal-law failure. -/
theorem mismatchingRecommendation_not_interim_obedient :
    ¬ ∀ who ownType recommended replacement,
      ∀ hObserved :
          ∃ rec ∈ game.obedienceEvent who ownType recommended,
            rec ∈ mismatchingRecommendation.support,
        game.interimDeviatingValue mismatchingRecommendation who ownType
              recommended replacement hObserved ≤
          game.interimRecommendedValue mismatchingRecommendation who ownType
            recommended hObserved := by
  intro hinterim
  apply mismatchingRecommendation_not_isBayesCorrelatedEq
  exact (game.isBayesCorrelatedEq_iff_interim_obedience
    mismatchingRecommendation).2
      ⟨mismatchingRecommendation_isBayesPlausible, hinterim⟩

end GameTheory.Tests.BayesCorrelated
