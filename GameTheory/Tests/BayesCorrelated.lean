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

open Probability

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

/-- The Bayes-Nash plan induces a Bayes-plausible and obedient recommendation
law in the original game. -/
theorem outcomeLaw_isBayesCorrelatedEq :
    game.IsBayesCorrelatedEq (information.outcomeLaw matchingPlan) :=
  information.isBayesCorrelatedEq_outcomeLaw_of_isNash
    matchingPlan matchingPlan_isNash

end GameTheory.Tests.BayesCorrelated
