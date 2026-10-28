module

/-
# Ex-post equilibrium and uncertainty about another player's type

Truthful matching is ex-post optimal for every prior. In the guessing game,
the first player cannot observe the second player's fair type. Every constant
guess is Bayes-Nash, but a wrong guess fails ex-post at a positive-mass profile.
-/

public import GameTheory.Core.BayesianEquilibrium

@[expose] public section

noncomputable section

namespace GameTheory.Tests.BayesianExPost

open GameTheory.Math.Probability

/-- Matching one's observed type is optimal for every prior. -/
@[reducible]
def matchingGame (prior : PMF (Unit → Bool)) : BayesianGame Unit where
  Ty _ := Bool
  Act _ := Bool
  prior := prior
  payoff types actions _ := if actions () = types () then 1 else 0

theorem matching_isExPostNash (prior : PMF (Unit → Bool)) :
    (matchingGame prior).IsExPostNash (fun _ ownType => ownType) := by
  rw [BayesianGame.isExPostNash_iff]
  intro types who alternative
  cases who
  simp only [matchingGame, BayesianGame.actionsOf, Profile.update_same, ↓reduceIte]
  split <;> norm_num

theorem matching_isNash (prior : PMF (Unit → Bool)) :
    IsNash (matchingGame prior).toForm
      (euPreference (matchingGame prior).utility) (fun _ ownType => ownType) :=
  BayesianGame.IsExPostNash.isNash _ _ (matching_isExPostNash prior)
    (fun _ _ => payoffIntegrable_of_finite _ _)

def firstTypes : Bool → Bool := fun _ => false

def secondTypes : Bool → Bool := id

def guessingPrior : PMF (Bool → Bool) :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure firstTypes) (PMF.pure secondTypes)

/-- Player `false` guesses player `true`'s unobserved type; the other player
has zero payoff. The guesser's own type is always `false`. -/
@[reducible]
def guessingGame : BayesianGame Bool where
  Ty _ := Bool
  Act _ := Bool
  prior := guessingPrior
  payoff types actions who := if who then 0 else
    if actions false = types true then 1 else 0

def constantGuess : Profile guessingGame.signature := fun _ _ => false

private theorem guessing_value (plan : Profile guessingGame.signature) (who : Bool) :
    expectedUtility guessingGame.utility who (guessingGame.toForm.play plan) =
      if who then 0 else 1 / 2 := by
  rw [guessingGame.expectedUtility_eq_prior]
  unfold guessingGame guessingPrior
  rw [expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _)]
  simp only [expect_pure, BayesianGame.planPayoff, BayesianGame.actionsOf,
    firstTypes, secondTypes, id_eq]
  rcases Bool.eq_false_or_eq_true (plan false false) with hguess | hguess <;>
    cases who <;> norm_num [hguess]

theorem constantGuess_isNash :
    IsNash guessingGame.toForm (euPreference guessingGame.utility) constantGuess := by
  rw [isNash_iff]
  intro who deviation
  apply (euPreference_iff _ _ _ _
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).2
  rw [guessing_value, guessing_value]

/-- Failure is on a positive-probability type profile, not a null event. -/
theorem secondTypes_positive : 0 < guessingGame.prior secondTypes := by
  simp only [guessingGame, guessingPrior, mix_apply]
  have hne : firstTypes ≠ secondTypes := by
    intro h
    have ht := congrFun h true
    simp [firstTypes, secondTypes] at ht
  norm_num [PMF.pure_apply, Ne.symm hne]

theorem constantGuess_not_isExPostNash :
    ¬ guessingGame.IsExPostNash constantGuess := by
  intro h
  have hwrong := (guessingGame.isExPostNash_iff constantGuess).mp h secondTypes false true
  norm_num [guessingGame, secondTypes, constantGuess, BayesianGame.actionsOf,
    Profile.update_same] at hwrong

end GameTheory.Tests.BayesianExPost
