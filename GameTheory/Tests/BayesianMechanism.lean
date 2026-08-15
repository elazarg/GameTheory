/-
Hostile Bayesian-mechanism integration probe.

One player has a fair Boolean type and reports a Boolean outcome. Truth earns
one and a lie earns zero. The mechanism is incentive compatible pointwise,
compiles to ordinary Bayes-Nash, and its truthful recommendation law is
Bayes-correlated. The explicit false-type lie prevents the result from passing
only because payoffs or the prior are degenerate.
-/

import GameTheory.Core.BayesCorrelated
import GameTheory.Mechanism.BayesianIncentives

noncomputable section

namespace GameTheory.Tests.BayesianMechanism

open GameTheory.Math.Probability
open Languages

def falseTypes : Unit → Bool := fun _ => false

def trueTypes : Unit → Bool := fun _ => true

def prior : FinDist (Unit → Bool) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure falseTypes) (FinDist.pure trueTypes)

/-- The chosen outcome is the sole report, while utility compares it with the
true type rather than treating the report as the type. -/
@[reducible]
def mechanism : Languages.BayesianMechanism Unit where
  Ty _ := Bool
  Report _ := Bool
  Outcome := Bool
  truth _ ownType := ownType
  choose reports := reports ()
  utility types outcome _ := if outcome = types () then 1 else 0

theorem mechanism_isIncentiveCompatible :
    mechanism.IsIncentiveCompatible := by
  intro who types reports misreport
  cases who
  simp [mechanism]
  split <;> norm_num

/-- The hostile branch is genuine: for the false type, truth pays one and the
opposite report pays zero. -/
theorem false_truth_beats_lie :
    mechanism.utility falseTypes
          (mechanism.choose (mechanism.truthfulReports falseTypes)) () = 1 ∧
      mechanism.utility falseTypes
          (mechanism.choose
            (Profile.update (mechanism.truthfulReports falseTypes) () true)) () = 0 := by
  simp [mechanism, falseTypes,
    Languages.BayesianMechanism.truthfulReports]

/-- Incentive compatibility transfers to the one accepted Bayesian-equilibrium
predicate: ordinary Nash of the compiled contingent-plan form. -/
theorem truthful_isNash :
    IsNash (mechanism.toBayesianGame prior).toForm
      (euPreference (mechanism.toBayesianGame prior).utility)
      (mechanism.truthfulPlan prior) :=
  mechanism.isNash_truthfulPlan_of_isIncentiveCompatible
    prior mechanism_isIncentiveCompatible

/-- Truthful compilation feeds the Bayes-correlated outcome-law theorem
directly. -/
theorem truthfulRecommendation_isBayesCorrelatedEq :
    (mechanism.toBayesianGame prior).IsBayesCorrelatedEq
      ((mechanism.toBayesianGame prior).strategyRecommendationLaw
        (mechanism.truthfulPlan prior)) :=
  (mechanism.toBayesianGame prior)
    |>.isBayesCorrelatedEq_strategyRecommendationLaw_of_isNash
      (mechanism.truthfulPlan prior) truthful_isNash

end GameTheory.Tests.BayesianMechanism
