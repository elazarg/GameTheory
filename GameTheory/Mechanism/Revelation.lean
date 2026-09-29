/-
# The revelation principle

Any pure Bayes-Nash plan of a canonical `BayesianGame` induces a direct
mechanism in which truthful reporting is Bayes-Nash, using the ordinary
Bayesian game and equilibrium predicates.
-/

import GameTheory.Mechanism.BayesianIncentives

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability Languages

universe uι ut ua

variable {ι : Type uι} [DecidableEq ι]

namespace BayesianGame

/-- The direct mechanism induced by a contingent plan.  Reports are types;
the mechanism applies the original plan to the reported profile, while utility
continues to use the true type profile. -/
@[reducible]
def toDirectMechanism (B : BayesianGame.{uι, ut, ua} ι)
    (plan : Profile B.signature) : BayesianMechanism ι where
  Ty := B.Ty
  Report := B.Ty
  Outcome := ∀ i, B.Act i
  truth _ ownType := ownType
  choose reports := B.actionsOf plan reports
  utility trueTypes actions who := B.payoff trueTypes actions who

variable (B : BayesianGame.{uι, ut, ua} ι) (plan : Profile B.signature)

omit [DecidableEq ι] in
@[simp]
theorem toDirectMechanism_truthfulReports (types : ∀ i, B.Ty i) :
    (B.toDirectMechanism plan).truthfulReports types = types :=
  rfl

omit [DecidableEq ι] in
@[simp]
theorem toDirectMechanism_choose_truthfulReports (types : ∀ i, B.Ty i) :
    (B.toDirectMechanism plan).choose
        ((B.toDirectMechanism plan).truthfulReports types) =
      B.actionsOf plan types :=
  rfl

/-- A type-contingent misreport in the direct mechanism realizes exactly the
action deviation obtained by composing the original plan with that report. -/
theorem toDirectMechanism_choose_update_truthfulReports
    (types : ∀ i, B.Ty i) (who : ι)
    (misreport : B.Ty who → B.Ty who) :
    (B.toDirectMechanism plan).choose
        (Profile.update
          ((B.toDirectMechanism plan).truthfulReports types) who
          (misreport (types who))) =
      B.actionsOf
        (Profile.update plan who (fun ownType => plan who (misreport ownType)))
        types := by
  funext i
  by_cases hi : i = who
  · subst hi
    simp [BayesianGame.actionsOf]
  · simp [BayesianGame.actionsOf, Profile.update_of_ne _ _ hi]

/-- **Revelation principle.** Every pure Bayes-Nash plan induces
a direct mechanism whose truthful plan is ordinary Nash of the compiled
Bayesian form.  No separate BNE or BIC predicate is introduced. -/
theorem revelation_principle
    (hNash : IsNash B.toForm (euPreference B.utility) plan) :
    let direct := B.toDirectMechanism plan
    IsNash (direct.toBayesianGame B.prior).toForm
      (euPreference (direct.toBayesianGame B.prior).utility)
      (direct.truthfulPlan B.prior) := by
  dsimp only
  rw [isNash_iff] at hNash ⊢
  intro who misreport
  let direct := B.toDirectMechanism plan
  let D := direct.toBayesianGame B.prior
  have hdeviation :=
    hNash who (fun ownType => plan who (misreport ownType))
  obtain ⟨hbase, hdev, hle⟩ := hdeviation
  have htruthPayoff (types : ∀ i, B.Ty i) :
      D.planPayoff who (direct.truthfulPlan B.prior) types =
        B.planPayoff who plan types := by
    simp only [BayesianGame.planPayoff, D, direct,
      Languages.BayesianMechanism.actionsOf_truthfulPlan]
    rfl
  have hdevPayoff (types : ∀ i, B.Ty i) :
      D.planPayoff who
          (Profile.update (direct.truthfulPlan B.prior) who misreport) types =
        B.planPayoff who
          (Profile.update plan who
            (fun ownType => plan who (misreport ownType))) types := by
    simp only [BayesianGame.planPayoff, D, direct,
      Languages.BayesianMechanism.actionsOf_update_truthfulPlan]
    exact congrArg (fun actions => B.payoff types actions who)
      (B.toDirectMechanism_choose_update_truthfulReports
        plan types who misreport)
  have htruthValue : extendedExpectedUtility D.utility who
      (D.toForm.play (direct.truthfulPlan B.prior)) =
        extendedExpectedUtility B.utility who (B.toForm.play plan) := by
    rw [D.extendedExpectedUtility_eq_prior, B.extendedExpectedUtility_eq_prior]
    exact extendedExpect_congr_on_support fun types _ => htruthPayoff types
  have hdevValue : extendedExpectedUtility D.utility who
      (D.toForm.play (Profile.update (direct.truthfulPlan B.prior) who misreport)) =
        extendedExpectedUtility B.utility who
          (B.toForm.play (Profile.update plan who
            (fun ownType => plan who (misreport ownType)))) := by
    rw [D.extendedExpectedUtility_eq_prior, B.extendedExpectedUtility_eq_prior]
    exact extendedExpect_congr_on_support fun types _ => hdevPayoff types
  have htruth : UtilityHasExpectation D.utility who
      (D.toForm.play (direct.truthfulPlan B.prior)) := by
    rw [D.utilityHasExpectation_iff_prior,
      hasExpectation_congr_on_support fun types _ => htruthPayoff types,
      ← B.utilityHasExpectation_iff_prior]
    exact hbase
  have hdirectDev : UtilityHasExpectation D.utility who
      (D.toForm.play (Profile.update (direct.truthfulPlan B.prior) who misreport)) := by
    rw [D.utilityHasExpectation_iff_prior,
      hasExpectation_congr_on_support fun types _ => hdevPayoff types,
      ← B.utilityHasExpectation_iff_prior]
    exact hdev
  refine ⟨htruth, hdirectDev, ?_⟩
  rw [htruthValue, hdevValue]
  exact hle

end BayesianGame

end GameTheory
