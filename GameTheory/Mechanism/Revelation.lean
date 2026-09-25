/-
# The guarded revelation principle

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

/-- **Guarded revelation principle.** Every pure Bayes-Nash plan induces
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
  rw [euPreference_apply] at hdeviation ⊢
  rcases hdeviation with ⟨hbase, hdev, hle⟩
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
  have htruthPrior : PayoffIntegrable B.prior
      (D.planPayoff who (direct.truthfulPlan B.prior)) :=
    payoffIntegrable_congr_on_support
      (fun types _ => (htruthPayoff types).symm)
      (B.planPayoff_integrable who plan hbase)
  have hdevPrior : PayoffIntegrable B.prior
      (D.planPayoff who
        (Profile.update (direct.truthfulPlan B.prior) who misreport)) :=
    payoffIntegrable_congr_on_support
      (fun types _ => (hdevPayoff types).symm)
      (B.planPayoff_integrable who
        (Profile.update plan who
          (fun ownType => plan who (misreport ownType))) hdev)
  have htruth : UtilityIntegrable D.utility who
      (D.toForm.play (direct.truthfulPlan B.prior)) := by
    exact (payoffIntegrable_map_iff
      (fun types => (types, D.actionsOf (direct.truthfulPlan B.prior) types))
      B.prior (fun outcome => D.utility outcome who)).mpr htruthPrior
  have hdirectDev : UtilityIntegrable D.utility who
      (D.toForm.play
        (Profile.update (direct.truthfulPlan B.prior) who misreport)) := by
    exact (payoffIntegrable_map_iff
      (fun types => (types,
        D.actionsOf
          (Profile.update (direct.truthfulPlan B.prior) who misreport) types))
      B.prior (fun outcome => D.utility outcome who)).mpr hdevPrior
  refine ⟨htruth, hdirectDev, ?_⟩
  rw [D.expectedUtility_eq_prior who
      (Profile.update (direct.truthfulPlan B.prior) who misreport) hdirectDev,
    D.expectedUtility_eq_prior who (direct.truthfulPlan B.prior) htruth,
    B.expectedUtility_eq_prior who
      (Profile.update plan who
        (fun ownType => plan who (misreport ownType))) hdev,
    B.expectedUtility_eq_prior who plan hbase] at *
  calc
    expect B.prior
        (D.planPayoff who
          (Profile.update (direct.truthfulPlan B.prior) who misreport))
        (D.planPayoff_integrable who _ hdirectDev) =
      expect B.prior
        (B.planPayoff who
          (Profile.update plan who
            (fun ownType => plan who (misreport ownType))))
        (B.planPayoff_integrable who _ hdev) :=
          expect_congr_on_support (fun types _ => hdevPayoff types) _ _
    _ ≤ expect B.prior (B.planPayoff who plan)
        (B.planPayoff_integrable who plan hbase) := hle
    _ = expect B.prior (D.planPayoff who (direct.truthfulPlan B.prior))
        (D.planPayoff_integrable who _ htruth) :=
          expect_congr_on_support
            (fun types _ => (htruthPayoff types).symm) _ _

end BayesianGame

end GameTheory
