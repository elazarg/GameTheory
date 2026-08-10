/-
# The finite revelation principle

Any pure Bayes-Nash plan of a canonical `BayesianGame` induces a direct
mechanism in which truthful reporting is Bayes-Nash, using the ordinary
Bayesian game and equilibrium predicates.
-/

import GameTheory.Mechanism.BayesianIncentives

noncomputable section

namespace GameTheory

open Probability Languages

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

/-- **Finite-support revelation principle.** Every pure Bayes-Nash plan induces
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
  have hdeviation :=
    hNash who (fun ownType => plan who (misreport ownType))
  rw [euPreference_apply] at hdeviation ⊢
  unfold expectedUtility at hdeviation ⊢
  rw [BayesianGame.toForm_play, FinDist.expect_map,
    BayesianGame.toForm_play, FinDist.expect_map] at hdeviation ⊢
  calc
    _ = B.prior.expect fun types =>
        B.utility
          (types,
            B.actionsOf
              (Profile.update plan who
                (fun ownType => plan who (misreport ownType)))
              types) who := by
      apply FinDist.expect_congr
      intro types _
      rw [Languages.BayesianMechanism.actionsOf_update_truthfulPlan]
      simp only [BayesianGame.utility]
      exact congrArg (fun actions => B.payoff types actions who)
        (B.toDirectMechanism_choose_update_truthfulReports
          plan types who misreport)
    _ ≤ B.prior.expect fun types =>
        B.utility (types, B.actionsOf plan types) who := hdeviation
    _ = _ := by
      apply FinDist.expect_congr
      intro types _
      rw [Languages.BayesianMechanism.actionsOf_truthfulPlan]
      simp only [BayesianGame.utility]
      exact congrArg (fun actions => B.payoff types actions who)
        (B.toDirectMechanism_choose_truthfulReports plan types).symm

end BayesianGame

end GameTheory
