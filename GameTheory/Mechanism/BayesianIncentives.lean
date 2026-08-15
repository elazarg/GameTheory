/-
# Incentives for Bayesian direct mechanisms

The direct-mechanism language is compiled first.  This solution leaf adds the
pointwise incentive predicate and proves that it yields ordinary Nash of the
canonical Bayesian contingent-plan form.
-/

import GameTheory.Languages.BayesianMechanism
import GameTheory.Core.BayesianEquilibrium

noncomputable section

namespace GameTheory.Languages

open GameTheory GameTheory.Math.Probability

universe uι ut ur uo

namespace BayesianMechanism

variable {ι : Type uι} [DecidableEq ι]
variable (M : BayesianMechanism.{uι, ut, ur, uo} ι)

/-- Dominant-strategy incentive compatibility: truth beats every report for
every true type profile and fixed profile of opponents' reports. -/
def IsIncentiveCompatible : Prop :=
  ∀ (who : ι) (types : ∀ i, M.Ty i)
    (reports : Profile M.reportSignature) (misreport : M.Report who),
    M.utility types
        (M.choose (Profile.update reports who misreport)) who ≤
      M.utility types
        (M.choose
          (Profile.update reports who (M.truth who (types who)))) who

/-- Pointwise incentive compatibility implies ordinary Nash of the compiled
Bayesian game under truthful contingent reporting. -/
theorem isNash_truthfulPlan_of_isIncentiveCompatible
    (prior : FinDist (∀ i, M.Ty i))
    (hIC : M.IsIncentiveCompatible) :
    IsNash (M.toBayesianGame prior).toForm
      (euPreference (M.toBayesianGame prior).utility)
      (M.truthfulPlan prior) := by
  rw [isNash_iff]
  intro who deviation
  rw [euPreference_apply]
  unfold expectedUtility
  rw [BayesianGame.toForm_play, FinDist.expect_map,
    BayesianGame.toForm_play, FinDist.expect_map]
  apply FinDist.expect_mono
  intro types _
  rw [M.actionsOf_update_truthfulPlan, M.actionsOf_truthfulPlan]
  have hpoint :=
    hIC who types (M.truthfulReports types) (deviation (types who))
  show
    M.utility types
        (M.choose
          (Profile.update (M.truthfulReports types) who
            (deviation (types who)))) who ≤
      M.utility types (M.choose (M.truthfulReports types)) who
  have hreport :
      M.truth who (types who) = M.truthfulReports types who := rfl
  rw [hreport, Profile.update_eq_self] at hpoint
  exact hpoint

end BayesianMechanism

end GameTheory.Languages
