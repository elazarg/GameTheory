/-
# Bayesian direct mechanisms

A Bayesian mechanism keeps true types separate from reports. Its utility reads
the true type profile and the chosen outcome; a misreport therefore cannot
silently change the type used to evaluate the deviator.

The compiler makes reports the actions of an ordinary `BayesianGame`.
Truthful Bayes-Nash is then the existing `IsNash` predicate on that game's
direct contingent-plan form.
-/

import GameTheory.Core.BayesianEquilibrium

noncomputable section

namespace GameTheory.Languages

open GameTheory Probability

universe uι ut ur uo

set_option linter.checkUnivs false in
/-- A direct mechanism with an explicit truthful report for each private type
and utility evaluated at the true type profile. -/
structure BayesianMechanism (ι : Type uι) where
  /-- Private type of player `i`. -/
  Ty : ι → Type ut
  /-- Report accepted from player `i`. -/
  Report : ι → Type ur
  /-- Outcome chosen from the report profile. -/
  Outcome : Type uo
  /-- The report encoding truthful revelation of one type. -/
  truth : ∀ i, Ty i → Report i
  /-- Outcome rule. -/
  choose : (∀ i, Report i) → Outcome
  /-- Utility at the true type profile and chosen outcome. -/
  utility : (∀ i, Ty i) → Outcome → ι → ℝ

namespace BayesianMechanism

variable {ι : Type uι} [DecidableEq ι]
variable (M : BayesianMechanism.{uι, ut, ur, uo} ι)

/-- Signature of reports, used only to reuse the canonical profile update. -/
abbrev reportSignature : GameSignature ι where
  Strategy := M.Report
  Outcome := M.Outcome

/-- Truthful report profile at a realized type profile. -/
def truthfulReports (types : ∀ i, M.Ty i) :
    Profile M.reportSignature :=
  fun i => M.truth i (types i)

/-- Dominant-strategy incentive compatibility: truth beats every report for
every true type profile and every fixed profile of opponents' reports. -/
def IsIncentiveCompatible : Prop :=
  ∀ (who : ι) (types : ∀ i, M.Ty i)
    (reports : Profile M.reportSignature) (misreport : M.Report who),
    M.utility types
        (M.choose (Profile.update reports who misreport)) who ≤
      M.utility types
        (M.choose
          (Profile.update reports who (M.truth who (types who)))) who

/-- Compile a prior and direct mechanism to the accepted Bayesian-game
semantics. Reports are actions; payoff uses true types separately. -/
@[reducible]
def toBayesianGame (prior : FinDist (∀ i, M.Ty i)) :
    BayesianGame ι where
  Ty := M.Ty
  Act := M.Report
  prior := prior
  payoff types reports who :=
    M.utility types (M.choose reports) who

/-- The contingent plan that reports truthfully at every own type. -/
def truthfulPlan (prior : FinDist (∀ i, M.Ty i)) :
    Profile (M.toBayesianGame prior).signature :=
  fun i ownType => M.truth i ownType

omit [DecidableEq ι] in
@[simp]
theorem actionsOf_truthfulPlan (prior : FinDist (∀ i, M.Ty i))
    (types : ∀ i, M.Ty i) :
    (M.toBayesianGame prior).actionsOf (M.truthfulPlan prior) types =
      M.truthfulReports types :=
  rfl

/-- Updating the truthful contingent plan realizes the corresponding update
of the truthful report profile. -/
theorem actionsOf_update_truthfulPlan
    (prior : FinDist (∀ i, M.Ty i)) (who : ι)
    (deviation : M.Ty who → M.Report who)
    (types : ∀ i, M.Ty i) :
    (M.toBayesianGame prior).actionsOf
        (Profile.update (M.truthfulPlan prior) who deviation) types =
      Profile.update (M.truthfulReports types) who
        (deviation (types who)) := by
  rw [BayesianGame.actionsOf_update, M.actionsOf_truthfulPlan]
  rfl

/-- **Incentive compatibility implies truthful Bayes-Nash.** The conclusion is
ordinary Nash of the compiled Bayesian game form, with no second Bayesian
equilibrium predicate. -/
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
