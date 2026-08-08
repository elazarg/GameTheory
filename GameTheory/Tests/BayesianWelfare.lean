/-
Hostile truthful-welfare and participation regression.

Truth is the nonidentity Boolean flip.  Both players obtain positive but
unequal truthful utilities, so the aggregate and a nonzero outside-option
profile are observable.  Raising one outside option refutes participation.
-/

import GameTheory.Mechanism.BayesianWelfare

noncomputable section

namespace GameTheory.Tests.BayesianWelfare

open Languages

@[reducible]
def mechanism : BayesianMechanism Bool where
  Ty _ := Bool
  Report _ := Bool
  Outcome := Bool → Bool
  truth _ ownType := !ownType
  choose reports := reports
  utility types outcome who :=
    if outcome who = !types who then if who then 1 else 2 else -4

def acceptedOutsideOption : Bool → ℝ
  | false => 3 / 2
  | true => 1 / 2

def rejectedOutsideOption : Bool → ℝ
  | false => 3 / 2
  | true => 3 / 2

theorem truthful_report_is_nonidentity :
    mechanism.truth false false = true :=
  rfl

theorem truthful_utilities (types : Bool → Bool) :
    mechanism.truthfulUtility types false = 2 ∧
      mechanism.truthfulUtility types true = 1 := by
  simp [BayesianMechanism.truthfulUtility,
    BayesianMechanism.truthfulReports]

theorem truthful_socialWelfare (types : Bool → Bool) :
    mechanism.truthfulSocialWelfare types = 3 := by
  norm_num [BayesianMechanism.truthfulSocialWelfare, truthful_utilities]

theorem accepts_nonzero_outside_option :
    mechanism.IsExPostIndividuallyRational acceptedOutsideOption := by
  intro types who
  cases who <;>
    norm_num [BayesianMechanism.truthfulUtility,
      BayesianMechanism.truthfulReports, acceptedOutsideOption]

theorem rejects_higher_outside_option :
    ¬mechanism.IsExPostIndividuallyRational rejectedOutsideOption := by
  intro hir
  have h := hir (fun _ => false) true
  norm_num [BayesianMechanism.truthfulUtility,
    BayesianMechanism.truthfulReports, rejectedOutsideOption] at h

theorem truthful_payoffs_are_nonnegative :
    mechanism.IsExPostNonnegative := by
  rw [BayesianMechanism.isExPostNonnegative_iff]
  intro types who
  cases who <;>
    norm_num [BayesianMechanism.truthfulUtility,
      BayesianMechanism.truthfulReports]

end GameTheory.Tests.BayesianWelfare
