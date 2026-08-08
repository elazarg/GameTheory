/-
# Truthful welfare and participation for Bayesian mechanisms

These are transparent aggregates and certificates over the canonical direct
mechanism.  They do not introduce a second mechanism, equilibrium predicate,
or utility semantics.
-/

import GameTheory.Languages.BayesianMechanism

noncomputable section

open scoped BigOperators

namespace GameTheory.Languages.BayesianMechanism

universe uι ut ur uo

variable {ι : Type uι} [DecidableEq ι]
variable (M : BayesianMechanism.{uι, ut, ur, uo} ι)

/-- Realized utility when every player sends its designated truthful report. -/
def truthfulUtility (types : ∀ i, M.Ty i) (who : ι) : ℝ :=
  M.utility types (M.choose (M.truthfulReports types)) who

/-- Utilitarian welfare under truthful reporting.  Player finiteness belongs
on this aggregate operation rather than on the mechanism. -/
def truthfulSocialWelfare [Fintype ι] (types : ∀ i, M.Ty i) : ℝ :=
  ∑ who, M.truthfulUtility types who

/-- Ex-post individual rationality relative to an explicit outside option for
each player. -/
def IsExPostIndividuallyRational (outsideOption : ι → ℝ) : Prop :=
  ∀ types who, outsideOption who ≤ M.truthfulUtility types who

/-- Zero-normalized ex-post individual rationality. -/
def IsExPostNonnegative : Prop :=
  M.IsExPostIndividuallyRational fun _ => 0

omit [DecidableEq ι] in
theorem isExPostNonnegative_iff :
    M.IsExPostNonnegative ↔
      M.IsExPostIndividuallyRational (fun _ => 0) :=
  Iff.rfl

end GameTheory.Languages.BayesianMechanism
