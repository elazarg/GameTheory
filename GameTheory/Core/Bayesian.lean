/-
# Finite Bayesian game forms

A common-prior Bayesian game has two static presentations: realized actions and
type-contingent plans. This module owns only that data and its direct
`GameForm`; utility and equilibrium theory live in `BayesianEquilibrium`, so a
language compiler may reuse the syntax without importing solution concepts.

Finiteness is deliberately absent from the structure. The common prior already
has finite support, while enumerating every value of one player's type is a
capability needed only by the interim decomposition theorem.
-/

import GameTheory.Core.Form

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι ut ua

set_option linter.checkUnivs false in
/-- A common-prior Bayesian game. Payoffs may depend on the full realized type
and action profiles, but a strategy below receives only its owner's type. -/
structure BayesianGame (ι : Type uι) where
  /-- Each player's private type. -/
  Ty : ι → Type ut
  /-- Each player's feasible action. -/
  Act : ι → Type ua
  /-- The common prior over type profiles. -/
  prior : FinDist (∀ i, Ty i)
  /-- Realized payoff as a function of types, actions, and the player paid. -/
  payoff : (∀ i, Ty i) → (∀ i, Act i) → ι → ℝ

namespace BayesianGame

/-- The signature of realized action profiles. -/
abbrev actionSignature (B : BayesianGame ι) : GameSignature ι where
  Strategy := B.Act
  Outcome := Unit

/-- The signature of type-contingent pure plans. -/
abbrev signature (B : BayesianGame ι) : GameSignature ι where
  Strategy i := B.Ty i → B.Act i
  Outcome := (∀ i, B.Ty i) × (∀ i, B.Act i)

/-- The action profile realized when `plan` meets `types`. Each coordinate can
read only its own type. -/
def actionsOf (B : BayesianGame ι) (plan : Profile B.signature)
    (types : ∀ i, B.Ty i) : Profile B.actionSignature :=
  fun i => plan i (types i)

/-- Updating one contingent plan updates exactly the corresponding realized
action at every type profile. -/
theorem actionsOf_update (B : BayesianGame ι) [DecidableEq ι]
    (plan : Profile B.signature) (who : ι)
    (replacement : B.Ty who → B.Act who) (types : ∀ i, B.Ty i) :
    B.actionsOf (Profile.update plan who replacement) types =
      Profile.update (B.actionsOf plan types) who
        (replacement (types who)) := by
  funext i
  by_cases hi : i = who
  · subst hi
    simp [actionsOf]
  · simp [actionsOf, Profile.update_of_ne _ _ hi]

/-- The direct ex-ante strategic form: draw a type profile, then apply each
player's contingent plan to its own coordinate. -/
@[reducible]
def toForm (B : BayesianGame ι) : GameForm ι where
  sig := B.signature
  play plan := B.prior.map fun types => (types, B.actionsOf plan types)

@[simp]
theorem toForm_play (B : BayesianGame ι) (plan : Profile B.signature) :
    B.toForm.play plan =
      B.prior.map fun types => (types, B.actionsOf plan types) := rfl

end BayesianGame

end GameTheory
