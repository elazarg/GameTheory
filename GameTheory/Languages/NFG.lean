/-
# Deterministic normal-form syntax

`NFG.Game` is utility-free syntax for a deterministic normal-form game. It
compiles directly to the canonical `GameForm`; utility, finiteness, executable
algorithms, deviations, and solution concepts remain in the layers that own
them.

This syntax module imports no Protocol, utility, preference, equilibrium,
finite algorithm, or Analysis module.
-/

import GameTheory.Core.Form

noncomputable section

namespace GameTheory.Languages.NFG

open GameTheory GameTheory.Probability

universe uι ua uo

set_option linter.checkUnivs false in
/-- Utility-free deterministic normal-form syntax. Capabilities such as
finiteness and utilities belong to the operations that need them. -/
structure Game (ι : Type uι) where
  /-- Each player's action carrier. -/
  Action : ι → Type ua
  /-- The outcome carrier. -/
  Outcome : Type uo
  /-- The outcome selected by a pure action profile. -/
  outcome : (∀ i, Action i) → Outcome

namespace Game

variable {ι : Type uι} (G : Game ι)

/-- The canonical static signature of a normal-form game. -/
abbrev signature : GameSignature ι where
  Strategy := G.Action
  Outcome := G.Outcome

/-- Deterministic normal-form syntax compiles directly to the canonical static
form. It introduces no language-specific deviation or equilibrium predicate. -/
@[reducible]
def toGameForm : GameForm ι :=
  GameForm.deterministic G.signature G.outcome

@[simp]
theorem toGameForm_play (profile : Profile G.signature) :
    G.toGameForm.play profile = FinDist.pure (G.outcome profile) := rfl

end Game

end GameTheory.Languages.NFG
