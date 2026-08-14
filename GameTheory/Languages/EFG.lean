/-
# Extensive forms as a transparent Protocol specialization

An extensive-form game is not given a second tree evaluator here. Its execution
and information semantics are exactly the accepted Protocol objects, together
with the two structural laws that distinguish an EFG from a general protocol:
reachable histories form a tree and at most one player moves at a state.
States with no active player are ordinary Protocol chance states.

Finiteness remains a capability of the theorem that needs it. In particular,
`Game` stores no `Fintype`; a finite state carrier plus tree-shapedness yields
an explicit history enumeration through `historyFintype`.

This syntax module imports no utility, preference, solution concept, or
Analysis module.
-/

import GameTheory.Languages.FOSG

noncomputable section

namespace GameTheory.Languages.EFG

open GameTheory.Protocol

universe uι us ua up uq uk

set_option linter.checkUnivs false in
/-- A Protocol presentation satisfying the structural laws of an
extensive-form game. -/
structure Game (ι : Type uι) where
  /-- The canonical execution semantics; no language-specific runner exists. -/
  execution : ExecutionProtocol.{uι, us, ua} ι
  /-- The canonical information semantics over that execution. -/
  information : InformationModel.{uι, us, ua, up, uq, uk} execution
  /-- Every reached state has at most one history. -/
  treeShaped : execution.IsTreeShaped
  /-- Decision states have at most one active player. -/
  singleMover :
    ∀ (state : execution.State) {first second : ι},
      execution.active state first →
      execution.active state second →
      first = second

namespace Game

variable {ι : Type uι} (G : Game ι)

/-- Forget the tree-shaped and single-mover certificates and view an EFG as
the canonical factored-observation stochastic game with the same execution and
information objects.  This is a structural projection, not a serialization or
a second evaluator. -/
@[reducible]
def toFOSG : FOSG.Game ι where
  execution := G.execution
  information := G.information

@[simp]
theorem toFOSG_execution : G.toFOSG.execution = G.execution := rfl

@[simp]
theorem toFOSG_information : G.toFOSG.information = G.information := rfl

/-- The EFG history type is the Protocol history type, definitionally. -/
abbrev History := G.execution.History

/-- A finite state carrier makes a tree-shaped EFG's histories explicitly
finite. This is a capability supplied at use, not stored in `Game`. -/
@[reducible]
noncomputable def historyFintype [Fintype G.execution.State] :
    Fintype G.History :=
  G.execution.historyFintype G.treeShaped

/-- Two active players at one EFG state are the same player. -/
theorem active_eq {state : G.execution.State} {first second : ι}
    (hfirst : G.execution.active state first)
    (hsecond : G.execution.active state second) :
    first = second :=
  G.singleMover state hfirst hsecond

end Game

end GameTheory.Languages.EFG
