/-
# Factored-observation stochastic games

A FOSG is the general sequential specialization: legal simultaneous actions
and stochastic transitions are one accepted `ExecutionProtocol`, while public
and private observations, local information, and menus are its accepted
`InformationModel`.

There is deliberately no FOSG-specific runner, history, strategy, utility, or
solution predicate. Compilation delegates to `InformationModel.toGameForm`.
-/

import GameTheory.Protocol.Strategic

noncomputable section

namespace GameTheory.Languages.FOSG

open GameTheory GameTheory.Protocol

universe uι us ua up uq uk

set_option linter.checkUnivs false in
/-- A factored-observation stochastic game uses the accepted execution object
and its information model directly. It owns no second runner or history type. -/
structure Game (ι : Type uι) where
  /-- Legal simultaneous actions and stochastic transitions. -/
  execution : ExecutionProtocol.{uι, us, ua} ι
  /-- Public/private observations, local information, and legal local menus. -/
  information : InformationModel.{uι, us, ua, up, uq, uk} execution

namespace Game

variable {ι : Type uι} (G : Game ι)

/-- FOSG histories are canonical Protocol histories. -/
abbrev History := G.execution.History

/-- Compile information-local pure policies using the canonical history
runner. -/
@[reducible]
def toGameForm (horizon : ℕ) : GameForm ι :=
  G.information.toGameForm horizon

@[simp]
theorem toGameForm_play (horizon : ℕ)
    (profile : Profile G.information.strategicSignature) :
    (G.toGameForm horizon).play profile =
      G.information.run profile horizon := rfl

end Game

end GameTheory.Languages.FOSG
