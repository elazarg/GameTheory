import GameTheory.Model.InfoGame
import GameTheory.Languages.EFG.Syntax

namespace GameTheory.EFG

open _root_.EFG

/-- EFG controller action alphabet at player `i`: infoset paired with a local
action admissible at that infoset. -/
abbrev CtrlAct (S : _root_.EFG.InfoStructure) (i : S.Player) : Type :=
  Sigma (fun I : S.Infoset i => S.Act I)

/-- Compile an EFG tree to the generic latent-state machine layer.

- states are EFG subtrees
- joint actions are controller actions for the currently active player, with
  all other coordinates inactive
- chance moves are compiled as all-player inactivity, with the latent state
  choosing the realized branch -/
def compileLSM {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome) : GameTheory.LSM S.Player where
  State := _root_.EFG.GameTree S Outcome
  Act := CtrlAct S
  init := t
  step := fun a s s' =>
    match s with
    | .terminal _ => False
    | .chance _k _μ _hk next =>
        (∀ i, a i = none) ∧ ∃ b, s' = next b
    | .decision (p := p) I next =>
        ∃ act : S.Act I,
          a p = some ⟨I, act⟩ ∧
          (∀ q, q ≠ p → a q = none) ∧
          s' = next act

/-- Public component exposed by the EFG compilation.

The compiled state-based semantics does not attempt to reconstruct the public
history from the current subtree, so the public view is kept trivial here. The
syntax-level public trace is handled separately in `EFG.SOS`. -/
abbrev PublicObs : Type := PUnit

/-- Local observation token extracted from a state for player `i`: the current
infoset when `i` moves, and `none` otherwise. -/
def obsOfState {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (i : S.Player) : _root_.EFG.GameTree S Outcome → Option (S.Infoset i)
  | .decision (p := p) I _ =>
      if h : p = i then
        by
          subst h
          exact some I
      else none
  | _ => none

/-- Compile EFG visibility to the generic `InfoModel` layer. Public visibility
is trivial at the state layer; private visibility is the current infoset, if
any, for the acting player. -/
def compileInfoOn {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome) :
    GameTheory.InfoModel (compileLSM (S := S) (Outcome := Outcome) t) where
  Public := PublicObs
  publicView := fun _ => PUnit.unit
  Obs := fun i => Option (S.Infoset i)
  observe := fun i s => obsOfState (S := S) (Outcome := Outcome) i s

/-- Build a pure-utility control model from local utility functionals over the
private infoset history seen by each player. -/
def compileControlUtility {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    (u : ∀ i : S.Player,
      List (Option (S.Infoset i)) → ℝ) :
    GameTheory.ControlModel (compileLSM (S := S) (Outcome := Outcome) t)
      (compileInfoOn (S := S) (Outcome := Outcome) t) where
  control := fun i => GameTheory.ControlSpec.utility (u i)

/-- Compile an EFG together with common-knowledge utility specifications into
the game-level `InfoGame` target. -/
def compileInfoGameUtility {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    (u : ∀ i : S.Player,
      List (Option (S.Infoset i)) → ℝ) :
    GameTheory.InfoGame (ι := S.Player) :=
  .ofControlModel <| compileControlUtility (S := S) (Outcome := Outcome) t u

/-- Build a pure-behavior control model from local behavior laws over each
player's private infoset history. -/
def compileControlBehavior {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    (β : ∀ i : S.Player,
      List (Option (S.Infoset i)) → PMF (Option (CtrlAct S i))) :
    GameTheory.ControlModel (compileLSM (S := S) (Outcome := Outcome) t)
      (compileInfoOn (S := S) (Outcome := Outcome) t) where
  control := fun i => GameTheory.ControlSpec.behavior (β i)

/-- Compile an EFG together with common-knowledge behavior specifications into
the game-level `InfoGame` target. -/
def compileInfoGameBehavior {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    (β : ∀ i : S.Player,
      List (Option (S.Infoset i)) → PMF (Option (CtrlAct S i))) :
    GameTheory.InfoGame (ι := S.Player) :=
  .ofControlModel <| compileControlBehavior (S := S) (Outcome := Outcome) t β

end GameTheory.EFG
