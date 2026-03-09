import GameTheory.Languages.EFG.SOS
import GameTheory.Theorems.Kuhn.ObsModel

/-!
# GameTheory.Languages.EFG.CompileObs

Compilation of EFG tree semantics into the `ObsModel` layer.

The compiled `ObsModel` treats each tree node as a stochastic transition:
chance nodes sample from their distribution, decision nodes read the acting
player's action deterministically. Terminal nodes are absorbing.

## Main definitions

- `compileObsModel G` : the observation model for an EFG game tree
-/

namespace GameTheory.EFG

open _root_.EFG

variable {S : InfoStructure} {Outcome : Type}

/-- Stochastic tree step: given a game tree node and joint player actions,
produce a distribution over successor tree nodes.

- **Chance**: sample from μ, ignore all actions
- **Decision** at infoset I of player p: extract p's action, move to successor
- **Terminal**: absorbing (identity) -/
noncomputable def treeStepPMF
    (t : GameTree S Outcome)
    (acts : ∀ p : S.Player, Option (CtrlAct S p)) :
    PMF (GameTree S Outcome) :=
  match t with
  | .terminal z => PMF.pure (.terminal z)
  | .chance _k μ _hk next => μ.map next
  | .decision (p := p) I next =>
      match acts p with
      | some ⟨I', act⟩ =>
          if h : I' = I then
            PMF.pure (next (h ▸ act))
          else
            PMF.pure (.decision I next)  -- invalid action, stay
      | none => PMF.pure (.decision I next)  -- no action, stay

/-- Compile an EFG game tree into the observation model layer.

- **States**: game tree nodes (`GameTree S Outcome`)
- **Players**: `Fin S.n`
- **Observations**: `Option (S.Infoset i)` (current infoset if acting, else none)
- **Actions**: `Option (CtrlAct S i)` (infoset + action pair, or idle)
- **Step**: stochastic resolution via `treeStepPMF`
-/
noncomputable def compileObsModel (t : GameTree S Outcome) :
    ObsModel S.Player (GameTree S Outcome)
      (fun i => Option (S.Infoset i))
      (fun (i : S.Player) (_ : Option (S.Infoset i)) =>
        Option (CtrlAct S i)) where
  observe := fun i s => obsOfState (S := S) (Outcome := Outcome) i s
  machine := {
    init := t
    step := fun s acts => treeStepPMF s acts
  }

end GameTheory.EFG
