import GameTheory.Languages.EFG.Syntax

/-!
# EFG Examples

Reader-facing extensive-form examples.

Compilation/SOS validation belongs in `GameTheory.Languages.EFG.Tests`.
-/

namespace GameTheory.EFG.Examples

open _root_.EFG

/-- A one-player information structure with a single binary infoset. -/
def oneInfo : InfoStructure where
  n := 1
  Infoset := fun _ => PUnit
  arity := fun _ _ => 2
  arity_pos := by
    intro _ _
    exact Nat.succ_pos 1

/-- The unique player in `oneInfo`. -/
def p0 : oneInfo.Player := ⟨0, by decide⟩

/-- A minimal binary decision tree. -/
def binaryChoiceTree : GameTree oneInfo Bool :=
  .decision (p := p0) PUnit.unit (fun a =>
    if a.1 = 0 then .terminal false else .terminal true)

/-- A tiny extensive-form game built from `binaryChoiceTree`. -/
def binaryChoiceGame : EFGGame where
  inf := oneInfo
  Outcome := Bool
  tree := binaryChoiceTree
  utility := fun b _ =>
    if b then 1 else 0

end GameTheory.EFG.Examples
