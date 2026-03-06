import GameTheory.Languages.EFG.Compile
import GameTheory.Languages.EFG.SOS

namespace GameTheory
namespace Languages
namespace EFG
namespace Tests

open _root_.EFG

noncomputable section

def oneInfo : InfoStructure where
  n := 1
  Infoset := fun _ => PUnit
  arity := fun _ _ => 2
  arity_pos := by intro _ _; exact Nat.succ_pos 1

def p0 : oneInfo.Player := ⟨0, by decide⟩

def decisionTree : GameTree oneInfo Bool :=
  .decision (p := p0) PUnit.unit (fun a =>
    if a.1 = 0 then .terminal false else .terminal true)

def chanceDecisionTree : GameTree oneInfo Bool :=
  .chance 2 (PMF.pure ⟨0, by decide⟩) (by decide) (fun _ =>
    .decision (p := p0) PUnit.unit (fun a =>
      if a.1 = 0 then .terminal false else .terminal true))

example :
    (compileLSM (S := oneInfo) (Outcome := Bool) decisionTree).init = decisionTree := rfl

example :
    (compileInfoOn (S := oneInfo) (Outcome := Bool) decisionTree).Obs p0 =
      Option (oneInfo.Infoset p0) := rfl

example :
    obsOfState (S := oneInfo) (Outcome := Bool) p0 decisionTree = some PUnit.unit := by
  simp [obsOfState, decisionTree, p0]

example :
    obsOfState (S := oneInfo) (Outcome := Bool) p0 chanceDecisionTree = none := by
  simp [obsOfState, chanceDecisionTree, p0]

example :
    _root_.EFG.ReachBy ([] : List (_root_.EFG.HistoryStep oneInfo)) decisionTree decisionTree := by
  exact ReachBy.here decisionTree

example :
    Semantics.Transition.ReachBy
      ((compileLSM (S := oneInfo) (Outcome := Bool) decisionTree).stepExists)
      ([] : List (GameTheory.JointAction (compileLSM (S := oneInfo) (Outcome := Bool) decisionTree)))
      decisionTree decisionTree := by
  exact reachBy_implies_compiled (t := decisionTree) (ReachBy.here decisionTree)

example :
    (compileInfoOn (S := oneInfo) (Outcome := Bool) chanceDecisionTree).projectStates p0
      [chanceDecisionTree] = ([PUnit.unit], [none]) := by
  rfl

example :
    (compileInfoOn (S := oneInfo) (Outcome := Bool) chanceDecisionTree).observe p0
      (.decision (p := p0) PUnit.unit (fun a =>
        if a.1 = 0 then .terminal false else .terminal true)) = some PUnit.unit := by
  simp [compileInfoOn, obsOfState, oneInfo, p0]

end

end Tests
end EFG
end Languages
end GameTheory
