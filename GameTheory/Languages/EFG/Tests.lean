import GameTheory.Languages.EFG.Compile

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
      ([] : List (_root_.EFG.HistoryStep oneInfo)) decisionTree decisionTree := by
  exact
    (reachBy_iff_compiled
      (S := oneInfo) (Outcome := Bool) decisionTree [] decisionTree decisionTree).1
      (ReachBy.here decisionTree)

example :
    (compileInfoOn (S := oneInfo) (Outcome := Bool) chanceDecisionTree).project p0
      [HistoryStep.chance 2 ⟨0, by decide⟩] = [] := by
  simp [compileInfoOn, _root_.EFG.playerHistory, oneInfo, p0]

example :
    let a : oneInfo.Act PUnit.unit := ⟨1, by decide⟩
    (compileInfoOn (S := oneInfo) (Outcome := Bool) chanceDecisionTree).project p0
      [HistoryStep.chance 2 ⟨0, by decide⟩, HistoryStep.action p0 PUnit.unit a] =
      [Sum.inr (some ⟨PUnit.unit, a⟩)] := by
  simp [compileInfoOn, _root_.EFG.playerHistory, oneInfo, p0]

end

end Tests
end EFG
end Languages
end GameTheory
