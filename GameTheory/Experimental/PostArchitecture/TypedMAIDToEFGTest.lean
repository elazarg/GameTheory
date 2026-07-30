/-
# EXP-041 hostile probe

One source owner controls incomparable decision sites with disjoint observed
parents. Both serializations are real EFGs. Changing the earlier incomparable
decision must leave the later site's information state unchanged.
-/

import GameTheory.Experimental.PostArchitecture.TypedMAIDTest
import GameTheory.Experimental.PostArchitecture.TypedMAIDToEFG

noncomputable section

namespace GameTheory.Experimental.TypedMAID.ToEFGTest

open GameTheory.Experimental.TypedMAID
open GameTheory.Experimental.TypedMAID.ToEFG

namespace SameOwner

abbrev Node := TypedMAIDTest.SameOwner.Node

open TypedMAIDTest.SameOwner

def leftFirst :
    GameTheoryMath.DAG.TopologicalOrder diagram.parents where
  order :=
    [.leftChance, .leftDecision, .rightChance, .rightDecision]
  nodup := by decide
  complete := by
    intro node
    cases node <;> simp
  respects := by
    intro index parent hparent
    fin_cases index <;> cases parent <;>
      simp_all [parents]
    all_goals
      exact ⟨⟨2, by decide⟩, by decide, rfl⟩

def rightFirst :
    GameTheoryMath.DAG.TopologicalOrder diagram.parents where
  order :=
    [.rightChance, .rightDecision, .leftChance, .leftDecision]
  nodup := by decide
  complete := by
    intro node
    cases node <;> simp
  respects := by
    intro index parent hparent
    fin_cases index <;> cases parent <;>
      simp_all [parents]
    all_goals
      exact ⟨⟨2, by decide⟩, by decide, rfl⟩

def leftInitial : Stage diagram leftFirst :=
  Stage.initial leftFirst

def afterLeftChance : Stage diagram leftFirst :=
  leftInitial.advance leftFirst (by decide) false

def afterLeftFalse : Stage diagram leftFirst :=
  afterLeftChance.advance leftFirst (by decide) false

def afterLeftTrue : Stage diagram leftFirst :=
  afterLeftChance.advance leftFirst (by decide) true

def beforeRightDecisionFalse : Stage diagram leftFirst :=
  afterLeftFalse.advance leftFirst (by decide) true

def beforeRightDecisionTrue : Stage diagram leftFirst :=
  afterLeftTrue.advance leftFirst (by decide) true

theorem beforeRightDecisionFalse_path :
    beforeRightDecisionFalse.path =
      [⟨Node.leftChance, false⟩, ⟨Node.leftDecision, false⟩,
        ⟨Node.rightChance, true⟩] := by
  rfl

theorem beforeRightDecisionTrue_path :
    beforeRightDecisionTrue.path =
      [⟨Node.leftChance, false⟩, ⟨Node.leftDecision, true⟩,
        ⟨Node.rightChance, true⟩] := by
  rfl

/-- The later right-site policy cannot see the earlier left decision. -/
theorem right_view_hides_left_decision :
    viewOf leftFirst semantics ()
        beforeRightDecisionFalse =
      viewOf leftFirst semantics ()
        beforeRightDecisionTrue := by
  have hfalsePending :
      beforeRightDecisionFalse.pending leftFirst =
        some Node.rightDecision := by
    rfl
  have htruePending :
      beforeRightDecisionTrue.pending leftFirst =
        some Node.rightDecision := by
    rfl
  have hfalseValue :
      beforeRightDecisionFalse.assignment leftFirst semantics
          Node.rightChance = true := by
    rw [Stage.assignment, beforeRightDecisionFalse_path]
    simp [Stage.Assignment.setOne,
      TypedMAID.Assignment.resolve]
  have htrueValue :
      beforeRightDecisionTrue.assignment leftFirst semantics
          Node.rightChance = true := by
    rw [Stage.assignment, beforeRightDecisionTrue_path]
    simp [Stage.Assignment.setOne,
      TypedMAID.Assignment.resolve]
  have hconfig :
      beforeRightDecisionFalse.configOf leftFirst semantics
          (diagram.observedParents Node.rightDecision) =
        beforeRightDecisionTrue.configOf leftFirst semantics
          (diagram.observedParents Node.rightDecision) := by
    funext observed
    rcases observed with ⟨node, hnode⟩
    have hnodeEq : node = Node.rightChance := by
      simpa [diagram, parents] using hnode
    subst node
    exact hfalseValue.trans htrueValue.symm
  calc
    viewOf leftFirst semantics () beforeRightDecisionFalse =
        .acting ⟨Node.rightDecision, rfl⟩
          (beforeRightDecisionFalse.configOf leftFirst semantics
            (diagram.observedParents Node.rightDecision)) :=
      viewOf_eq_acting leftFirst semantics ()
        beforeRightDecisionFalse hfalsePending rfl
    _ = .acting ⟨Node.rightDecision, rfl⟩
          (beforeRightDecisionTrue.configOf leftFirst semantics
            (diagram.observedParents Node.rightDecision)) := by
      rw [hconfig]
    _ = viewOf leftFirst semantics ()
          beforeRightDecisionTrue :=
      (viewOf_eq_acting leftFirst semantics ()
        beforeRightDecisionTrue htruePending rfl).symm

def rightInitial : Stage diagram rightFirst :=
  Stage.initial rightFirst

def afterRightChance : Stage diagram rightFirst :=
  rightInitial.advance rightFirst (by decide) true

def afterRightFalse : Stage diagram rightFirst :=
  afterRightChance.advance rightFirst (by decide) false

def afterRightTrue : Stage diagram rightFirst :=
  afterRightChance.advance rightFirst (by decide) true

def beforeLeftDecisionFalse : Stage diagram rightFirst :=
  afterRightFalse.advance rightFirst (by decide) false

def beforeLeftDecisionTrue : Stage diagram rightFirst :=
  afterRightTrue.advance rightFirst (by decide) false

theorem beforeLeftDecisionFalse_path :
    beforeLeftDecisionFalse.path =
      [⟨Node.rightChance, true⟩, ⟨Node.rightDecision, false⟩,
        ⟨Node.leftChance, false⟩] := by
  rfl

theorem beforeLeftDecisionTrue_path :
    beforeLeftDecisionTrue.path =
      [⟨Node.rightChance, true⟩, ⟨Node.rightDecision, true⟩,
        ⟨Node.leftChance, false⟩] := by
  rfl

/-- The symmetric order hides the earlier right decision from the left site. -/
theorem left_view_hides_right_decision :
    viewOf rightFirst semantics ()
        beforeLeftDecisionFalse =
      viewOf rightFirst semantics ()
        beforeLeftDecisionTrue := by
  have hfalsePending :
      beforeLeftDecisionFalse.pending rightFirst =
        some Node.leftDecision := by
    rfl
  have htruePending :
      beforeLeftDecisionTrue.pending rightFirst =
        some Node.leftDecision := by
    rfl
  have hfalseValue :
      beforeLeftDecisionFalse.assignment rightFirst semantics
          Node.leftChance = false := by
    rw [Stage.assignment, beforeLeftDecisionFalse_path]
    simp [Stage.Assignment.setOne,
      TypedMAID.Assignment.resolve]
  have htrueValue :
      beforeLeftDecisionTrue.assignment rightFirst semantics
          Node.leftChance = false := by
    rw [Stage.assignment, beforeLeftDecisionTrue_path]
    simp [Stage.Assignment.setOne,
      TypedMAID.Assignment.resolve]
  have hconfig :
      beforeLeftDecisionFalse.configOf rightFirst semantics
          (diagram.observedParents Node.leftDecision) =
        beforeLeftDecisionTrue.configOf rightFirst semantics
          (diagram.observedParents Node.leftDecision) := by
    funext observed
    rcases observed with ⟨node, hnode⟩
    have hnodeEq : node = Node.leftChance := by
      simpa [diagram, parents] using hnode
    subst node
    exact hfalseValue.trans htrueValue.symm
  calc
    viewOf rightFirst semantics () beforeLeftDecisionFalse =
        .acting ⟨Node.leftDecision, rfl⟩
          (beforeLeftDecisionFalse.configOf rightFirst semantics
            (diagram.observedParents Node.leftDecision)) :=
      viewOf_eq_acting rightFirst semantics ()
        beforeLeftDecisionFalse hfalsePending rfl
    _ = .acting ⟨Node.leftDecision, rfl⟩
          (beforeLeftDecisionTrue.configOf rightFirst semantics
            (diagram.observedParents Node.leftDecision)) := by
      rw [hconfig]
    _ = viewOf rightFirst semantics ()
          beforeLeftDecisionTrue :=
      (viewOf_eq_acting rightFirst semantics ()
        beforeLeftDecisionTrue htruePending rfl).symm

/-- Both explicit orders produce accepted EFG objects with source owners. -/
def leftGame : GameTheory.Languages.EFG.Game Unit :=
  game leftFirst semantics

def rightGame : GameTheory.Languages.EFG.Game Unit :=
  game rightFirst semantics

def leftBehavioral :=
  behavioralProfile leftFirst semantics responsive

def rightBehavioral :=
  behavioralProfile rightFirst semantics responsive

end SameOwner

end GameTheory.Experimental.TypedMAID.ToEFGTest
