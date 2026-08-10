/-
# EXP-041 hostile probe

One source owner controls incomparable decision sites with disjoint observed
parents. Both serializations are real EFGs. Changing the earlier incomparable
decision must leave the later site's information state unchanged.
-/

import GameTheory.Experimental.PostArchitecture.TypedMAIDTest
import GameTheory.Languages.MAID.Order

noncomputable section

namespace GameTheory.Experimental.TypedMAID.ToEFGTest

open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.ToEFG
open GameTheory.Probability

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
      GameTheory.Languages.MAID.Assignment.resolve]
  have htrueValue :
      beforeRightDecisionTrue.assignment leftFirst semantics
          Node.rightChance = true := by
    rw [Stage.assignment, beforeRightDecisionTrue_path]
    simp [Stage.Assignment.setOne,
      GameTheory.Languages.MAID.Assignment.resolve]
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
      GameTheory.Languages.MAID.Assignment.resolve]
  have htrueValue :
      beforeLeftDecisionTrue.assignment rightFirst semantics
          Node.leftChance = false := by
    rw [Stage.assignment, beforeLeftDecisionTrue_path]
    simp [Stage.Assignment.setOne,
      GameTheory.Languages.MAID.Assignment.resolve]
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

def leftCompleteResponsive : Stage diagram leftFirst :=
  beforeRightDecisionFalse.advance leftFirst (by decide) true

def rightCompleteResponsive : Stage diagram rightFirst :=
  beforeLeftDecisionTrue.advance rightFirst (by decide) false

theorem leftCompleteResponsive_path :
    leftCompleteResponsive.path =
      [⟨Node.leftChance, false⟩, ⟨Node.leftDecision, false⟩,
        ⟨Node.rightChance, true⟩, ⟨Node.rightDecision, true⟩] := by
  rfl

theorem rightCompleteResponsive_path :
    rightCompleteResponsive.path =
      [⟨Node.rightChance, true⟩, ⟨Node.rightDecision, true⟩,
        ⟨Node.leftChance, false⟩, ⟨Node.leftDecision, false⟩] := by
  rfl

theorem complete_assignments_order_independent :
    leftCompleteResponsive.assignment leftFirst semantics =
      rightCompleteResponsive.assignment rightFirst semantics := by
  funext node
  cases node <;>
    rw [Stage.assignment, Stage.assignment,
      leftCompleteResponsive_path, rightCompleteResponsive_path] <;>
    simp [Stage.Assignment.setOne,
      GameTheory.Languages.MAID.Assignment.resolve]

theorem native_complete_left_chance :
    completeResponsive.values Node.leftChance = false := by
  simp [completeResponsive, FrontierState.extend,
    Assignment.resolve_of_notMem, afterChance_frontier,
    afterChance_left_value]

theorem native_complete_right_chance :
    completeResponsive.values Node.rightChance = true := by
  simp [completeResponsive, FrontierState.extend,
    Assignment.resolve_of_notMem, afterChance_frontier,
    afterChance_right_value]

theorem left_complete_assignment_eq_native :
    leftCompleteResponsive.assignment leftFirst semantics =
      completeResponsive.values := by
  funext node
  cases node
  · rw [native_complete_left_chance, Stage.assignment,
      leftCompleteResponsive_path]
    simp [Stage.Assignment.setOne,
      GameTheory.Languages.MAID.Assignment.resolve]
  · rw [native_complete_right_chance, Stage.assignment,
      leftCompleteResponsive_path]
    simp [Stage.Assignment.setOne,
      GameTheory.Languages.MAID.Assignment.resolve]
  · rw [completeResponsive_left_value, Stage.assignment,
      leftCompleteResponsive_path]
    simp [Stage.Assignment.setOne,
      GameTheory.Languages.MAID.Assignment.resolve]
  · rw [completeResponsive_right_value, Stage.assignment,
      leftCompleteResponsive_path]
    simp [Stage.Assignment.setOne,
      GameTheory.Languages.MAID.Assignment.resolve]

theorem right_complete_assignment_eq_native :
    rightCompleteResponsive.assignment rightFirst semantics =
      completeResponsive.values :=
  complete_assignments_order_independent.symm.trans
    left_complete_assignment_eq_native

theorem serialStep_leftInitial :
    serialStep leftFirst semantics responsive leftInitial (by decide) =
      FinDist.pure afterLeftChance := by
  let hpending :
      leftInitial.path.length < leftFirst.order.length := by
    decide
  have hnode :
      leftInitial.pendingNode leftFirst hpending =
        Node.leftChance :=
    pendingNode_eq_of_pending_eq leftFirst hpending (by rfl)
  have hkind :
      diagram.kind (leftInitial.pendingNode leftFirst hpending) =
        NodeKind.chance := by
    rw [hnode]
    rfl
  have hlaw :
      semantics.chanceLaw
          (leftInitial.pendingNode leftFirst hpending) hkind
          (leftInitial.configOf leftFirst semantics
            (diagram.parents
              (leftInitial.pendingNode leftFirst hpending))) =
        FinDist.pure false := by
    generalize hnodeEq :
      leftInitial.pendingNode leftFirst hpending = node at hkind ⊢
    have heq : node = Node.leftChance :=
      hnodeEq.symm.trans hnode
    subst node
    rfl
  unfold serialStep
  rw [serialNodeLaw_of_chance leftFirst semantics responsive
    leftInitial hpending hkind, hlaw, FinDist.map_pure]
  rfl

theorem serialStep_afterLeftChance :
    serialStep leftFirst semantics responsive afterLeftChance (by decide) =
      FinDist.pure afterLeftFalse := by
  unfold serialStep
  rw [serialNodeLaw_of_decision leftFirst semantics responsive
    afterLeftChance (by decide) (by rfl)]
  simp [responsive, decisionParent, Stage.configOf,
    GameTheory.Languages.MAID.Assignment.restrict, afterLeftChance,
    leftInitial, Stage.initial, Stage.assignment,
    Stage.Assignment.setOne, GameTheory.Languages.MAID.Assignment.resolve,
    leftFirst, afterLeftFalse]

theorem serialStep_afterLeftFalse :
    serialStep leftFirst semantics responsive afterLeftFalse (by decide) =
      FinDist.pure beforeRightDecisionFalse := by
  let hpending :
      afterLeftFalse.path.length < leftFirst.order.length := by
    decide
  have hnode :
      afterLeftFalse.pendingNode leftFirst hpending =
        Node.rightChance :=
    pendingNode_eq_of_pending_eq leftFirst hpending (by rfl)
  have hkind :
      diagram.kind (afterLeftFalse.pendingNode leftFirst hpending) =
        NodeKind.chance := by
    rw [hnode]
    rfl
  have hlaw :
      semantics.chanceLaw
          (afterLeftFalse.pendingNode leftFirst hpending) hkind
          (afterLeftFalse.configOf leftFirst semantics
            (diagram.parents
              (afterLeftFalse.pendingNode leftFirst hpending))) =
        FinDist.pure true := by
    generalize hnodeEq :
      afterLeftFalse.pendingNode leftFirst hpending = node at hkind ⊢
    have heq : node = Node.rightChance :=
      hnodeEq.symm.trans hnode
    subst node
    rfl
  unfold serialStep
  rw [serialNodeLaw_of_chance leftFirst semantics responsive
    afterLeftFalse hpending hkind, hlaw, FinDist.map_pure]
  rfl

theorem serialStep_beforeRightDecision :
    serialStep leftFirst semantics responsive
        beforeRightDecisionFalse (by decide) =
      FinDist.pure leftCompleteResponsive := by
  unfold serialStep
  rw [serialNodeLaw_of_decision leftFirst semantics responsive
    beforeRightDecisionFalse (by decide) (by rfl)]
  simp [responsive, decisionParent, Stage.configOf,
    GameTheory.Languages.MAID.Assignment.restrict, Stage.assignment,
    beforeRightDecisionFalse_path, Stage.Assignment.setOne,
    GameTheory.Languages.MAID.Assignment.resolve, leftCompleteResponsive]

theorem serialStep_rightInitial :
    serialStep rightFirst semantics responsive rightInitial (by decide) =
      FinDist.pure afterRightChance := by
  let hpending :
      rightInitial.path.length < rightFirst.order.length := by
    decide
  have hnode :
      rightInitial.pendingNode rightFirst hpending =
        Node.rightChance :=
    pendingNode_eq_of_pending_eq rightFirst hpending (by rfl)
  have hkind :
      diagram.kind (rightInitial.pendingNode rightFirst hpending) =
        NodeKind.chance := by
    rw [hnode]
    rfl
  have hlaw :
      semantics.chanceLaw
          (rightInitial.pendingNode rightFirst hpending) hkind
          (rightInitial.configOf rightFirst semantics
            (diagram.parents
              (rightInitial.pendingNode rightFirst hpending))) =
        FinDist.pure true := by
    generalize hnodeEq :
      rightInitial.pendingNode rightFirst hpending = node at hkind ⊢
    have heq : node = Node.rightChance :=
      hnodeEq.symm.trans hnode
    subst node
    rfl
  unfold serialStep
  rw [serialNodeLaw_of_chance rightFirst semantics responsive
    rightInitial hpending hkind, hlaw, FinDist.map_pure]
  rfl

theorem serialStep_afterRightChance :
    serialStep rightFirst semantics responsive afterRightChance (by decide) =
      FinDist.pure afterRightTrue := by
  unfold serialStep
  rw [serialNodeLaw_of_decision rightFirst semantics responsive
    afterRightChance (by decide) (by rfl)]
  simp [responsive, decisionParent, Stage.configOf,
    GameTheory.Languages.MAID.Assignment.restrict, afterRightChance,
    rightInitial, Stage.initial, Stage.assignment,
    Stage.Assignment.setOne, GameTheory.Languages.MAID.Assignment.resolve,
    rightFirst, afterRightTrue]

theorem serialStep_afterRightTrue :
    serialStep rightFirst semantics responsive afterRightTrue (by decide) =
      FinDist.pure beforeLeftDecisionTrue := by
  let hpending :
      afterRightTrue.path.length < rightFirst.order.length := by
    decide
  have hnode :
      afterRightTrue.pendingNode rightFirst hpending =
        Node.leftChance :=
    pendingNode_eq_of_pending_eq rightFirst hpending (by rfl)
  have hkind :
      diagram.kind (afterRightTrue.pendingNode rightFirst hpending) =
        NodeKind.chance := by
    rw [hnode]
    rfl
  have hlaw :
      semantics.chanceLaw
          (afterRightTrue.pendingNode rightFirst hpending) hkind
          (afterRightTrue.configOf rightFirst semantics
            (diagram.parents
              (afterRightTrue.pendingNode rightFirst hpending))) =
        FinDist.pure false := by
    generalize hnodeEq :
      afterRightTrue.pendingNode rightFirst hpending = node at hkind ⊢
    have heq : node = Node.leftChance :=
      hnodeEq.symm.trans hnode
    subst node
    rfl
  unfold serialStep
  rw [serialNodeLaw_of_chance rightFirst semantics responsive
    afterRightTrue hpending hkind, hlaw, FinDist.map_pure]
  rfl

theorem serialStep_beforeLeftDecision :
    serialStep rightFirst semantics responsive
        beforeLeftDecisionTrue (by decide) =
      FinDist.pure rightCompleteResponsive := by
  unfold serialStep
  rw [serialNodeLaw_of_decision rightFirst semantics responsive
    beforeLeftDecisionTrue (by decide) (by rfl)]
  simp [responsive, decisionParent, Stage.configOf,
    GameTheory.Languages.MAID.Assignment.restrict, Stage.assignment,
    beforeLeftDecisionTrue_path, Stage.Assignment.setOne,
    GameTheory.Languages.MAID.Assignment.resolve, rightCompleteResponsive]

theorem serialRun_leftFirst :
    serialRun leftFirst semantics responsive 4 leftInitial =
      FinDist.pure leftCompleteResponsive := by
  rw [serialRun, dif_neg (by decide), serialStep_leftInitial,
    FinDist.pure_bind, serialRun, dif_neg (by decide),
    serialStep_afterLeftChance, FinDist.pure_bind, serialRun,
    dif_neg (by decide), serialStep_afterLeftFalse,
    FinDist.pure_bind, serialRun, dif_neg (by decide),
    serialStep_beforeRightDecision, FinDist.pure_bind, serialRun]

theorem serialRun_rightFirst :
    serialRun rightFirst semantics responsive 4 rightInitial =
      FinDist.pure rightCompleteResponsive := by
  rw [serialRun, dif_neg (by decide), serialStep_rightInitial,
    FinDist.pure_bind, serialRun, dif_neg (by decide),
    serialStep_afterRightChance, FinDist.pure_bind, serialRun,
    dif_neg (by decide), serialStep_afterRightTrue,
    FinDist.pure_bind, serialRun, dif_neg (by decide),
    serialStep_beforeLeftDecision, FinDist.pure_bind, serialRun]

theorem serial_assignment_law_order_independent :
    FinDist.map (Stage.assignment leftFirst semantics)
        (serialRun leftFirst semantics responsive 4 leftInitial) =
      FinDist.map (Stage.assignment rightFirst semantics)
        (serialRun rightFirst semantics responsive 4 rightInitial) := by
  simpa [leftInitial, rightInitial, leftFirst, rightFirst] using
    serialRun_topological_order_independent semantics responsive
      leftFirst rightFirst

theorem left_serial_assignment_law_eq_native :
    FinDist.map (Stage.assignment leftFirst semantics)
        (serialRun leftFirst semantics responsive 4 leftInitial) =
      FinDist.map (fun state => state.values)
        (GameTheory.Languages.MAID.run diagram semantics responsive 2 initial) := by
  rw [serialRun_leftFirst, run_two_responsive,
    FinDist.map_pure, FinDist.map_pure,
    left_complete_assignment_eq_native]

theorem right_serial_assignment_law_eq_native :
    FinDist.map (Stage.assignment rightFirst semantics)
        (serialRun rightFirst semantics responsive 4 rightInitial) =
      FinDist.map (fun state => state.values)
        (GameTheory.Languages.MAID.run diagram semantics responsive 2 initial) := by
  rw [serialRun_rightFirst, run_two_responsive,
    FinDist.map_pure, FinDist.map_pure,
    right_complete_assignment_eq_native]

/-- The actual compiled EFG behavioral runner agrees with the native frontier
runner after histories are forgotten and the completed assignment is read. -/
theorem left_behavioral_assignment_law_eq_native :
    FinDist.map
        (fun history =>
          Stage.assignment leftFirst semantics history.state)
        ((information leftFirst semantics).runBehavioral
          leftBehavioral 4) =
      FinDist.map (fun state => state.values)
        (GameTheory.Languages.MAID.run diagram semantics responsive 2 initial) := by
  have hrun :=
    map_state_runBehavioralFrom_eq_serialRun leftFirst
      semantics responsive 4 (execution leftFirst semantics).initHistory
  have hmapped :=
    congrArg (FinDist.map (Stage.assignment leftFirst semantics))
      hrun
  rw [FinDist.map_comp] at hmapped
  calc
    _ = FinDist.map (Stage.assignment leftFirst semantics)
          (serialRun leftFirst semantics responsive 4 leftInitial) := by
        simpa [GameTheory.Protocol.InformationModel.runBehavioral,
          leftBehavioral, leftInitial,
          Function.comp_def] using hmapped
    _ = _ := left_serial_assignment_law_eq_native

theorem right_behavioral_assignment_law_eq_native :
    FinDist.map
        (fun history =>
          Stage.assignment rightFirst semantics history.state)
        ((information rightFirst semantics).runBehavioral
          rightBehavioral 4) =
      FinDist.map (fun state => state.values)
        (GameTheory.Languages.MAID.run diagram semantics responsive 2 initial) := by
  have hrun :=
    map_state_runBehavioralFrom_eq_serialRun rightFirst
      semantics responsive 4 (execution rightFirst semantics).initHistory
  have hmapped :=
    congrArg (FinDist.map (Stage.assignment rightFirst semantics))
      hrun
  rw [FinDist.map_comp] at hmapped
  calc
    _ = FinDist.map (Stage.assignment rightFirst semantics)
          (serialRun rightFirst semantics responsive 4 rightInitial) := by
        simpa [GameTheory.Protocol.InformationModel.runBehavioral,
          rightBehavioral, rightInitial,
          Function.comp_def] using hmapped
    _ = _ := right_serial_assignment_law_eq_native

theorem behavioral_assignment_law_order_independent :
    FinDist.map
        (fun history =>
          Stage.assignment leftFirst semantics history.state)
        ((information leftFirst semantics).runBehavioral
          leftBehavioral 4) =
      FinDist.map
        (fun history =>
          Stage.assignment rightFirst semantics history.state)
        ((information rightFirst semantics).runBehavioral
          rightBehavioral 4) :=
  left_behavioral_assignment_law_eq_native.trans
    right_behavioral_assignment_law_eq_native.symm

end SameOwner

end GameTheory.Experimental.TypedMAID.ToEFGTest
