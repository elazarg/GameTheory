/-
# EXP-040 hostile typed-MAID fixtures

The first fixture has heterogeneous node alphabets on a diamond. The second is
EXP-038's one-player, two-decision antichain: each decision observes only its
own chance parent, while both sites resolve in the same native frontier.
-/

import GameTheory.Languages.MAID.Basic
import Mathlib.Data.Fintype.OfMap

noncomputable section

namespace GameTheory.Experimental.TypedMAIDTest

open GameTheory.Math.Probability
open GameTheory.Languages.MAID

/-! ## A heterogeneous diamond -/

namespace Heterogeneous

inductive Node
  | root
  | left
  | right
  | sink
  deriving DecidableEq

instance : Fintype Node :=
  Fintype.ofList [.root, .left, .right, .sink] (by
    intro node
    cases node <;> simp)

def parents : Node → Finset Node
  | .root => ∅
  | .left | .right => {.root}
  | .sink => {.left, .right}

def rank : Node → Nat
  | .root => 0
  | .left | .right => 1
  | .sink => 2

theorem acyclic :
    GameTheory.Math.DAG.Acyclic
      (fun first second => first ∈ parents second) := by
  have rank_lt_of_predecessor : ∀ {first second : Node},
      first ∈ parents second → rank first < rank second := by
    intro first second hedge
    cases first <;> cases second <;>
      simp_all [parents, rank]
  have rank_lt_of_path : ∀ {first second : Node},
      Relation.TransGen
        (fun source target => source ∈ parents target)
        first second →
      rank first < rank second := by
    intro first second path
    induction path with
    | single hedge => exact rank_lt_of_predecessor hedge
    | tail _ hedge ih =>
        exact ih.trans (rank_lt_of_predecessor hedge)
  intro node hcycle
  exact Nat.lt_irrefl _ (rank_lt_of_path hcycle)

@[reducible]
def Value : Node → Type
  | .root => Bool
  | .left => Fin 2
  | .right => Unit
  | .sink => Bool

@[reducible]
def diagram : Structure Unit Node where
  kind _ := .chance
  parents := parents
  observedParents := parents
  Value := Value
  observed_sub _ := fun _ => id
  observed_eq_of_chance _ _ := rfl
  acyclic := acyclic

def defaultValue : (node : Node) → Value node
  | .root => false
  | .left => 0
  | .right => ()
  | .sink => false

def semantics : Semantics diagram where
  defaultValue := defaultValue
  chanceLaw node _ _ := FinDist.pure (defaultValue node)
  utility _ _ := 0

theorem initial_frontier :
    (FrontierState.initial semantics).frontier = {.root} := by
  ext node
  rw [FrontierState.mem_frontier_iff]
  cases node <;>
    simp [FrontierState.initial, diagram, parents]

end Heterogeneous

/-! ## Same owner, disjoint local observations -/

namespace SameOwner

inductive Node
  | leftChance
  | rightChance
  | leftDecision
  | rightDecision
  deriving DecidableEq

instance : Fintype Node :=
  Fintype.ofList
    [.leftChance, .rightChance, .leftDecision, .rightDecision] (by
      intro node
      cases node <;> simp)

def parents : Node → Finset Node
  | .leftChance | .rightChance => ∅
  | .leftDecision => {.leftChance}
  | .rightDecision => {.rightChance}

def kind : Node → NodeKind Unit
  | .leftChance | .rightChance => .chance
  | .leftDecision | .rightDecision => .decision ()

def rank : Node → Nat
  | .leftChance | .rightChance => 0
  | .leftDecision | .rightDecision => 1

theorem acyclic :
    GameTheory.Math.DAG.Acyclic
      (fun first second => first ∈ parents second) := by
  have rank_lt_of_predecessor : ∀ {first second : Node},
      first ∈ parents second → rank first < rank second := by
    intro first second hedge
    cases first <;> cases second <;>
      simp_all [parents, rank]
  have rank_lt_of_path : ∀ {first second : Node},
      Relation.TransGen
        (fun source target => source ∈ parents target)
        first second →
      rank first < rank second := by
    intro first second path
    induction path with
    | single hedge => exact rank_lt_of_predecessor hedge
    | tail _ hedge ih =>
        exact ih.trans (rank_lt_of_predecessor hedge)
  intro node hcycle
  exact Nat.lt_irrefl _ (rank_lt_of_path hcycle)

@[reducible]
def diagram : Structure Unit Node where
  kind := kind
  parents := parents
  observedParents := parents
  Value _ := Bool
  observed_sub _ := fun _ => id
  observed_eq_of_chance node hkind := by
    cases node <;> simp_all [kind]
  acyclic := acyclic

def decisionParent (site : DecisionSite diagram ()) :
    {node // node ∈ diagram.observedParents site.1} := by
  rcases site with ⟨node, hkind⟩
  cases node with
  | leftChance => simp [kind] at hkind
  | rightChance => simp [kind] at hkind
  | leftDecision =>
      exact ⟨.leftChance, by simp [parents]⟩
  | rightDecision =>
      exact ⟨.rightChance, by simp [parents]⟩

/-- Each rule reads exactly its own singleton observation configuration. -/
def responsive : Policy diagram :=
  fun _ site observation =>
    FinDist.pure (observation (decisionParent site))

def constant (value : Bool) : Policy diagram :=
  fun _ _ _ => FinDist.pure value

def chanceValue : Node → Bool
  | .leftChance => false
  | .rightChance => true
  | .leftDecision | .rightDecision => false

@[reducible]
def semantics : Semantics diagram where
  defaultValue _ := false
  chanceLaw node hkind _ := by
    cases node with
    | leftChance => exact FinDist.pure false
    | rightChance => exact FinDist.pure true
    | leftDecision => simp [kind] at hkind
    | rightDecision => simp [kind] at hkind
  utility _ assignment :=
    (if assignment .leftDecision = assignment .leftChance then 1 else 0) +
      (if assignment .rightDecision = assignment .rightChance then 1 else 0)

def initial : FrontierState diagram :=
  FrontierState.initial semantics

theorem initial_frontier :
    initial.frontier = {.leftChance, .rightChance} := by
  ext node
  rw [FrontierState.mem_frontier_iff]
  cases node <;>
    simp [initial, FrontierState.initial, diagram, parents]

def chanceDraw :
    (node : {node // node ∈ initial.frontier}) →
      diagram.Value node.1 :=
  fun node => chanceValue node.1

def afterChance : FrontierState diagram :=
  initial.extend chanceDraw

theorem chance_nodes_commit_together :
    afterChance.resolved = {.leftChance, .rightChance} := by
  simp only [afterChance, FrontierState.extend]
  rw [initial_frontier]
  simp [initial, FrontierState.initial]

theorem afterChance_frontier :
    afterChance.frontier = {.leftDecision, .rightDecision} := by
  ext node
  rw [FrontierState.mem_frontier_iff,
    chance_nodes_commit_together]
  cases node <;> simp [parents]

theorem afterChance_left_value :
    afterChance.values .leftChance = false := by
  exact FrontierState.extend_value_of_frontier initial chanceDraw
    ⟨.leftChance, by simp [initial_frontier]⟩

theorem afterChance_right_value :
    afterChance.values .rightChance = true := by
  exact FrontierState.extend_value_of_frontier initial chanceDraw
    ⟨.rightChance, by simp [initial_frontier]⟩

theorem initial_nodeLaw (policy : Policy diagram)
    (node : {node // node ∈ initial.frontier}) :
    nodeLaw diagram semantics policy initial node =
      FinDist.pure (chanceDraw node) := by
  rcases node with ⟨node, hnode⟩
  cases node with
  | leftChance => rfl
  | rightChance => rfl
  | leftDecision =>
      rw [initial_frontier] at hnode
      simp at hnode
  | rightDecision =>
      rw [initial_frontier] at hnode
      simp at hnode

theorem initial_frontierLaw (policy : Policy diagram) :
    frontierLaw diagram semantics policy initial =
      FinDist.pure chanceDraw := by
  rw [frontierLaw, show
    (fun node => nodeLaw diagram semantics policy initial node) =
      fun node => FinDist.pure (chanceDraw node) by
        funext node
        exact initial_nodeLaw policy node]
  exact FinDist.pi_pure chanceDraw

theorem step_initial (policy : Policy diagram) :
    step diagram semantics policy initial =
      FinDist.pure afterChance := by
  rw [step, initial_frontierLaw policy, FinDist.map_pure]
  rfl

def responsiveDraw :
    (node : {node // node ∈ afterChance.frontier}) →
      diagram.Value node.1
  | ⟨.leftDecision, _⟩ => afterChance.values .leftChance
  | ⟨.rightDecision, _⟩ => afterChance.values .rightChance
  | ⟨.leftChance, hmem⟩ =>
      False.elim (by
        have := hmem
        rw [afterChance_frontier] at this
        simp at this)
  | ⟨.rightChance, hmem⟩ =>
      False.elim (by
        have := hmem
        rw [afterChance_frontier] at this
        simp at this)

def completeResponsive : FrontierState diagram :=
  afterChance.extend responsiveDraw

theorem afterChance_nodeLaw
    (node : {node // node ∈ afterChance.frontier}) :
    nodeLaw diagram semantics responsive afterChance node =
      FinDist.pure (responsiveDraw node) := by
  rcases node with ⟨node, hnode⟩
  cases node with
  | leftChance =>
      rw [afterChance_frontier] at hnode
      simp at hnode
  | rightChance =>
      rw [afterChance_frontier] at hnode
      simp at hnode
  | leftDecision => rfl
  | rightDecision => rfl

theorem afterChance_frontierLaw :
    frontierLaw diagram semantics responsive afterChance =
      FinDist.pure responsiveDraw := by
  rw [frontierLaw, show
    (fun node => nodeLaw diagram semantics responsive afterChance node) =
      fun node => FinDist.pure (responsiveDraw node) by
        funext node
        exact afterChance_nodeLaw node]
  exact FinDist.pi_pure responsiveDraw

theorem step_afterChance :
    step diagram semantics responsive afterChance =
      FinDist.pure completeResponsive := by
  rw [step, afterChance_frontierLaw, FinDist.map_pure]
  rfl

theorem initial_not_complete :
    ¬ initial.IsComplete := by
  rw [FrontierState.IsComplete]
  show (∅ : Finset Node) ≠ Finset.univ
  decide

theorem afterChance_not_complete :
    ¬ afterChance.IsComplete := by
  rw [FrontierState.IsComplete, chance_nodes_commit_together]
  decide

theorem run_two_responsive :
    run diagram semantics responsive 2 initial =
      FinDist.pure completeResponsive := by
  rw [run, if_neg initial_not_complete, step_initial responsive,
    FinDist.pure_bind, run, if_neg afterChance_not_complete,
    step_afterChance, FinDist.pure_bind, run]

theorem decisions_commit_together :
    completeResponsive.resolved = Finset.univ := by
  simp only [completeResponsive, FrontierState.extend]
  rw [chance_nodes_commit_together, afterChance_frontier]
  decide

theorem completeResponsive_left_value :
    completeResponsive.values .leftDecision = false := by
  calc
    completeResponsive.values .leftDecision =
        responsiveDraw
          ⟨.leftDecision, by simp [afterChance_frontier]⟩ :=
      FrontierState.extend_value_of_frontier afterChance responsiveDraw
        ⟨.leftDecision, by simp [afterChance_frontier]⟩
    _ = afterChance.values .leftChance := rfl
    _ = false := afterChance_left_value

theorem completeResponsive_right_value :
    completeResponsive.values .rightDecision = true := by
  calc
    completeResponsive.values .rightDecision =
        responsiveDraw
          ⟨.rightDecision, by simp [afterChance_frontier]⟩ :=
      FrontierState.extend_value_of_frontier afterChance responsiveDraw
        ⟨.rightDecision, by simp [afterChance_frontier]⟩
    _ = afterChance.values .rightChance := rfl
    _ = true := afterChance_right_value

theorem completeResponsive_utility :
    semantics.utility () completeResponsive.values = 2 := by
  rw [show semantics.utility () completeResponsive.values =
      (if completeResponsive.values .leftDecision =
          completeResponsive.values .leftChance then 1 else 0) +
        (if completeResponsive.values .rightDecision =
          completeResponsive.values .rightChance then 1 else 0) from rfl,
    completeResponsive_left_value, completeResponsive_right_value]
  have hleftChance :
      completeResponsive.values .leftChance = false := by
    simp [completeResponsive, FrontierState.extend,
      Assignment.resolve_of_notMem, afterChance_frontier,
      afterChance_left_value]
  have hrightChance :
      completeResponsive.values .rightChance = true := by
    simp [completeResponsive, FrontierState.extend,
      Assignment.resolve_of_notMem, afterChance_frontier,
      afterChance_right_value]
  simp [hleftChance, hrightChance]
  norm_num

def constantFalseDraw :
    (node : {node // node ∈ afterChance.frontier}) →
      diagram.Value node.1 :=
  fun _ => false

def completeConstantFalse : FrontierState diagram :=
  afterChance.extend constantFalseDraw

theorem afterChance_nodeLaw_constantFalse
    (node : {node // node ∈ afterChance.frontier}) :
    nodeLaw diagram semantics (constant false) afterChance node =
      FinDist.pure (constantFalseDraw node) := by
  rcases node with ⟨node, hnode⟩
  cases node with
  | leftChance =>
      rw [afterChance_frontier] at hnode
      simp at hnode
  | rightChance =>
      rw [afterChance_frontier] at hnode
      simp at hnode
  | leftDecision => rfl
  | rightDecision => rfl

theorem step_afterChance_constantFalse :
    step diagram semantics (constant false) afterChance =
      FinDist.pure completeConstantFalse := by
  rw [step, frontierLaw, show
    (fun node =>
      nodeLaw diagram semantics (constant false) afterChance node) =
        fun node => FinDist.pure (constantFalseDraw node) by
          funext node
          exact afterChance_nodeLaw_constantFalse node,
    FinDist.pi_pure, FinDist.map_pure]
  rfl

theorem run_two_constantFalse :
    run diagram semantics (constant false) 2 initial =
      FinDist.pure completeConstantFalse := by
  rw [run, if_neg initial_not_complete, step_initial (constant false),
    FinDist.pure_bind, run, if_neg afterChance_not_complete,
    step_afterChance_constantFalse, FinDist.pure_bind, run]

theorem completeConstantFalse_left_value :
    completeConstantFalse.values .leftDecision = false := by
  exact FrontierState.extend_value_of_frontier
    afterChance constantFalseDraw
      ⟨.leftDecision, by simp [afterChance_frontier]⟩

theorem completeConstantFalse_right_value :
    completeConstantFalse.values .rightDecision = false := by
  exact FrontierState.extend_value_of_frontier
    afterChance constantFalseDraw
      ⟨.rightDecision, by simp [afterChance_frontier]⟩

theorem completeConstantFalse_utility :
    semantics.utility () completeConstantFalse.values = 1 := by
  rw [show semantics.utility () completeConstantFalse.values =
      (if completeConstantFalse.values .leftDecision =
          completeConstantFalse.values .leftChance then 1 else 0) +
        (if completeConstantFalse.values .rightDecision =
          completeConstantFalse.values .rightChance then 1 else 0) from rfl,
    completeConstantFalse_left_value,
    completeConstantFalse_right_value]
  have hleftChance :
      completeConstantFalse.values .leftChance = false := by
    simp [completeConstantFalse, FrontierState.extend,
      Assignment.resolve_of_notMem, afterChance_frontier,
      afterChance_left_value]
  have hrightChance :
      completeConstantFalse.values .rightChance = true := by
    simp [completeConstantFalse, FrontierState.extend,
      Assignment.resolve_of_notMem, afterChance_frontier,
      afterChance_right_value]
  simp [hleftChance, hrightChance]

theorem outcome_law_depends_on_policy :
    run diagram semantics responsive 2 initial ≠
      run diagram semantics (constant false) 2 initial := by
  intro hequal
  have hutility := congrArg
    (fun law => law.expect fun state =>
      semantics.utility () state.values) hequal
  rw [run_two_responsive, run_two_constantFalse,
    FinDist.expect_pure, FinDist.expect_pure,
    completeResponsive_utility,
    completeConstantFalse_utility] at hutility
  norm_num at hutility

def constantTrueDraw :
    (node : {node // node ∈ afterChance.frontier}) →
      diagram.Value node.1 :=
  fun _ => true

def completeConstantTrue : FrontierState diagram :=
  afterChance.extend constantTrueDraw

theorem afterChance_nodeLaw_constantTrue
    (node : {node // node ∈ afterChance.frontier}) :
    nodeLaw diagram semantics (constant true) afterChance node =
      FinDist.pure (constantTrueDraw node) := by
  rcases node with ⟨node, hnode⟩
  cases node with
  | leftChance =>
      rw [afterChance_frontier] at hnode
      simp at hnode
  | rightChance =>
      rw [afterChance_frontier] at hnode
      simp at hnode
  | leftDecision => rfl
  | rightDecision => rfl

theorem step_afterChance_constantTrue :
    step diagram semantics (constant true) afterChance =
      FinDist.pure completeConstantTrue := by
  rw [step, frontierLaw, show
    (fun node =>
      nodeLaw diagram semantics (constant true) afterChance node) =
        fun node => FinDist.pure (constantTrueDraw node) by
          funext node
          exact afterChance_nodeLaw_constantTrue node,
    FinDist.pi_pure, FinDist.map_pure]
  rfl

theorem run_two_constantTrue :
    run diagram semantics (constant true) 2 initial =
      FinDist.pure completeConstantTrue := by
  rw [run, if_neg initial_not_complete, step_initial (constant true),
    FinDist.pure_bind, run, if_neg afterChance_not_complete,
    step_afterChance_constantTrue, FinDist.pure_bind, run]

theorem completeConstantTrue_left_value :
    completeConstantTrue.values .leftDecision = true := by
  exact FrontierState.extend_value_of_frontier
    afterChance constantTrueDraw
      ⟨.leftDecision, by simp [afterChance_frontier]⟩

theorem completeConstantTrue_right_value :
    completeConstantTrue.values .rightDecision = true := by
  exact FrontierState.extend_value_of_frontier
    afterChance constantTrueDraw
      ⟨.rightDecision, by simp [afterChance_frontier]⟩

theorem completeConstantTrue_utility :
    semantics.utility () completeConstantTrue.values = 1 := by
  rw [show semantics.utility () completeConstantTrue.values =
      (if completeConstantTrue.values .leftDecision =
          completeConstantTrue.values .leftChance then 1 else 0) +
        (if completeConstantTrue.values .rightDecision =
          completeConstantTrue.values .rightChance then 1 else 0) from rfl,
    completeConstantTrue_left_value,
    completeConstantTrue_right_value]
  have hleftChance :
      completeConstantTrue.values .leftChance = false := by
    simp [completeConstantTrue, FrontierState.extend,
      Assignment.resolve_of_notMem, afterChance_frontier,
      afterChance_left_value]
  have hrightChance :
      completeConstantTrue.values .rightChance = true := by
    simp [completeConstantTrue, FrontierState.extend,
      Assignment.resolve_of_notMem, afterChance_frontier,
      afterChance_right_value]
  simp [hleftChance, hrightChance]

theorem outcome_law_depends_on_left_policy :
    run diagram semantics responsive 2 initial ≠
      run diagram semantics (constant true) 2 initial := by
  intro hequal
  have hutility := congrArg
    (fun law => law.expect fun state =>
      semantics.utility () state.values) hequal
  rw [run_two_responsive, run_two_constantTrue,
    FinDist.expect_pure, FinDist.expect_pure,
    completeResponsive_utility,
    completeConstantTrue_utility] at hutility
  norm_num at hutility

end SameOwner

end GameTheory.Experimental.TypedMAIDTest
