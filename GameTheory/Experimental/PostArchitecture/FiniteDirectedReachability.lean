/-
# EXP-109: executable finite directed reachability

This module validates an explicit-list boundary for deciding directed
reachability.  The node carrier remains arbitrary: callers provide a complete,
duplicate-free enumeration only when they want to run the checker.
-/

import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation

namespace GameTheory.Experimental.PostArchitecture.FiniteDirectedReachability

universe u

/-- A Boolean binary relation, kept separate from its proposition-valued view. -/
abbrev BoolRel (α : Type u) := α → α → Bool

/-- Interpret a Boolean relation as a proposition-valued relation. -/
def Holds {α : Type u} (edge : BoolRel α) (source target : α) : Prop :=
  edge source target = true

/-- Add every route through one pivot to a Boolean relation. -/
def addPivot {α : Type u} (pivot : α) (relation : BoolRel α) : BoolRel α :=
  fun source target =>
    relation source target || (relation source pivot && relation pivot target)

/-- Warshall closure, with the supplied list serving as the pivot enumeration. -/
def warshall {α : Type u} : List α → BoolRel α → BoolRel α
  | [], relation => relation
  | pivot :: rest, relation => addPivot pivot (warshall rest relation)

/-- Add reflexivity before closing a Boolean edge relation under listed pivots. -/
def reachableBool {α : Type u} [DecidableEq α]
    (nodes : List α) (edge : BoolRel α) : BoolRel α :=
  warshall nodes fun source target => decide (source = target) || edge source target

/-- A finite carrier presented explicitly, without installing a `Fintype`. -/
structure Enumeration (α : Type u) [DecidableEq α] where
  nodes : List α
  nodup : nodes.Nodup
  complete : ∀ node, node ∈ nodes

namespace Enumeration

/-- Run the directed reachability checker over an explicit node enumeration. -/
def reachable {α : Type u} [DecidableEq α]
    (enumeration : Enumeration α) (edge : BoolRel α) : BoolRel α :=
  reachableBool enumeration.nodes edge

end Enumeration

/-! ## Semantic proof -/

theorem warshall_of_base {α : Type u} (nodes : List α) (relation : BoolRel α)
    {source target : α} (h : relation source target = true) :
    warshall nodes relation source target = true := by
  induction nodes generalizing source target with
  | nil => exact h
  | cons pivot rest ih =>
      simp only [warshall, addPivot, Bool.or_eq_true, Bool.and_eq_true]
      exact Or.inl (ih h)

theorem warshall_trans_of_mem {α : Type u} (relation : BoolRel α)
    {nodes : List α} {source middle target : α} (hmiddle : middle ∈ nodes)
    (hsource : warshall nodes relation source middle = true)
    (htarget : warshall nodes relation middle target = true) :
    warshall nodes relation source target = true := by
  induction nodes generalizing source middle target with
  | nil => simp at hmiddle
  | cons pivot rest ih =>
      simp only [List.mem_cons] at hmiddle
      simp only [warshall, addPivot, Bool.or_eq_true, Bool.and_eq_true] at hsource htarget ⊢
      rcases hmiddle with rfl | hmiddle
      · have hsource' : warshall rest relation source middle = true :=
          hsource.elim id And.left
        have htarget' : warshall rest relation middle target = true :=
          htarget.elim id And.right
        exact Or.inr ⟨hsource', htarget'⟩
      · rcases hsource with hsource | ⟨hsource, hmiddleSource⟩
        · rcases htarget with htarget | ⟨hmiddleTarget, hpivotTarget⟩
          · exact Or.inl (ih hmiddle hsource htarget)
          · exact Or.inr ⟨ih hmiddle hsource hmiddleTarget, hpivotTarget⟩
        · rcases htarget with htarget | ⟨_, hpivotTarget⟩
          · exact Or.inr ⟨hsource, ih hmiddle hmiddleSource htarget⟩
          · exact Or.inr ⟨hsource, hpivotTarget⟩

theorem warshall_sound {α : Type u} (nodes : List α) (edge : BoolRel α)
    {source target : α}
    (h : warshall nodes edge source target = true) :
    Relation.ReflTransGen (Holds edge) source target := by
  induction nodes generalizing source target with
  | nil => exact Relation.ReflTransGen.single h
  | cons pivot rest ih =>
      simp only [warshall, addPivot, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨hsource, htarget⟩
      · exact ih h
      · exact (ih hsource).trans (ih htarget)

theorem reachableBool_sound {α : Type u} [DecidableEq α]
    (nodes : List α) (edge : BoolRel α) {source target : α}
    (h : reachableBool nodes edge source target = true) :
    Relation.ReflTransGen (Holds edge) source target := by
  have hclosed := warshall_sound nodes
    (fun left right => decide (left = right) || edge left right) h
  apply hclosed.lift' id
  intro left right hbase
  simp only [Holds, Bool.or_eq_true, decide_eq_true_eq] at hbase
  rcases hbase with rfl | hedge
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single hedge

theorem reachableBool_complete {α : Type u} [DecidableEq α]
    (nodes : List α) (edge : BoolRel α) (hcomplete : ∀ node, node ∈ nodes)
    {source target : α}
    (h : Relation.ReflTransGen (Holds edge) source target) :
    reachableBool nodes edge source target = true := by
  unfold reachableBool
  induction h with
  | refl =>
      apply warshall_of_base
      simp
  | @tail middle target hpath hedge ih =>
      apply warshall_trans_of_mem _ (hcomplete middle) ih
      apply warshall_of_base
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr hedge

/-- The executable checker is exactly reflexive-transitive directed reachability. -/
theorem reachableBool_eq_true_iff {α : Type u} [DecidableEq α]
    (nodes : List α) (edge : BoolRel α) (hcomplete : ∀ node, node ∈ nodes)
    (source target : α) :
    reachableBool nodes edge source target = true ↔
      Relation.ReflTransGen (Holds edge) source target :=
  ⟨reachableBool_sound nodes edge,
    reachableBool_complete nodes edge hcomplete⟩

theorem Enumeration.reachable_eq_true_iff {α : Type u} [DecidableEq α]
    (enumeration : Enumeration α) (edge : BoolRel α) (source target : α) :
    enumeration.reachable edge source target = true ↔
      Relation.ReflTransGen (Holds edge) source target := by
  exact reachableBool_eq_true_iff enumeration.nodes edge enumeration.complete source target

/-! ## Hostile executable controls -/

private inductive ProbeNode where
  | start
  | middle
  | finish
  | isolated
  deriving DecidableEq

private def probeEnumeration : Enumeration ProbeNode where
  nodes := [.start, .middle, .finish, .isolated]
  nodup := by decide
  complete node := by cases node <;> simp

private def chainEdge : BoolRel ProbeNode
  | .start, .middle => true
  | .middle, .finish => true
  | _, _ => false

private def cycleEdge : BoolRel ProbeNode
  | .start, .middle => true
  | .middle, .finish => true
  | .finish, .start => true
  | _, _ => false

/-- A two-edge directed chain is found. -/
example : probeEnumeration.reachable chainEdge .start .finish = true := by
  decide

/-- Directed closure does not silently reverse the chain. -/
example : probeEnumeration.reachable chainEdge .finish .start = false := by
  decide

/-- A listed but disconnected node remains unreachable from the chain. -/
example : probeEnumeration.reachable chainEdge .start .isolated = false := by
  decide

/-- Reflexivity holds even for a disconnected node. -/
example : probeEnumeration.reachable chainEdge .isolated .isolated = true := by
  decide

/-- A directed cycle makes the reverse route reachable through two pivots. -/
example : probeEnumeration.reachable cycleEdge .finish .middle = true := by
  decide

/-- The executable positive result produces the canonical semantic witness. -/
example : Relation.ReflTransGen (Holds chainEdge) ProbeNode.start ProbeNode.finish := by
  apply (probeEnumeration.reachable_eq_true_iff chainEdge .start .finish).mp
  decide

end GameTheory.Experimental.PostArchitecture.FiniteDirectedReachability
