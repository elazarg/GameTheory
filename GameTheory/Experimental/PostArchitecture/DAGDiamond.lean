/-
# EXP-039: arbitrary-carrier finite DAG

The diamond has two incomparable middle vertices. It checks that the DAG
substrate derives an order without storing one and proves both direct and
transitive predecessors occur earlier.
-/

import GameTheory.Math.DAG
import Mathlib.Data.Fintype.OfMap

namespace GameTheory.Experimental.DAGDiamond

inductive Vertex
  | root
  | left
  | right
  | sink
  deriving DecidableEq

instance : Fintype Vertex :=
  Fintype.ofList [.root, .left, .right, .sink] (by
    intro vertex
    cases vertex <;> simp)

def predecessors : Vertex → Finset Vertex
  | .root => ∅
  | .left => {.root}
  | .right => {.root}
  | .sink => {.left, .right}

def rank : Vertex → Nat
  | .root => 0
  | .left | .right => 1
  | .sink => 2

theorem rank_lt_of_predecessor {first second : Vertex}
    (hedge : first ∈ predecessors second) :
    rank first < rank second := by
  cases first <;> cases second <;> simp_all [predecessors, rank]

theorem acyclic :
    GameTheory.Math.DAG.Acyclic
      (fun first second => first ∈ predecessors second) := by
  intro vertex hcycle
  have rank_lt_of_path : ∀ {first second : Vertex},
      Relation.TransGen
        (fun source target => source ∈ predecessors target)
        first second →
      rank first < rank second := by
    intro first second path
    induction path with
    | single hedge => exact rank_lt_of_predecessor hedge
    | tail _ hedge ih =>
        exact ih.trans (rank_lt_of_predecessor hedge)
  have hrank : rank vertex < rank vertex :=
    rank_lt_of_path hcycle
  exact Nat.lt_irrefl _ hrank

noncomputable def topological :
    GameTheory.Math.DAG.TopologicalOrder predecessors :=
  Classical.choice
    (GameTheory.Math.DAG.topologicalOrder_of_acyclic acyclic)

theorem middle_vertices_incomparable :
    .left ∉ predecessors .right ∧
      .right ∉ predecessors .left := by
  decide

theorem root_ancestor_sink :
    Relation.TransGen
      (fun first second => first ∈ predecessors second)
      .root .sink := by
  have hrootLeft : .root ∈ predecessors .left := by
    simp [predecessors]
  have hleftSink : .left ∈ predecessors .sink := by
    simp [predecessors]
  exact (Relation.TransGen.single hrootLeft).tail hleftSink

theorem root_occurs_before_sink
    {rootIndex sinkIndex : Fin topological.order.length}
    (hroot : topological.order[rootIndex] = .root)
    (hsink : topological.order[sinkIndex] = .sink) :
    rootIndex.val < sinkIndex.val :=
  topological.ancestor_lt root_ancestor_sink hroot hsink

theorem left_occurs_before_sink
    {leftIndex sinkIndex : Fin topological.order.length}
    (hleft : topological.order[leftIndex] = .left)
    (hsink : topological.order[sinkIndex] = .sink) :
    leftIndex.val < sinkIndex.val := by
  obtain ⟨found, hlt, heq⟩ :=
    topological.predecessor_lt
      (show .left ∈ predecessors .sink by simp [predecessors])
      hsink
  have hsame : leftIndex = found :=
    topological.nodup.get_inj_iff.mp (hleft.trans heq.symm)
  simpa only [hsame] using hlt

end GameTheory.Experimental.DAGDiamond
