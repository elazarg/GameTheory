/-
# EXP-104: ancestral-moral separation for finite Bayesian-network queries

This owner-free graph experiment starts only from finite parent scopes.  It
restricts to the ancestors of the two queried coordinate sets and the evidence,
moralizes that ancestral graph, and only then deletes the evidence vertices.

No global Markov theorem is claimed here.  The purpose of this file is to
validate the graph-side relation and its factor-scope clique property before a
factorization proof connects it to finite conditional independence.
-/

import GameTheory.Math.DAG

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation

universe uNode

variable {Node : Type uNode}

/-- A directed parent edge. -/
def DirectedEdge [DecidableEq Node] (parents : Node → Finset Node)
    (parent child : Node) : Prop :=
  parent ∈ parents child

/-- Directed ancestry, including the node itself. -/
def AncestorOrSelf [DecidableEq Node] (parents : Node → Finset Node)
    (ancestor descendant : Node) : Prop :=
  Relation.ReflTransGen (DirectedEdge parents) ancestor descendant

/-- The finite root set used by an `X ⟂ Y | Z` query. -/
def queryRoots [DecidableEq Node]
    (first second evidence : Finset Node) : Finset Node :=
  first ∪ second ∪ evidence

/-- Membership in the ancestors of `X ∪ Y ∪ Z`. -/
def InAncestralClosure [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node) (node : Node) : Prop :=
  ∃ root ∈ queryRoots first second evidence,
    AncestorOrSelf parents node root

/-- Adjacency in the moralized ancestral graph after deleting evidence.

The child witnessing a co-parent edge must itself be ancestral. -/
def MoralAdjacent [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node)
    (left right : Node) : Prop :=
  left ≠ right ∧
    left ∉ evidence ∧
    right ∉ evidence ∧
    InAncestralClosure parents first second evidence left ∧
    InAncestralClosure parents first second evidence right ∧
    (DirectedEdge parents left right ∨
      DirectedEdge parents right left ∨
      ∃ child,
        InAncestralClosure parents first second evidence child ∧
        DirectedEdge parents left child ∧
        DirectedEdge parents right child)

/-- Connectivity in the ancestral moral graph with evidence deleted. -/
def Connected [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node)
    (left right : Node) : Prop :=
  left ∉ evidence ∧
    right ∉ evidence ∧
    Relation.ReflTransGen
      (MoralAdjacent parents first second evidence) left right

/-- Setwise ancestral-moral separation. -/
def Separates [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node) : Prop :=
  ∀ left ∈ first, ∀ right ∈ second,
    ¬ Connected parents first second evidence left right

/-- Every parent of an ancestral child is itself ancestral. -/
theorem parent_mem_ancestralClosure [DecidableEq Node]
    {parents : Node → Finset Node}
    {first second evidence : Finset Node} {parent child : Node}
    (hchild : InAncestralClosure parents first second evidence child)
    (hparent : parent ∈ parents child) :
    InAncestralClosure parents first second evidence parent := by
  obtain ⟨root, hroot, path⟩ := hchild
  exact ⟨root, hroot,
    Relation.ReflTransGen.head hparent path⟩

/-- The scope of every ancestral factor is a clique after moralization (apart
from deleted evidence vertices).  This is the load-bearing bridge needed by a
later factor-elimination proof. -/
theorem factorScope_pairwise_moralAdjacent [DecidableEq Node]
    {parents : Node → Finset Node}
    {queryFirst querySecond evidence : Finset Node} {child left right : Node}
    (hchild :
      InAncestralClosure parents queryFirst querySecond evidence child)
    (hleft : left ∈ insert child (parents child))
    (hright : right ∈ insert child (parents child))
    (hne : left ≠ right) (hleftOpen : left ∉ evidence)
    (hrightOpen : right ∉ evidence) :
    MoralAdjacent parents queryFirst querySecond evidence left right := by
  rcases Finset.mem_insert.mp hleft with hleftChild | hleftParent
  · subst left
    rcases Finset.mem_insert.mp hright with hrightChild | hrightParent
    · exact (hne hrightChild.symm).elim
    · exact ⟨hne, hleftOpen, hrightOpen, hchild,
        parent_mem_ancestralClosure hchild hrightParent,
        Or.inr (Or.inl hrightParent)⟩
  · rcases Finset.mem_insert.mp hright with hrightChild | hrightParent
    · subst right
      exact ⟨hne, hleftOpen, hrightOpen,
        parent_mem_ancestralClosure hchild hleftParent, hchild,
        Or.inl hleftParent⟩
    · exact ⟨hne, hleftOpen, hrightOpen,
        parent_mem_ancestralClosure hchild hleftParent,
        parent_mem_ancestralClosure hchild hrightParent,
        Or.inr (Or.inr ⟨child, hchild, hleftParent, hrightParent⟩)⟩

/-! ## Chain and collider controls -/

inductive ControlNode
  | left
  | middle
  | right
  deriving DecidableEq

def queryFirst : Finset ControlNode := {.left}

def querySecond : Finset ControlNode := {.right}

namespace Chain

def parents : ControlNode → Finset ControlNode
  | .left => ∅
  | .middle => {.left}
  | .right => {.middle}

def noEvidence : Finset ControlNode := ∅

def middleEvidence : Finset ControlNode := {.middle}

theorem not_separated_without_evidence :
    ¬ Separates parents queryFirst querySecond noEvidence := by
  have leftClosure : InAncestralClosure parents queryFirst querySecond
      noEvidence .left :=
    ⟨.left, by simp [queryRoots, queryFirst], Relation.ReflTransGen.refl⟩
  have rightClosure : InAncestralClosure parents queryFirst querySecond
      noEvidence .right :=
    ⟨.right, by simp [queryRoots, querySecond], Relation.ReflTransGen.refl⟩
  have middleRight : DirectedEdge parents .middle .right := by
    simp [DirectedEdge, parents]
  have middleClosure : InAncestralClosure parents queryFirst querySecond
      noEvidence .middle :=
    ⟨.right, by simp [queryRoots, querySecond],
      Relation.ReflTransGen.single middleRight⟩
  have leftMiddle : DirectedEdge parents .left .middle := by
    simp [DirectedEdge, parents]
  have firstStep : MoralAdjacent parents queryFirst querySecond noEvidence
      .left .middle :=
    ⟨by decide, by simp [noEvidence], by simp [noEvidence],
      leftClosure, middleClosure, Or.inl leftMiddle⟩
  have secondStep : MoralAdjacent parents queryFirst querySecond noEvidence
      .middle .right :=
    ⟨by decide, by simp [noEvidence], by simp [noEvidence],
      middleClosure, rightClosure, Or.inl middleRight⟩
  intro separated
  exact separated .left (by simp [queryFirst]) .right (by simp [querySecond])
    ⟨by simp [noEvidence], by simp [noEvidence],
      Relation.ReflTransGen.head firstStep
        (Relation.ReflTransGen.single secondStep)⟩

theorem separated_by_middle :
    Separates parents queryFirst querySecond middleEvidence := by
  intro source hsource target htarget
  have hsourceEq : source = .left := by simpa [queryFirst] using hsource
  have htargetEq : target = .right := by simpa [querySecond] using htarget
  subst source
  subst target
  rintro ⟨_, _, connection⟩
  have isolated : ∀ next,
      ¬ MoralAdjacent parents queryFirst querySecond middleEvidence
        .left next := by
    intro next adjacent
    rcases adjacent with
      ⟨hne, _, hnextOpen, _, _, hforward | hbackward | hcoparents⟩
    · cases next with
      | left => exact hne rfl
      | middle => exact hnextOpen (by simp [middleEvidence])
      | right =>
          simp [DirectedEdge, parents] at hforward
    · cases next <;>
        simp [DirectedEdge, parents] at hbackward
    · obtain ⟨child, _, hleftParent, hnextParent⟩ := hcoparents
      cases child with
      | left => simp [DirectedEdge, parents] at hleftParent
      | middle =>
          have hnextEq : next = .left := by
            cases next <;>
              simp [DirectedEdge, parents] at hnextParent ⊢
          exact hne hnextEq.symm
      | right => simp [DirectedEdge, parents] at hleftParent
  rcases Relation.ReflTransGen.cases_head connection with
    equality | ⟨next, firstStep, _⟩
  · cases equality
  · exact isolated next firstStep

end Chain

namespace Collider

def parents : ControlNode → Finset ControlNode
  | .left => ∅
  | .middle => {.left, .right}
  | .right => ∅

def noEvidence : Finset ControlNode := ∅

def middleEvidence : Finset ControlNode := {.middle}

private theorem middle_not_ancestral_without_evidence :
    ¬ InAncestralClosure parents queryFirst querySecond noEvidence .middle := by
  have noOutgoing : ∀ next, ¬ DirectedEdge parents .middle next := by
    intro next
    cases next <;> simp [DirectedEdge, parents]
  rintro ⟨root, hroot, path⟩
  cases root with
  | left =>
      rcases Relation.ReflTransGen.cases_head path with
        equality | ⟨next, edge, _⟩
      · cases equality
      · exact noOutgoing next edge
  | middle =>
      simp [queryRoots, queryFirst, querySecond, noEvidence] at hroot
  | right =>
      rcases Relation.ReflTransGen.cases_head path with
        equality | ⟨next, edge, _⟩
      · cases equality
      · exact noOutgoing next edge

theorem separated_without_evidence :
    Separates parents queryFirst querySecond noEvidence := by
  intro source hsource target htarget
  have hsourceEq : source = .left := by simpa [queryFirst] using hsource
  have htargetEq : target = .right := by simpa [querySecond] using htarget
  subst source
  subst target
  rintro ⟨_, _, connection⟩
  have isolated : ∀ next,
      ¬ MoralAdjacent parents queryFirst querySecond noEvidence
        .left next := by
    intro next adjacent
    rcases adjacent with
      ⟨hne, _, _, _, hnextClosure,
        hforward | hbackward | hcoparents⟩
    · cases next with
      | left => exact hne rfl
      | middle => exact middle_not_ancestral_without_evidence hnextClosure
      | right => simp [DirectedEdge, parents] at hforward
    · cases next <;> simp [DirectedEdge, parents] at hbackward
    · obtain ⟨child, hchildClosure, hleftParent, _⟩ := hcoparents
      cases child with
      | left => simp [DirectedEdge, parents] at hleftParent
      | middle =>
          exact middle_not_ancestral_without_evidence hchildClosure
      | right => simp [DirectedEdge, parents] at hleftParent
  rcases Relation.ReflTransGen.cases_head connection with
    equality | ⟨next, firstStep, _⟩
  · cases equality
  · exact isolated next firstStep

theorem not_separated_by_middle :
    ¬ Separates parents queryFirst querySecond middleEvidence := by
  have middleClosure : InAncestralClosure parents queryFirst querySecond
      middleEvidence .middle :=
    ⟨.middle, by simp [queryRoots, middleEvidence],
      Relation.ReflTransGen.refl⟩
  have leftParent : DirectedEdge parents .left .middle := by
    simp [DirectedEdge, parents]
  have rightParent : DirectedEdge parents .right .middle := by
    simp [DirectedEdge, parents]
  have moralEdge : MoralAdjacent parents queryFirst querySecond middleEvidence
      .left .right :=
    factorScope_pairwise_moralAdjacent middleClosure
      (Finset.mem_insert_of_mem leftParent)
      (Finset.mem_insert_of_mem rightParent) (by decide)
      (by simp [middleEvidence]) (by simp [middleEvidence])
  intro separated
  exact separated .left (by simp [queryFirst]) .right (by simp [querySecond])
    ⟨by simp [middleEvidence], by simp [middleEvidence],
      Relation.ReflTransGen.single moralEdge⟩

end Collider

end GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation
