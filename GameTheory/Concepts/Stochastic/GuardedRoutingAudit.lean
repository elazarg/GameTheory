/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice

/-!
# Guarded routing audit: the abstract skeleton

Provenance: this file is the game-free skeleton of the Question 77 audit, whose
full statement is recorded in an untracked local research note.  It formalizes
only the bookkeeping layer of that audit -- the part which is genuinely
independent of the analytic atlas -- over an arbitrary node type.  It is deliberately *not*
Theorem 77: the full guarded registry (refined obstruction cells, the coverage
formulas (8)-(9), the status-refined neutral graph (17) and its phase map (18))
is future work gated on the rank re-review.

The abstract package is a `LocalRuleSystem`: a well-founded rank codomain, a
rank assignment, and a local rule sending each node to `closed`, an explicit
finite child list, or a typed obstruction.

Two hypotheses are stated *on* such a system rather than bundled into it:

* `StrictProgress` -- every emitted child strictly decreases the rank;
* `ObstructionFree` -- no node reachable from the root emits an obstruction.

Both must remain assumable *and refutable*, so neither is a structure field
carrying its own proof.  Under them, `auditCertificate_of_strictProgress_of_`
`obstructionFree` produces an `AuditCertificate`: the reachable unfolding is a
finite set of nodes and every reachable leaf is closed.  This is Koenig-style
bookkeeping, not game mathematics: the strategic content of Question 77 (the
eight-gate child verifier, minimal strategic closure, guard coverage) lives
entirely in *establishing* `StrictProgress` for a concrete system, not here.

## The self-child falsifier

Question 77 section 1 exhibits the one-state, one-action, zero-payoff game whose
single local rule returns the singleton child list `[N]`.  Every child-validity
field passes and the rank codomain is well founded, yet the recursion is the
infinite self-chain `N ⇝ N ⇝ N ⇝ ⋯`.  `selfChildSystem` is that example, and
`not_strictProgress_selfChildSystem` machine-checks its lesson: a well-founded
rank *codomain* together with well-typed child data does **not** imply progress.
`not_wellFounded_childRel_selfChildSystem` and `selfChildSystem_infinite_branch`
sharpen this -- the child relation itself is not well founded and an infinite
branch exists -- while `selfChildSystem_obstructionFree` shows the failure is
not caused by a missing obstruction consumer.  The strict-descent hypothesis is
where all the content sits.

Note on scope: the falsifier refutes the *hypothesis*, not the conclusion.  Its
reachable node set is a singleton and hence finite; what fails is the branch
well-foundedness that `StrictProgress` supplies in general (`not_infinite_branch`).

`closedSystem` is the vacuity probe: the all-closed system satisfies both
hypotheses, so the interface is inhabited and the positive theorem is not empty.
-/

set_option autoImplicit false

universe u v w

namespace GameTheory
namespace GuardedRouting

/-- The three outputs a local rule may return at a node: a terminal closed
output, an explicit finite list of purported strict children, or a typed
unresolved obstruction. -/
inductive LocalRuleOutput (Node : Type u) (Obstruction : Type w) where
  /-- The node is discharged by a terminal output. -/
  | closed : LocalRuleOutput Node Obstruction
  /-- The node is expanded into an explicitly enumerated finite child list. -/
  | children (list : List Node) : LocalRuleOutput Node Obstruction
  /-- The node emits a typed obstruction. -/
  | obstruction (o : Obstruction) : LocalRuleOutput Node Obstruction

/-- An abstract local rule system.

The `rankLt_wf` field is only the *codomain* hypothesis of Question 77 equation
(1): it says the order on ranks is well founded.  It deliberately says nothing
about the child relation; `StrictProgress` is the separate, refutable statement
that children actually descend, and `selfChildSystem` shows the gap is real. -/
structure LocalRuleSystem (Node : Type u) (Rank : Type v)
    (Obstruction : Node → Type w) where
  /-- The strict order used to compare ranks. -/
  rankLt : Rank → Rank → Prop
  /-- The rank order is well founded.  A codomain hypothesis only. -/
  rankLt_wf : WellFounded rankLt
  /-- The rank assigned to each node. -/
  rank : Node → Rank
  /-- The local rule classifying each node. -/
  step : (n : Node) → LocalRuleOutput Node (Obstruction n)

namespace LocalRuleSystem

variable {Node : Type u} {Rank : Type v} {Obstruction : Node → Type w}

/-- The children emitted at a node.  Closed and obstructed nodes emit none. -/
def childrenOf (S : LocalRuleSystem Node Rank Obstruction) (n : Node) : List Node :=
  match S.step n with
  | .closed => []
  | .children list => list
  | .obstruction _ => []

/-- The rule discharges the node with a terminal closed output. -/
def IsClosed (S : LocalRuleSystem Node Rank Obstruction) (n : Node) : Prop :=
  S.step n = .closed

/-- The rule expands the node into a child list. -/
def Expands (S : LocalRuleSystem Node Rank Obstruction) (n : Node) : Prop :=
  ∃ list : List Node, S.step n = .children list

/-- The rule returns a typed obstruction at the node. -/
def EmitsObstruction (S : LocalRuleSystem Node Rank Obstruction) (n : Node) : Prop :=
  ∃ o : Obstruction n, S.step n = .obstruction o

/-- A leaf is a node the rule does not expand.

This is stronger than "emits no child": the degenerate output `children []` has
an empty child list yet is an expansion, so it is not a leaf.  Keeping the two
notions apart is what makes `leaf_isClosed` an honest statement. -/
def IsLeaf (S : LocalRuleSystem Node Rank Obstruction) (n : Node) : Prop :=
  ¬ S.Expands n

/-- Every node is closed, expanded, or obstructed. -/
theorem isClosed_or_expands_or_emitsObstruction
    (S : LocalRuleSystem Node Rank Obstruction) (n : Node) :
    S.IsClosed n ∨ S.Expands n ∨ S.EmitsObstruction n := by
  rcases hstep : S.step n with _ | list | o
  · exact Or.inl hstep
  · exact Or.inr (Or.inl ⟨list, hstep⟩)
  · exact Or.inr (Or.inr ⟨o, hstep⟩)

@[simp] theorem childrenOf_of_children
    (S : LocalRuleSystem Node Rank Obstruction) {n : Node} {list : List Node}
    (h : S.step n = .children list) : S.childrenOf n = list := by
  unfold childrenOf
  rw [h]

@[simp] theorem childrenOf_of_isClosed
    (S : LocalRuleSystem Node Rank Obstruction) {n : Node} (h : S.IsClosed n) :
    S.childrenOf n = [] := by
  unfold childrenOf
  rw [h]

@[simp] theorem childrenOf_of_emitsObstruction
    (S : LocalRuleSystem Node Rank Obstruction) {n : Node}
    (h : S.EmitsObstruction n) : S.childrenOf n = [] := by
  obtain ⟨o, ho⟩ := h
  unfold childrenOf
  rw [ho]

/-- Reachability from a root by following emitted child lists. -/
inductive Reachable (S : LocalRuleSystem Node Rank Obstruction) (root : Node) :
    Node → Prop
  /-- The root is reachable from itself. -/
  | root : Reachable S root root
  /-- A child of a reachable node is reachable. -/
  | child {n c : Node} (hn : Reachable S root n) (hc : c ∈ S.childrenOf n) :
      Reachable S root c

/-- A node reachable from a root is the root itself or lies below one of the
root's emitted children. -/
theorem reachable_cases {S : LocalRuleSystem Node Rank Obstruction} {root m : Node}
    (h : S.Reachable root m) :
    m = root ∨ ∃ c ∈ S.childrenOf root, S.Reachable c m := by
  induction h with
  | root => exact Or.inl rfl
  | child _ hc ih =>
      rcases ih with rfl | ⟨c', hc', hreach⟩
      · exact Or.inr ⟨_, hc, Reachable.root⟩
      · exact Or.inr ⟨c', hc', Reachable.child hreach hc⟩

/-- The reachable set of a node is contained in the node together with the
reachable sets of its emitted children. -/
theorem reachable_subset_insert_biUnion
    (S : LocalRuleSystem Node Rank Obstruction) (root : Node) :
    {m | S.Reachable root m} ⊆
      insert root
        (⋃ c ∈ ({c | c ∈ S.childrenOf root} : Set Node), {m | S.Reachable c m}) := by
  intro m hm
  rcases reachable_cases hm with rfl | ⟨c, hc, hreach⟩
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_biUnion hc hreach)

/-- Strict progress: every child emitted anywhere strictly decreases the rank.

This is the load-bearing hypothesis of the audit; it is stated on the system so
that it can be assumed *and refuted* (see `not_strictProgress_selfChildSystem`). -/
def StrictProgress (S : LocalRuleSystem Node Rank Obstruction) : Prop :=
  ∀ n : Node, ∀ c ∈ S.childrenOf n, S.rankLt (S.rank c) (S.rank n)

/-- Obstruction freedom: no node reachable from the root emits an obstruction.
This is the abstract shadow of the coverage formula (8) of Question 77. -/
def ObstructionFree (S : LocalRuleSystem Node Rank Obstruction) (root : Node) : Prop :=
  ∀ n : Node, S.Reachable root n → ¬ S.EmitsObstruction n

/-- Under strict progress the child relation itself is well founded. -/
theorem childRel_wf (S : LocalRuleSystem Node Rank Obstruction)
    (hprog : StrictProgress S) :
    WellFounded (fun c n : Node => c ∈ S.childrenOf n) := by
  have hinv : WellFounded (InvImage S.rankLt S.rank) := InvImage.wf S.rank S.rankLt_wf
  refine Subrelation.wf ?_ hinv
  intro c n hc
  exact hprog n c hc

/-- Under strict progress there is no infinite branch: no sequence of nodes in
which each entry is an emitted child of its predecessor. -/
theorem not_infinite_branch (S : LocalRuleSystem Node Rank Obstruction)
    (hprog : StrictProgress S) (f : ℕ → Node) :
    ¬ ∀ k : ℕ, f (k + 1) ∈ S.childrenOf (f k) := by
  intro hf
  have key : ∀ n : Node, Acc (fun c m : Node => c ∈ S.childrenOf m) n →
      ∀ g : ℕ → Node, (∀ k : ℕ, g (k + 1) ∈ S.childrenOf (g k)) → g 0 ≠ n := by
    intro n hacc
    induction hacc with
    | intro x _ ih =>
        intro g hg hg0
        have hstep : g 1 ∈ S.childrenOf x := by
          rw [← hg0]
          exact hg 0
        exact ih (g 1) hstep (fun k => g (k + 1)) (fun k => hg (k + 1)) rfl
  exact key (f 0) ((S.childRel_wf hprog).apply (f 0)) f hf rfl

/-- Under strict progress the reachable unfolding from any root is a finite set
of nodes.  Finite child lists supply the branching bound and the well-founded
child relation supplies the depth bound; this is the Koenig step. -/
theorem reachable_finite (S : LocalRuleSystem Node Rank Obstruction)
    (hprog : StrictProgress S) (root : Node) :
    {m | S.Reachable root m}.Finite := by
  refine (S.childRel_wf hprog).induction
    (C := fun n : Node => {m | S.Reachable n m}.Finite) root ?_
  intro n ih
  refine Set.Finite.subset ?_ (S.reachable_subset_insert_biUnion n)
  refine Set.Finite.insert n ?_
  refine Set.Finite.biUnion (List.finite_toSet _) ?_
  intro c hc
  exact ih c hc

/-- If no reachable node is obstructed, every reachable leaf is closed. -/
theorem leaf_isClosed (S : LocalRuleSystem Node Rank Obstruction) {root : Node}
    (hfree : ObstructionFree S root) {n : Node} (hn : S.Reachable root n)
    (hleaf : S.IsLeaf n) : S.IsClosed n := by
  rcases S.isClosed_or_expands_or_emitsObstruction n with h | h | h
  · exact h
  · exact absurd h hleaf
  · exact absurd h (hfree n hn)

/-- Every reachable node with an empty emitted child list is either closed or
carries the degenerate empty expansion.  Recorded to keep `AuditCertificate`
honest about what "leaf" means. -/
theorem reachable_childless_isClosed_or_empty_expansion
    (S : LocalRuleSystem Node Rank Obstruction) {root : Node}
    (hfree : ObstructionFree S root) {n : Node} (hn : S.Reachable root n)
    (hnil : S.childrenOf n = []) :
    S.IsClosed n ∨ S.step n = .children [] := by
  rcases S.isClosed_or_expands_or_emitsObstruction n with h | h | h
  · exact Or.inl h
  · obtain ⟨list, hlist⟩ := h
    have hlistNil : list = [] := by
      rw [← S.childrenOf_of_children hlist]
      exact hnil
    exact Or.inr (hlistNil ▸ hlist)
  · exact absurd h (hfree n hn)

/-- The audit certificate: the finite reachable unfolding of a root together
with the fact that every reachable leaf is discharged by a closed output.

No field of this structure is assumed anywhere; it is only ever produced by
`auditCertificate_of_strictProgress_of_obstructionFree`. -/
structure AuditCertificate (S : LocalRuleSystem Node Rank Obstruction)
    (root : Node) : Prop where
  /-- The set of nodes reachable from the root is finite. -/
  reachableFinite : {n | S.Reachable root n}.Finite
  /-- Every reachable leaf carries a terminal closed output. -/
  leafClosed : ∀ n : Node, S.Reachable root n → S.IsLeaf n → S.IsClosed n

/-- Positive theorem.  Strict progress plus obstruction freedom yield the audit
certificate at the given root.

This is bookkeeping, not game mathematics: all strategic content of Question 77
is consumed in discharging `StrictProgress` and `ObstructionFree`. -/
theorem auditCertificate_of_strictProgress_of_obstructionFree
    (S : LocalRuleSystem Node Rank Obstruction) {root : Node}
    (hprog : StrictProgress S) (hfree : ObstructionFree S root) :
    AuditCertificate S root :=
  { reachableFinite := S.reachable_finite hprog root
    leafClosed := fun _ hn hleaf => S.leaf_isClosed hfree hn hleaf }

end LocalRuleSystem

open LocalRuleSystem

/-! ### The self-child falsifier of Question 77 section 1 -/

/-- The one-node self-child system: a single node whose rule returns the
singleton child list containing that same node.  The rank codomain is `Unit`
with the empty (hence vacuously well-founded) order, and no obstruction can be
emitted since the obstruction family is `Empty`. -/
def selfChildSystem : LocalRuleSystem Unit Unit (fun _ => Empty) where
  rankLt := fun _ _ => False
  rankLt_wf := WellFounded.intro fun a => Acc.intro a fun _ h => h.elim
  rank := fun _ => ()
  step := fun _ => .children [()]

@[simp] theorem selfChildSystem_childrenOf (n : Unit) :
    selfChildSystem.childrenOf n = [()] := rfl

/-- The rank codomain of the self-child system is well founded. -/
theorem selfChildSystem_rankLt_wellFounded :
    WellFounded selfChildSystem.rankLt :=
  selfChildSystem.rankLt_wf

/-- The self-child system emits no obstruction anywhere, so its failure is not
a missing consumer. -/
theorem selfChildSystem_obstructionFree (root : Unit) :
    ObstructionFree selfChildSystem root := by
  intro n _ h
  obtain ⟨o, _⟩ := h
  exact o.elim

/-- **Falsifier.**  Despite a well-founded rank codomain and well-typed child
data, the self-child system fails strict progress: its child does not descend. -/
theorem not_strictProgress_selfChildSystem :
    ¬ StrictProgress selfChildSystem := by
  intro hprog
  exact hprog () () (by simp)

/-- The self-child relation is not well founded, so no induction on children is
available for it. -/
theorem not_wellFounded_childRel_selfChildSystem :
    ¬ WellFounded (fun c n : Unit => c ∈ selfChildSystem.childrenOf n) := by
  intro hwf
  have key : ∀ x : Unit,
      Acc (fun c n : Unit => c ∈ selfChildSystem.childrenOf n) x → False := by
    intro x hx
    induction hx with
    | intro y _ ih => exact ih () (by simp)
  exact key () (hwf.apply ())

/-- The self-chain `N ⇝ N ⇝ N ⇝ ⋯` of Question 77 section 1, exhibited as an
infinite branch.  Contrast `LocalRuleSystem.not_infinite_branch`. -/
theorem selfChildSystem_infinite_branch (k : ℕ) :
    (fun _ : ℕ => ()) (k + 1) ∈
      selfChildSystem.childrenOf ((fun _ : ℕ => ()) k) := by
  simp

/-! ### Vacuity probe: the all-closed system -/

/-- The all-closed system over an arbitrary node type: every node is discharged
immediately by a terminal output. -/
def closedSystem (Node : Type u) : LocalRuleSystem Node Unit (fun _ => Empty) where
  rankLt := fun _ _ => False
  rankLt_wf := WellFounded.intro fun a => Acc.intro a fun _ h => h.elim
  rank := fun _ => ()
  step := fun _ => .closed

@[simp] theorem closedSystem_childrenOf {Node : Type u} (n : Node) :
    (closedSystem Node).childrenOf n = [] := rfl

/-- The all-closed system satisfies strict progress vacuously. -/
theorem strictProgress_closedSystem (Node : Type u) :
    StrictProgress (closedSystem Node) := by
  intro n c hc
  simp at hc

/-- The all-closed system emits no obstruction. -/
theorem obstructionFree_closedSystem (Node : Type u) (root : Node) :
    ObstructionFree (closedSystem Node) root := by
  intro n _ h
  obtain ⟨o, _⟩ := h
  exact o.elim

/-- Vacuity probe: the audit interface is inhabited.  The all-closed system
satisfies both hypotheses and therefore carries an audit certificate. -/
theorem auditCertificate_closedSystem (Node : Type u) (root : Node) :
    AuditCertificate (closedSystem Node) root :=
  auditCertificate_of_strictProgress_of_obstructionFree (closedSystem Node)
    (strictProgress_closedSystem Node) (obstructionFree_closedSystem Node root)

end GuardedRouting
end GameTheory
