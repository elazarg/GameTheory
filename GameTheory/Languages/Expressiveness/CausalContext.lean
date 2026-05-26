/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.Expressiveness.Relations
import GameTheory.Languages.Bridges.MAID_EFG

/-!
# Causal Context-Free EFG Trees

This file gives an EFG-facing characterization of the MAID fragment.

The useful structural idea is not "there exists a MAID that generated this
tree".  It is:

* play is an assignment tree over a fixed finite family of causal variables;
* every variable has a fixed finite value type, independent of the previous
  path through the tree;
* a chance variable is sampled from a fixed conditional distribution depending
  only on its fixed parent variables;
* a decision variable is chosen by a fixed player from that variable's fixed
  value type;
* the decision's information set is exactly the fiber of the fixed projection
  to its observed parent variables;
* utility coordinates are deterministic singleton-valued coordinates whose
  payoff contribution depends only on fixed parent variables;
* the parent relation is acyclic, so any topological order can be unrolled as
  an EFG assignment tree.

That is the "causal context-free choices" shape: the context can affect what a
player observes and what chance probabilities/utilities are used, but it cannot
change which decision variable is being chosen or which alternatives that
variable has.
-/

namespace GameTheory
namespace Languages
namespace Expressiveness

/-- A causal variable is either a chance coordinate, a player-owned decision
coordinate, or a player-owned utility coordinate.

This reuses the already-developed three-way node tag so that the exact
conversion to the existing MAID semantics is definitional.  The surrounding
`CausalContextFreeForm` fields give the EFG-side reading. -/
abbrev CausalNodeKind (Player : Type) := MAID.NodeKind Player

/-- Semantic form for an assignment-tree EFG with causal context-free choices.

This is the intrinsic EFG-side schema for the MAID fragment.  The syntax is a
finite list of causal variables, not arbitrary tree nodes.  A generated EFG tree
gets its nodes by walking a topological order and branching on the fixed value
type of each variable. -/
structure CausalContextFreeForm (m : Nat) where
  /-- Number of causal variables. -/
  nodeCount : Nat
  /-- Chance/decision/utility role of each causal variable. -/
  kind : Fin nodeCount → CausalNodeKind (Fin m)
  /-- Fixed causal parents.  Chance laws and utility functions depend only on
  these coordinates. -/
  parents : Fin nodeCount → Finset (Fin nodeCount)
  /-- Fixed observed parents.  At a decision variable, information sets are
  fibers of the projection to this set. -/
  obsParents : Fin nodeCount → Finset (Fin nodeCount)
  /-- Fixed value/action domain of each causal variable. -/
  Val : Fin nodeCount → Type
  instFintype : ∀ nd, Fintype (Val nd)
  instDecidableEq : ∀ nd, DecidableEq (Val nd)
  instInhabited : ∀ nd, Inhabited (Val nd)
  /-- A decision can only observe causal parents. -/
  obs_sub : ∀ nd, obsParents nd ⊆ parents nd
  /-- Non-decision variables observe all parents, since they have no strategic
  information-set coarsening. -/
  obs_eq_nondec : ∀ nd, (¬ ∃ p, kind nd = .decision p) → obsParents nd = parents nd
  /-- Utility variables carry no extra random or strategic content; the payoff
  contribution is stored in `utilityFn`. -/
  utility_unique : ∀ nd p, kind nd = .utility p → Unique (Val nd)
  /-- Causal parenthood is acyclic. -/
  acyclic : DAG.Acyclic (· ∈ parents ·)
  /-- Context-free chance law: a chance coordinate's distribution is a function
  of a fixed parent projection, not of the whole history. -/
  chanceCPD :
    (c : { nd : Fin nodeCount // kind nd = .chance }) →
      ((nd : ↥(parents c.val)) → Val nd.val) → PMF (Val c.val)
  /-- Context-free payoff law: a utility coordinate's contribution is a function
  of a fixed parent projection, not of the whole history. -/
  utilityFn :
    (p : Fin m) →
      (u : { nd : Fin nodeCount // kind nd = .utility p }) →
        ((nd : ↥(parents u.val)) → Val nd.val) → ℝ

namespace CausalContextFreeForm

variable {m : Nat}

instance (F : CausalContextFreeForm m) (nd : Fin F.nodeCount) :
    Fintype (F.Val nd) :=
  F.instFintype nd

instance (F : CausalContextFreeForm m) (nd : Fin F.nodeCount) :
    DecidableEq (F.Val nd) :=
  F.instDecidableEq nd

instance (F : CausalContextFreeForm m) (nd : Fin F.nodeCount) :
    Inhabited (F.Val nd) :=
  F.instInhabited nd

/-- Chance coordinate subtype. -/
abbrev ChanceNode (F : CausalContextFreeForm m) :=
  { nd : Fin F.nodeCount // F.kind nd = .chance }

/-- Decision coordinate subtype for a player. -/
abbrev DecisionNode (F : CausalContextFreeForm m) (p : Fin m) :=
  { nd : Fin F.nodeCount // F.kind nd = .decision p }

/-- Utility coordinate subtype for a player. -/
abbrev UtilityNode (F : CausalContextFreeForm m) (p : Fin m) :=
  { nd : Fin F.nodeCount // F.kind nd = .utility p }

/-- Configuration on a fixed set of causal variables. -/
abbrev Cfg (F : CausalContextFreeForm m) (ps : Finset (Fin F.nodeCount)) :=
  (nd : ↥ps) → F.Val nd.val

/-- Total assignment to all causal variables. -/
abbrev TAssign (F : CausalContextFreeForm m) :=
  ∀ nd : Fin F.nodeCount, F.Val nd

instance (F : CausalContextFreeForm m) : Fintype (ChanceNode F) :=
  Subtype.fintype _

instance (F : CausalContextFreeForm m) (p : Fin m) : Fintype (DecisionNode F p) :=
  Subtype.fintype _

instance (F : CausalContextFreeForm m) (p : Fin m) : Fintype (UtilityNode F p) :=
  Subtype.fintype _

instance (F : CausalContextFreeForm m) : DecidableEq (ChanceNode F) :=
  inferInstanceAs (DecidableEq { nd : Fin F.nodeCount // F.kind nd = .chance })

instance (F : CausalContextFreeForm m) (p : Fin m) : DecidableEq (DecisionNode F p) :=
  inferInstanceAs (DecidableEq { nd : Fin F.nodeCount // F.kind nd = .decision p })

instance (F : CausalContextFreeForm m) (p : Fin m) : DecidableEq (UtilityNode F p) :=
  inferInstanceAs (DecidableEq { nd : Fin F.nodeCount // F.kind nd = .utility p })

instance (F : CausalContextFreeForm m) (ps : Finset (Fin F.nodeCount)) :
    Fintype (Cfg F ps) :=
  inferInstance

instance (F : CausalContextFreeForm m) (ps : Finset (Fin F.nodeCount)) :
    DecidableEq (Cfg F ps) :=
  inferInstanceAs (DecidableEq ((nd : ↥ps) → F.Val nd.val))

/-- EFG information set induced by a context-free causal decision:
the decision variable plus the fixed observed-parent projection. -/
abbrev Infoset (F : CausalContextFreeForm m) (p : Fin m) :=
  Σ (d : DecisionNode F p), Cfg F (F.obsParents d.val)

/-- Alternatives available at a causal information set: the fixed value domain
of its decision variable.  This is the context-free-choice condition in type
form. -/
abbrev Action (F : CausalContextFreeForm m) {p : Fin m} (I : Infoset F p) :=
  F.Val I.1.val

/-- Project a full causal assignment to a fixed set of observed coordinates. -/
def obsProjection (F : CausalContextFreeForm m) (a : TAssign F)
    (ps : Finset (Fin F.nodeCount)) : Cfg F ps :=
  fun nd => a nd.val

@[simp] theorem obsProjection_apply (F : CausalContextFreeForm m)
    (a : TAssign F) (ps : Finset (Fin F.nodeCount)) (nd : ↥ps) :
    F.obsProjection a ps nd = a nd.val :=
  rfl

/-- The causal information set reached at a decision coordinate under a total
assignment: fixed decision variable plus fixed observed-parent projection. -/
def decisionInfosetOfAssignment (F : CausalContextFreeForm m)
    {p : Fin m} (d : DecisionNode F p) (a : TAssign F) : Infoset F p :=
  ⟨d, F.obsProjection a (F.obsParents d.val)⟩

@[simp] theorem decisionInfosetOfAssignment_eq_iff
    (F : CausalContextFreeForm m) {p : Fin m} (d : DecisionNode F p)
    (a b : TAssign F) :
    F.decisionInfosetOfAssignment d a = F.decisionInfosetOfAssignment d b ↔
      F.obsProjection a (F.obsParents d.val) =
        F.obsProjection b (F.obsParents d.val) := by
  simp [decisionInfosetOfAssignment]

instance (F : CausalContextFreeForm m) (p : Fin m) : Fintype (Infoset F p) :=
  Sigma.instFintype

instance (F : CausalContextFreeForm m) (p : Fin m) : DecidableEq (Infoset F p) :=
  inferInstanceAs
    (DecidableEq (Σ (d : DecisionNode F p), Cfg F (F.obsParents d.val)))

/-- Context-free behavioral strategy at causal decision information sets. -/
abbrev PlayerStrategy (F : CausalContextFreeForm m) (p : Fin m) :=
  (I : Infoset F p) → PMF (F.Val I.1.val)

/-- Joint behavioral policy for the seed profile used by the EFG unrolling API.
This is not part of the strategic game; it only picks distributions in the
existing bridge's tree-construction parameter. -/
abbrev Policy (F : CausalContextFreeForm m) :=
  (p : Fin m) → PlayerStrategy F p

/-- Forget the EFG-facing causal-context-free presentation into the existing
MAID structure.  This is a lossless structural translation. -/
def toMAIDStruct (F : CausalContextFreeForm m) :
    MAID.Struct (Fin m) F.nodeCount where
  kind := F.kind
  parents := F.parents
  obsParents := F.obsParents
  Val := F.Val
  instFintype := F.instFintype
  instDecidableEq := F.instDecidableEq
  instInhabited := F.instInhabited
  obs_sub := F.obs_sub
  obs_eq_nondec := F.obs_eq_nondec
  utility_unique := F.utility_unique
  acyclic := F.acyclic

/-- Forget the EFG-facing causal-context-free laws into MAID semantics. -/
def toMAIDSem (F : CausalContextFreeForm m) : MAID.Sem F.toMAIDStruct where
  chanceCPD := F.chanceCPD
  utilityFn := F.utilityFn

/-- Native kernel semantics of the causal-context-free form. -/
noncomputable def toKernelGame (F : CausalContextFreeForm m) :
    KernelGame (Fin m) :=
  MAID.toKernelGame F.toMAIDStruct F.toMAIDSem

/-- Unroll the causal variables as an EFG assignment tree along a topological
order. -/
noncomputable def toEFGAt (F : CausalContextFreeForm m)
    (seedPolicy : F.Policy) (order : MAID.TopologicalOrder F.toMAIDStruct) :
    EFG.EFGGame :=
  MAID_EFG.maidToEFGAt F.toMAIDStruct F.toMAIDSem seedPolicy order

/-- Unroll the causal variables as an EFG assignment tree using a classically
chosen topological order. -/
noncomputable def toEFG (F : CausalContextFreeForm m)
    (seedPolicy : F.Policy) : EFG.EFGGame :=
  MAID_EFG.maidToEFG F.toMAIDStruct F.toMAIDSem seedPolicy

/-- Kernel semantics of an explicitly unrolled causal-context-free EFG tree. -/
noncomputable def toEFGAtKernelGame (F : CausalContextFreeForm m)
    (seedPolicy : F.Policy) (order : MAID.TopologicalOrder F.toMAIDStruct) :
    KernelGame (Fin m) :=
  (F.toEFGAt seedPolicy order).toKernelGame

/-- The native causal semantics and the assignment-tree EFG semantics agree up
to the bridge's utility-distribution bisimulation. -/
noncomputable def toEFGAt_bisimulation (F : CausalContextFreeForm m)
    (seedPolicy : F.Policy) (order : MAID.TopologicalOrder F.toMAIDStruct) :
    KernelGame.Bisimulation F.toKernelGame
      (F.toEFGAtKernelGame seedPolicy order) :=
  MAID_EFG.maidToEFGAt_bisimulation F.toMAIDSem seedPolicy order

/-- View an existing MAID structure and semantics as a causal-context-free form.
This is the converse of `toMAIDStruct`/`toMAIDSem`, with no semantic loss. -/
def ofMAID {n : Nat} (S : MAID.Struct (Fin m) n) (sem : MAID.Sem S) :
    CausalContextFreeForm m where
  nodeCount := n
  kind := S.kind
  parents := S.parents
  obsParents := S.obsParents
  Val := S.Val
  instFintype := S.instFintype
  instDecidableEq := S.instDecidableEq
  instInhabited := S.instInhabited
  obs_sub := S.obs_sub
  obs_eq_nondec := S.obs_eq_nondec
  utility_unique := S.utility_unique
  acyclic := S.acyclic
  chanceCPD := sem.chanceCPD
  utilityFn := sem.utilityFn

@[simp] theorem ofMAID_toMAIDStruct {n : Nat}
    (S : MAID.Struct (Fin m) n) (sem : MAID.Sem S) :
    (ofMAID S sem).toMAIDStruct = S :=
  rfl

@[simp] theorem ofMAID_toMAIDSem {n : Nat}
    (S : MAID.Struct (Fin m) n) (sem : MAID.Sem S) :
    (ofMAID S sem).toMAIDSem = sem :=
  rfl

@[simp] theorem ofMAID_toEFGAt {n : Nat}
    (S : MAID.Struct (Fin m) n) (sem : MAID.Sem S) (pol : MAID.Policy S)
    (order : MAID.TopologicalOrder S) :
    (ofMAID S sem).toEFGAt pol order = MAID_EFG.maidToEFGAt S sem pol order :=
  rfl

end CausalContextFreeForm

/-- A concrete EFG presentation obtained by unrolling a causal-context-free form
along a specific topological order. -/
structure CausalContextFreeEFGPresentation (m : Nat) where
  form : CausalContextFreeForm m
  seedPolicy : form.Policy
  order : MAID.TopologicalOrder form.toMAIDStruct

namespace CausalContextFreeEFGPresentation

variable {m : Nat}

/-- The generated assignment-tree EFG. -/
noncomputable def toEFG (X : CausalContextFreeEFGPresentation m) : EFG.EFGGame :=
  X.form.toEFGAt X.seedPolicy X.order

/-- The generated assignment-tree EFG as a kernel game. -/
noncomputable def toKernelGame (X : CausalContextFreeEFGPresentation m) :
    KernelGame (Fin m) :=
  X.toEFG.toKernelGame

/-- Native causal-context-free kernel semantics. -/
noncomputable def toNativeKernelGame (X : CausalContextFreeEFGPresentation m) :
    KernelGame (Fin m) :=
  X.form.toKernelGame

/-- Native causal semantics and the generated assignment-tree EFG are
utility-distribution bisimilar. -/
noncomputable def toEFG_bisimulation (X : CausalContextFreeEFGPresentation m) :
    KernelGame.Bisimulation X.toNativeKernelGame X.toKernelGame :=
  X.form.toEFGAt_bisimulation X.seedPolicy X.order

end CausalContextFreeEFGPresentation

/-- Certificate that an arbitrary EFG is literally a causal context-free
assignment tree.

This is the intrinsic tree-shape predicate for the MAID fragment.  It says the
EFG presentation itself is the unrolling of fixed causal variables with fixed
action domains and information sets given by fixed observed-parent projections. -/
structure CausalContextFreeEFGTreeCertificate (G : EFG.EFGGame) where
  form : CausalContextFreeForm G.inf.n
  seedPolicy : form.Policy
  order : MAID.TopologicalOrder form.toMAIDStruct
  sameGame : form.toEFGAt seedPolicy order = G

/-- Predicate for EFG trees with causal context-free choices. -/
def IsCausalContextFreeEFGTree (G : EFG.EFGGame) : Prop :=
  Nonempty (CausalContextFreeEFGTreeCertificate G)

namespace CausalContextFreeEFGTreeCertificate

variable {G : EFG.EFGGame}

/-- Semantic utility-distribution equivalence for the generated tree named by
the certificate.  The `sameGame` field identifies that generated tree with the
ambient EFG presentation. -/
theorem generatedUtilityDistributionEquivalent
    (c : CausalContextFreeEFGTreeCertificate G) :
    UtilityDistributionEquivalent c.form.toKernelGame
      (c.form.toEFGAt c.seedPolicy c.order).toKernelGame :=
  ⟨c.form.toEFGAt_bisimulation c.seedPolicy c.order⟩

end CausalContextFreeEFGTreeCertificate

/-- Every explicitly unrolled causal-context-free form is a causal
context-free EFG tree. -/
theorem causalContextFree_toEFGAt_isCausalContextFreeEFGTree
    {m : Nat} (F : CausalContextFreeForm m) (pol : F.Policy)
    (order : MAID.TopologicalOrder F.toMAIDStruct) :
    IsCausalContextFreeEFGTree (F.toEFGAt pol order) :=
  ⟨{
    form := F
    seedPolicy := pol
    order := order
    sameGame := rfl
  }⟩

/-- Every MAID-to-EFG unrolling is a causal context-free EFG tree. -/
theorem maidToEFGAt_isCausalContextFreeEFGTree
    {m n : Nat} (S : MAID.Struct (Fin m) n)
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    (order : MAID.TopologicalOrder S) :
    IsCausalContextFreeEFGTree (MAID_EFG.maidToEFGAt S sem pol order) := by
  exact ⟨{
    form := CausalContextFreeForm.ofMAID S sem
    seedPolicy := pol
    order := order
    sameGame := rfl
  }⟩

/-- Every order-free MAID-to-EFG unrolling is a causal context-free EFG tree. -/
theorem maidToEFG_isCausalContextFreeEFGTree
    {m n : Nat} (S : MAID.Struct (Fin m) n)
    (sem : MAID.Sem S) (pol : MAID.Policy S) :
    IsCausalContextFreeEFGTree (MAID_EFG.maidToEFG S sem pol) := by
  unfold MAID_EFG.maidToEFG
  exact maidToEFGAt_isCausalContextFreeEFGTree S sem pol
    (Classical.choice (MAID.topologicalOrder_exists S))

/-- Exact tree characterization, unfolded around the explicit causal
context-free form. -/
theorem isCausalContextFreeEFGTree_iff (G : EFG.EFGGame) :
    IsCausalContextFreeEFGTree G ↔
      ∃ (F : CausalContextFreeForm G.inf.n) (pol : F.Policy)
        (order : MAID.TopologicalOrder F.toMAIDStruct),
        F.toEFGAt pol order = G := by
  constructor
  · intro h
    rcases h with ⟨c⟩
    exact ⟨c.form, c.seedPolicy, c.order, c.sameGame⟩
  · rintro ⟨F, pol, order, hG⟩
    exact ⟨{
      form := F
      seedPolicy := pol
      order := order
      sameGame := hG
    }⟩

end Expressiveness
end Languages
end GameTheory
