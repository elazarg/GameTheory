/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Sequential
import GameTheory.Languages.MAID.Prefix
import GameTheory.Languages.Bridges.MAID_EFG

/-!
# Finite Sequential Open Games as MAIDs

This bridge embeds a finite heterogeneous perfect-information sequential shape
into the repository's existing MAID language.  The first `n` nodes are
decisions, one per stage/agent, and the last `n` nodes are utility nodes.  Every
decision observes the complete preceding action history; every utility node
observes the complete realized path.

The finiteness constraints are inherited from `MAID.Struct`, whose node values
form finite Bayesian-network variables.  The open-game shape itself remains
defined for arbitrary action carriers.
-/

noncomputable section

namespace OpenGames.ShapeSeqDep.MAIDBridge

open GameTheory

variable {n : Nat}

/-- The MAID node corresponding to sequential decision `i`. -/
def decisionNode (i : Fin n) : Fin (n + n) :=
  Fin.castAdd n i

/-- The MAID utility node belonging to stage-agent `i`. -/
def utilityNode (i : Fin n) : Fin (n + n) :=
  Fin.natAdd n i

/-- Node kinds for the canonical agent-form sequential MAID. -/
def nodeKind (nd : Fin (n + n)) : MAID.NodeKind (Fin n) :=
  Fin.addCases (fun i => .decision i) (fun i => .utility i) nd

/-- Node-value types for the canonical agent-form sequential MAID. -/
def nodeVal (A : Fin n → Type) (nd : Fin (n + n)) : Type :=
  Fin.addCases (motive := fun _ => Type) (fun i => A i) (fun _ => Unit) nd

@[simp] theorem nodeVal_castAdd (A : Fin n → Type) (i : Fin n) :
    nodeVal A (Fin.castAdd n i) = A i := by
  exact Fin.addCases_left i

@[simp] theorem nodeVal_natAdd (A : Fin n → Type) (i : Fin n) :
    nodeVal A (Fin.natAdd n i) = Unit := by
  exact Fin.addCases_right i

/-- Causal and informational parents.  A decision sees all preceding
decisions; a utility sees all decisions. -/
def parentNodes (nd : Fin (n + n)) : Finset (Fin (n + n)) :=
  Fin.addCases
    (fun i => Finset.univ.filter fun p => p.val < i.val)
    (fun _ => Finset.univ.filter fun p => p.val < n)
    nd

theorem parentNodes_lt {a b : Fin (n + n)} (h : a ∈ parentNodes b) :
    a.val < b.val := by
  refine Fin.addCases (motive := fun b => a ∈ parentNodes b → a.val < b.val)
      ?_ ?_ b h
  · intro i hi
    simpa [parentNodes] using hi
  · intro i hi
    simp only [parentNodes, Fin.addCases_right, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi
    change a.val < n + i.val
    omega

theorem parentNodes_acyclic :
    Math.DAG.Acyclic (fun a b : Fin (n + n) => a ∈ parentNodes b) := by
  intro a haa
  have path_lt : ∀ {u v : Fin (n + n)},
      Relation.TransGen (fun x y => x ∈ parentNodes y) u v → u.val < v.val := by
    intro u v huv
    induction huv with
    | single h => exact parentNodes_lt h
    | tail _ h ih => exact Nat.lt_trans ih (parentNodes_lt h)
  exact (Nat.lt_irrefl a.val) (path_lt haa)

/-- The canonical perfect-information MAID underlying `ShapeSeqDep A` in
agent form. -/
def sequentialStruct (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] : MAID.Struct (Fin n) (n + n) where
  kind := nodeKind
  parents := parentNodes
  obsParents := parentNodes
  Val := nodeVal A
  instFintype := Fin.addCases (motive := fun nd => Fintype (nodeVal A nd))
    (fun i => by simpa only [nodeVal_castAdd] using (inferInstance : Fintype (A i)))
    (fun i => by simpa only [nodeVal_natAdd] using (inferInstance : Fintype Unit))
  instDecidableEq := Fin.addCases (motive := fun nd => DecidableEq (nodeVal A nd))
    (fun i => by simpa only [nodeVal_castAdd] using (inferInstance : DecidableEq (A i)))
    (fun i => by simpa only [nodeVal_natAdd] using (inferInstance : DecidableEq Unit))
  instInhabited := Fin.addCases (motive := fun nd => Inhabited (nodeVal A nd))
    (fun i => by simpa only [nodeVal_castAdd] using (inferInstance : Inhabited (A i)))
    (fun i => by simpa only [nodeVal_natAdd] using (inferInstance : Inhabited Unit))
  obs_sub := fun _ => Finset.Subset.rfl
  obs_eq_nondec := fun _ _ => rfl
  utility_unique := by
    intro nd p h
    refine Fin.addCases (motive := fun nd =>
        nodeKind nd = .utility p → Unique (nodeVal A nd)) ?_ ?_ nd h
    · intro i hi
      simp [nodeKind] at hi
    · intro i _
      simpa only [nodeVal_natAdd] using (inferInstance : Unique Unit)
  acyclic := parentNodes_acyclic

@[simp] theorem sequentialStruct_kind_decision (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (i : Fin n) :
    (sequentialStruct A).kind (decisionNode i) = .decision i := by
  simp [sequentialStruct, nodeKind, decisionNode]

@[simp] theorem sequentialStruct_kind_utility (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (i : Fin n) :
    (sequentialStruct A).kind (utilityNode i) = .utility i := by
  change nodeKind (Fin.natAdd n i) = .utility i
  exact Fin.addCases_right i

@[simp] theorem sequentialStruct_parents_decision (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (i : Fin n) :
    (sequentialStruct A).parents (decisionNode i) =
      Finset.univ.filter (fun p => p.val < i.val) := by
  change parentNodes (Fin.castAdd n i) = _
  exact Fin.addCases_left i

@[simp] theorem sequentialStruct_parents_utility (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (i : Fin n) :
    (sequentialStruct A).parents (utilityNode i) =
      Finset.univ.filter (fun p => p.val < n) := by
  change parentNodes (Fin.natAdd n i) = _
  exact Fin.addCases_right i

@[simp] theorem decisionNode_mem_parents_decision (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (i j : Fin n) :
    decisionNode j ∈ (sequentialStruct A).parents (decisionNode i) ↔
      j.val < i.val := by
  rw [sequentialStruct_parents_decision]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decisionNode,
    Fin.val_castAdd]

@[simp] theorem decisionNode_mem_parents_utility (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (i j : Fin n) :
    decisionNode j ∈ (sequentialStruct A).parents (utilityNode i) := by
  simp [decisionNode]

/-- There is exactly one decision node for each stage-agent. -/
theorem decisionNode_eq {A : Fin n → Type}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n)
    (d : MAID.DecisionNode (sequentialStruct A) p) :
    d.val = decisionNode p := by
  have hd : nodeKind d.val = .decision p := d.property
  refine Fin.addCases (motive := fun nd =>
      nodeKind nd = .decision p → nd = decisionNode p) ?_ ?_ d.val hd
  · intro i hi
    simp only [nodeKind, Fin.addCases_left] at hi
    injection hi with hip
    subst p
    rfl
  · intro i hi
    unfold nodeKind at hi
    rw [Fin.addCases_right] at hi
    cases hi

/-- The canonical decision-node witness for stage-agent `p`. -/
def decisionNodeFor (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n) :
    MAID.DecisionNode (sequentialStruct A) p :=
  ⟨decisionNode p, sequentialStruct_kind_decision A p⟩

/-- Read the sequential-history index represented by a parent of decision
`i`. -/
def parentStage (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (i : Fin n)
    (q : ↥((sequentialStruct A).parents (decisionNode i))) : Fin i.val :=
  ⟨q.val.val, by
    have hq := q.property
    change q.val ∈ parentNodes (Fin.castAdd n i) at hq
    unfold parentNodes at hq
    rw [Fin.addCases_left] at hq
    exact (Finset.mem_filter.mp hq).2⟩

/-- Embed a dependent prefix index as a parent node. -/
def priorParent (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (i : Fin n) (j : Fin i.val) :
    ↥((sequentialStruct A).parents (decisionNode i)) :=
  ⟨decisionNode (ShapeSeqDep.priorIndex i j), by
    rw [sequentialStruct_parents_decision]
    simp [decisionNode, ShapeSeqDep.priorIndex]⟩

@[simp] theorem parentStage_priorParent (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (i : Fin n) (j : Fin i.val) :
    parentStage A i (priorParent A i j) = j := by
  apply Fin.ext
  rfl

theorem priorParent_parentStage (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (i : Fin n)
    (q : ↥((sequentialStruct A).parents (decisionNode i))) :
    priorParent A i (parentStage A i q) = q := by
  apply Subtype.ext
  apply Fin.ext
  rfl

/-- The parent nodes of decision `i` are canonically equivalent to the
dependent prefix indices before `i`. -/
def parentIndexEquiv (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (i : Fin n) :
    ↥((sequentialStruct A).parents (decisionNode i)) ≃ Fin i.val where
  toFun := parentStage A i
  invFun := priorParent A i
  left_inv := priorParent_parentStage A i
  right_inv := parentStage_priorParent A i

/-- At a decision parent, the MAID node-value type is the corresponding
dependent action type. -/
theorem parentValueType_eq (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (i : Fin n)
    (q : ↥((sequentialStruct A).parents (decisionNode i))) :
    (sequentialStruct A).Val q.val =
      A (ShapeSeqDep.priorIndex i (parentStage A i q)) := by
  change nodeVal A q.val = _
  have hq : q.val = decisionNode
      (ShapeSeqDep.priorIndex i (parentStage A i q)) := by
    apply Fin.ext
    rfl
  rw [hq]
  exact nodeVal_castAdd A _

/-- A sequential history is exactly the information observed at its canonical
MAID decision node. -/
def cfgHistoryEquiv (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (i : Fin n) :
    MAID.Cfg (sequentialStruct A)
        ((sequentialStruct A).parents (decisionNode i)) ≃
      ShapeSeqDep.History A i :=
  Equiv.piCongr (parentIndexEquiv A i) fun q =>
    Equiv.cast (parentValueType_eq A i q)

/-- Forget the unique decision-node witness in an agent-form information set. -/
def infosetCfgEquiv (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n) :
    MAID.Infoset (sequentialStruct A) p ≃
      MAID.Cfg (sequentialStruct A)
        ((sequentialStruct A).parents (decisionNode p)) where
  toFun I := by
    rcases I with ⟨d, cfg⟩
    have hd : d = decisionNodeFor A p := by
      apply Subtype.ext
      exact decisionNode_eq p d
    subst d
    exact cfg
  invFun cfg := ⟨decisionNodeFor A p, cfg⟩
  left_inv I := by
    rcases I with ⟨d, cfg⟩
    have hd : d = decisionNodeFor A p := by
      apply Subtype.ext
      exact decisionNode_eq p d
    subst d
    rfl
  right_inv _ := rfl

/-- Information sets of stage-agent `p` are exactly its dependent action
histories. -/
def infosetHistoryEquiv (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n) :
    MAID.Infoset (sequentialStruct A) p ≃ ShapeSeqDep.History A p :=
  (infosetCfgEquiv A p).trans (cfgHistoryEquiv A p)

/-- The value chosen at any information set of stage-agent `p` has action
type `A p`. -/
theorem infosetValueType_eq (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n)
    (I : MAID.Infoset (sequentialStruct A) p) :
    (sequentialStruct A).Val I.1.val = A p := by
  change nodeVal A I.1.val = A p
  rw [decisionNode_eq p I.1]
  exact nodeVal_castAdd A p

/-- Pure MAID behavior for one stage-agent is exactly one contingent stage
plan. -/
def pureStageEquiv (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n) :
    MAID.PureStrategy (sequentialStruct A) p ≃
      (ShapeSeqDep.History A p → A p) :=
  Equiv.piCongr (infosetHistoryEquiv A p) fun I =>
    Equiv.cast (infosetValueType_eq A p I)

/-- Pure policies of the canonical MAID are exactly finite-horizon
open-game strategy profiles. -/
def purePolicyEquiv (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] :
    MAID.PurePolicy (sequentialStruct A) ≃ ShapeSeqDep.Strategy A :=
  Equiv.piCongrRight fun p => pureStageEquiv A p

/-- Encode an open-game contingent-plan profile as a pure MAID policy. -/
def toPurePolicy (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (σ : ShapeSeqDep.Strategy A) :
    MAID.PurePolicy (sequentialStruct A) :=
  (purePolicyEquiv A).symm σ

/-- Decode a pure MAID policy as an open-game contingent-plan profile. -/
def ofPurePolicy (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (π : MAID.PurePolicy (sequentialStruct A)) :
    ShapeSeqDep.Strategy A :=
  purePolicyEquiv A π

@[simp] theorem ofPurePolicy_toPurePolicy (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (σ : ShapeSeqDep.Strategy A) :
    ofPurePolicy A (toPurePolicy A σ) = σ :=
  (purePolicyEquiv A).apply_symm_apply σ

@[simp] theorem toPurePolicy_ofPurePolicy (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (π : MAID.PurePolicy (sequentialStruct A)) :
    toPurePolicy A (ofPurePolicy A π) = π :=
  (purePolicyEquiv A).symm_apply_apply π

/-! ## Assignments and utility semantics -/

/-- Read the decision path from a total MAID assignment. -/
def pathOfAssign (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)]
    (a : MAID.TAssign (sequentialStruct A)) : ∀ i, A i :=
  fun i => by
    have v := a (decisionNode i)
    simpa [sequentialStruct, decisionNode] using v

/-- Extend a dependent decision path by the unique values at utility nodes. -/
def assignOfPath (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (path : ∀ i, A i) :
    MAID.TAssign (sequentialStruct A) :=
  Fin.addCases (motive := fun nd => (sequentialStruct A).Val nd)
    (fun i => by simpa [sequentialStruct] using path i)
    (fun i => by
      change nodeVal A (Fin.natAdd n i)
      exact (Equiv.cast (nodeVal_natAdd A i)).symm ())

@[simp] theorem pathOfAssign_assignOfPath (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (path : ∀ i, A i) :
    pathOfAssign A (assignOfPath A path) = path := by
  funext i
  simp [pathOfAssign, assignOfPath, decisionNode]

@[simp] theorem assignOfPath_pathOfAssign (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (a : MAID.TAssign (sequentialStruct A)) :
    assignOfPath A (pathOfAssign A a) = a := by
  funext nd
  refine Fin.addCases (motive := fun nd =>
      assignOfPath A (pathOfAssign A a) nd = a nd) ?_ ?_ nd
  · intro i
    simp [assignOfPath, pathOfAssign, decisionNode]
  · intro i
    apply (Equiv.cast (nodeVal_natAdd A i)).injective
    exact Subsingleton.elim _ _

/-- Total MAID assignments carry exactly the sequential action path; utility
nodes add no data. -/
def assignPathEquiv (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] :
    MAID.TAssign (sequentialStruct A) ≃ (∀ i, A i) where
  toFun := pathOfAssign A
  invFun := assignOfPath A
  left_inv := assignOfPath_pathOfAssign A
  right_inv := pathOfAssign_assignOfPath A

/-- There is exactly one utility node for each stage-agent. -/
theorem utilityNode_eq {A : Fin n → Type}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n)
    (u : MAID.UtilityNode (sequentialStruct A) p) :
    u.val = utilityNode p := by
  have hu : nodeKind u.val = .utility p := u.property
  refine Fin.addCases (motive := fun nd =>
      nodeKind nd = .utility p → nd = utilityNode p) ?_ ?_ u.val hu
  · intro i hi
    unfold nodeKind at hi
    rw [Fin.addCases_left] at hi
    cases hi
  · intro i hi
    unfold nodeKind at hi
    rw [Fin.addCases_right] at hi
    injection hi with hip
    subst p
    rfl

/-- The canonical utility-node witness for stage-agent `p`. -/
def utilityNodeFor (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n) :
    MAID.UtilityNode (sequentialStruct A) p :=
  ⟨utilityNode p, sequentialStruct_kind_utility A p⟩

/-- Read the stage index represented by a parent of a utility node. -/
def utilityParentStage (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n)
    (q : ↥((sequentialStruct A).parents (utilityNode p))) : Fin n :=
  ⟨q.val.val, by
    have hq := q.property
    change q.val ∈ parentNodes (Fin.natAdd n p) at hq
    unfold parentNodes at hq
    rw [Fin.addCases_right] at hq
    exact (Finset.mem_filter.mp hq).2⟩

/-- Embed a stage as a utility-parent node. -/
def utilityParent (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p i : Fin n) :
    ↥((sequentialStruct A).parents (utilityNode p)) :=
  ⟨decisionNode i, decisionNode_mem_parents_utility A p i⟩

@[simp] theorem utilityParentStage_utilityParent (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p i : Fin n) :
    utilityParentStage A p (utilityParent A p i) = i := by
  apply Fin.ext
  rfl

theorem utilityParent_utilityParentStage (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n)
    (q : ↥((sequentialStruct A).parents (utilityNode p))) :
    utilityParent A p (utilityParentStage A p q) = q := by
  apply Subtype.ext
  apply Fin.ext
  rfl

def utilityParentEquiv (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n) :
    ↥((sequentialStruct A).parents (utilityNode p)) ≃ Fin n where
  toFun := utilityParentStage A p
  invFun := utilityParent A p
  left_inv := utilityParent_utilityParentStage A p
  right_inv := utilityParentStage_utilityParent A p

theorem utilityParentValueType_eq (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n)
    (q : ↥((sequentialStruct A).parents (utilityNode p))) :
    (sequentialStruct A).Val q.val = A (utilityParentStage A p q) := by
  change nodeVal A q.val = _
  have hq : q.val = decisionNode (utilityParentStage A p q) := by
    apply Fin.ext
    rfl
  rw [hq]
  exact nodeVal_castAdd A _

/-- A utility-node parent configuration is exactly a complete action path. -/
def utilityCfgPathEquiv (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n) :
    MAID.Cfg (sequentialStruct A)
        ((sequentialStruct A).parents (utilityNode p)) ≃
      (∀ i, A i) :=
  Equiv.piCongr (utilityParentEquiv A p) fun q =>
    Equiv.cast (utilityParentValueType_eq A p q)

/-- Read a complete dependent action path directly from a utility-node parent
configuration.  This is the computational projection underlying
`utilityCfgPathEquiv`. -/
def pathOfUtilityCfg (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n)
    (cfg : MAID.Cfg (sequentialStruct A)
      ((sequentialStruct A).parents (utilityNode p))) : ∀ i, A i :=
  fun i => by
    have v := cfg (utilityParent A p i)
    simpa [sequentialStruct, utilityParent, decisionNode] using v

/-- The canonical MAID semantics for a sequential payoff continuation.  It
has no chance nodes and one utility node per stage-agent. -/
def sequentialSem (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (k : (∀ i, A i) → Fin n → ℝ) :
    MAID.Sem (sequentialStruct A) where
  chanceCPD c := by
    have hc : nodeKind c.val = .chance := c.property
    refine Fin.addCases (motive := fun nd =>
        nodeKind nd = .chance →
          MAID.Cfg (sequentialStruct A)
            ((sequentialStruct A).parents nd) →
          PMF ((sequentialStruct A).Val nd)) ?_ ?_ c.val hc
    · intro i hi
      unfold nodeKind at hi
      rw [Fin.addCases_left] at hi
      cases hi
    · intro i hi
      unfold nodeKind at hi
      rw [Fin.addCases_right] at hi
      cases hi
  utilityFn p u cfg := by
    have hu : u = utilityNodeFor A p := by
      apply Subtype.ext
      exact utilityNode_eq p u
    subst u
    exact k (pathOfUtilityCfg A p cfg) p

theorem pathOfUtilityCfg_projCfg (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (p : Fin n)
    (a : MAID.TAssign (sequentialStruct A)) :
    pathOfUtilityCfg A p
        (MAID.projCfg a ((sequentialStruct A).parents (utilityNode p))) =
      pathOfAssign A a := by
  funext i
  simp only [pathOfUtilityCfg, MAID.projCfg, eq_mp_eq_cast, pathOfAssign]
  apply eq_of_heq
  rfl

/-- The MAID utility semantics reads exactly the open-game continuation from
the decision coordinates of an assignment. -/
theorem utilityOf_eq (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (k : (∀ i, A i) → Fin n → ℝ)
    (a : MAID.TAssign (sequentialStruct A)) (p : Fin n) :
    MAID.utilityOf (sequentialStruct A) (sequentialSem A k) a p =
      k (pathOfAssign A a) p := by
  have huniv :
      (Finset.univ : Finset (MAID.UtilityNode (sequentialStruct A) p)) =
        {utilityNodeFor A p} := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    exact utilityNode_eq p u
  rw [MAID.utilityOf, huniv, Finset.sum_singleton]
  change k (pathOfUtilityCfg A p
      (MAID.projCfg a ((sequentialStruct A).parents (utilityNode p)))) p = _
  rw [pathOfUtilityCfg_projCfg]

@[simp] theorem utilityOf_assignOfPath (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (k : (∀ i, A i) → Fin n → ℝ)
    (path : ∀ i, A i) (p : Fin n) :
    MAID.utilityOf (sequentialStruct A) (sequentialSem A k)
        (assignOfPath A path) p = k path p := by
  rw [utilityOf_eq, pathOfAssign_assignOfPath]

/-- Node indices themselves give a topological order for the canonical
sequential MAID. -/
theorem sequentialStruct_naturalOrder (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] :
    (sequentialStruct A).NaturalOrder := by
  intro nd p hp
  exact parentNodes_lt hp

/-- The canonical sequential MAID has perfect recall.  In agent form every
player owns exactly one decision node, so both recall clauses are immediate. -/
theorem sequentialStruct_perfectRecall (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] :
    (sequentialStruct A).PerfectRecall := by
  constructor
  · intro p d₁ d₂ hd₁ hd₂ hne
    let D₁ : MAID.DecisionNode (sequentialStruct A) p := ⟨d₁, hd₁⟩
    let D₂ : MAID.DecisionNode (sequentialStruct A) p := ⟨d₂, hd₂⟩
    have h₁ := decisionNode_eq p D₁
    have h₂ := decisionNode_eq p D₂
    exact absurd (h₁.trans h₂.symm) hne
  · intro p d₁ d₂ hd₁ hd₂ _hancestor
    let D₁ : MAID.DecisionNode (sequentialStruct A) p := ⟨d₁, hd₁⟩
    let D₂ : MAID.DecisionNode (sequentialStruct A) p := ⟨d₂, hd₂⟩
    have h₁ := decisionNode_eq p D₁
    have h₂ := decisionNode_eq p D₂
    change d₁ = decisionNode p at h₁
    change d₂ = decisionNode p at h₂
    rw [h₁, h₂] at _hancestor
    exact absurd _hancestor
      ((sequentialStruct A).isAncestor_irrefl (decisionNode p))

/-! ## Reuse of the existing MAID-to-EFG bridge -/

/-- The EFG obtained by passing the canonical sequential MAID through the
repository's general MAID-to-EFG translation.  The seed policy is semantically
irrelevant to that translation; the existing bridge proves this internally. -/
def toEFG (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (k : (∀ i, A i) → Fin n → ℝ) : EFG.EFGGame :=
  MAID_EFG.maidToEFG (sequentialStruct A) (sequentialSem A k)
    (MAID.defaultPolicy (sequentialStruct A))

/-- The general MAID-to-EFG compiler supplies a game bisimulation for the
canonical sequential presentation. -/
def toEFGBisimulation (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (k : (∀ i, A i) → Fin n → ℝ) :
    GameTheory.KernelGame.Bisimulation
      (MAID.toKernelGame (sequentialStruct A) (sequentialSem A k))
      ((toEFG A k).toKernelGame) :=
  MAID_EFG.maidToEFG_bisimulation (sequentialSem A k)
    (MAID.defaultPolicy (sequentialStruct A))

/-- The induced extensive-form game has perfect recall. -/
theorem toEFG_perfectRecall (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (k : (∀ i, A i) → Fin n → ℝ) :
    EFG.PerfectRecall (toEFG A k).tree :=
  MAID_EFG.maidToEFG_perfectRecall (sequentialStruct_perfectRecall A)
    (sequentialSem A k) (MAID.defaultPolicy (sequentialStruct A))

end OpenGames.ShapeSeqDep.MAIDBridge
