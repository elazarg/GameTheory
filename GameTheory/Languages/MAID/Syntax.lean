import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.Finset.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Order.RelClasses

import GameTheory.Core.KernelGame
import Math.DAG

/-!
# Multi-Agent Influence Diagrams (MAID)

A MAID (Koller & Milch 2003) is a directed acyclic graph with three kinds of
nodes — chance, decision, utility — together with conditional probability
distributions for chance nodes and utility functions for utility nodes.

The DAG structure (parent sets) is fundamental; the joint distribution over
assignments is defined as the standard Bayesian network factorization
`P(x) = ∏ᵢ P(xᵢ | parents(xᵢ))`, which is manifestly order-independent.
Fold-based evaluation (`evalStep`, `evalFold`) lives in `FoldEval.lean` for
use by the EFG bridge; the core module here is order-free.

## Outline
- Core: `NodeKind`, `Struct`, typed assignments
- Topological orders: `TopologicalOrder`
- Semantics: `Sem`, strategies, `assignProb`, `evalAssignDist`
- `bayesian_marginal_fold`: Bayesian product invariant (used internally and by `FoldEval`)
- Game: `KernelGame` bridge
-/

namespace MAID

-- ============================================================================
-- Core — pure DAG structure
-- ============================================================================

/-- The kind of a node in a MAID. -/
inductive NodeKind (Player : Type) where
  | chance
  | decision (agent : Player)
  | utility (agent : Player)
deriving DecidableEq, Repr

/-- A MAID structure: a DAG with typed nodes over `Fin n`.

The structure is defined by node kinds, parent relations, and domain sizes.
Acyclicity is stated as irreflexivity of the transitive closure of the parent
relation — the standard definition of "directed acyclic graph". -/
structure Struct (Player : Type) [DecidableEq Player] [Fintype Player]
    (n : Nat) where
  kind : Fin n → NodeKind Player
  parents    : Fin n → Finset (Fin n)
  obsParents : Fin n → Finset (Fin n)
  Val : Fin n → Type
  instFintype : ∀ nd, Fintype (Val nd)
  instDecidableEq : ∀ nd, DecidableEq (Val nd)
  instInhabited : ∀ nd, Inhabited (Val nd)
  -- Invariants
  obs_sub        : ∀ nd, obsParents nd ⊆ parents nd
  obs_eq_nondec  : ∀ nd, (¬ ∃ a, kind nd = .decision a) → obsParents nd = parents nd
  utility_unique : ∀ nd a, kind nd = .utility a → Unique (Val nd)
  acyclic        : DAG.Acyclic (· ∈ parents ·)

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

instance (S : Struct Player n) (nd : Fin n) : Fintype (S.Val nd) := S.instFintype nd
instance (S : Struct Player n) (nd : Fin n) : DecidableEq (S.Val nd) := S.instDecidableEq nd
instance (S : Struct Player n) (nd : Fin n) : Inhabited (S.Val nd) := S.instInhabited nd

/-- Node `a` is an ancestor of node `b` in the DAG: there is a directed path
from `a` to `b` through the parent relation. -/
def Struct.IsAncestor (S : Struct Player n) (a b : Fin n) : Prop :=
  Relation.TransGen (· ∈ S.parents ·) a b

/-- `IsAncestor` is irreflexive (no node is its own ancestor). -/
theorem Struct.isAncestor_irrefl (S : Struct Player n) (nd : Fin n) :
    ¬ S.IsAncestor nd nd :=
  S.acyclic nd

/-- If `a` is a parent of `b`, then `a` is an ancestor of `b`. -/
theorem Struct.parent_isAncestor (S : Struct Player n) {a b : Fin n}
    (h : a ∈ S.parents b) : S.IsAncestor a b :=
  Relation.TransGen.single h

/-- Ancestry is transitive. -/
theorem Struct.isAncestor_trans (S : Struct Player n) {a b c : Fin n}
    (hab : S.IsAncestor a b) (hbc : S.IsAncestor b c) : S.IsAncestor a c :=
  Relation.TransGen.trans hab hbc

-- ============================================================================
-- Topological orders
-- ============================================================================

/-- A topological order for a MAID: a permutation of all nodes that respects the
parent relation (every parent appears before its child). -/
abbrev TopologicalOrder (S : Struct Player n) := DAG.TopologicalOrder S.parents

/-- Acyclicity guarantees at least one topological order exists. -/
theorem topologicalOrder_exists (S : Struct Player n) :
    Nonempty (TopologicalOrder S) :=
  DAG.topologicalOrder_of_acyclic S.acyclic

-- ============================================================================
-- Node subtypes and assignments
-- ============================================================================

/-- Chance node subtype. -/
abbrev ChanceNode (S : Struct Player n) := {nd : Fin n // S.kind nd = .chance}

/-- Decision node subtype for a given player. -/
abbrev DecisionNode (S : Struct Player n) (p : Player) :=
  {nd : Fin n // S.kind nd = .decision p}

/-- Utility node subtype for a given player. -/
abbrev UtilityNode (S : Struct Player n) (p : Player) :=
  {nd : Fin n // S.kind nd = .utility p}

/-- Configuration: values at a subset of nodes. -/
abbrev Cfg (S : Struct Player n) (ps : Finset (Fin n)) :=
  (nd : ↥ps) → S.Val nd.val

/-- Total assignment: a value at every node. -/
abbrev TAssign (S : Struct Player n) := ∀ nd : Fin n, S.Val nd

/-- Project a total assignment to a configuration on a subset. -/
def projCfg {S : Struct Player n} (a : TAssign S) (ps : Finset (Fin n)) :
    Cfg S ps :=
  fun nd => a nd.val

/-- Default assignment: the default value at every node. -/
def defaultAssign (S : Struct Player n) : TAssign S :=
  fun _ => default

-- ============================================================================
-- Derived domain-size API (for bridges to Fin-based representations like EFG)
-- ============================================================================

/-- Domain size derived from Val's Fintype instance. -/
def Struct.domainSize (S : Struct Player n) (nd : Fin n) : Nat :=
  Fintype.card (S.Val nd)

/-- Every node has positive domain size. -/
theorem Struct.dom_pos (S : Struct Player n) (nd : Fin n) :
    0 < S.domainSize nd :=
  Fintype.card_pos

/-- Utility nodes have domain size 1. -/
theorem Struct.utility_domain (S : Struct Player n) (nd : Fin n) (a : Player)
    (h : S.kind nd = .utility a) : S.domainSize nd = 1 := by
  have := S.utility_unique nd a h
  exact Fintype.card_unique

/-- Equivalence between node values and `Fin (domainSize nd)`. -/
noncomputable def Struct.valEquiv (S : Struct Player n) (nd : Fin n) :
    S.Val nd ≃ Fin (S.domainSize nd) :=
  Fintype.equivFin (S.Val nd)

-- Fintype instances for node subtypes
instance (S : Struct Player n) : Fintype (ChanceNode S) :=
  Subtype.fintype _

instance (S : Struct Player n) (p : Player) : Fintype (DecisionNode S p) :=
  Subtype.fintype _

instance (S : Struct Player n) (p : Player) : Fintype (UtilityNode S p) :=
  Subtype.fintype _

instance (S : Struct Player n) : DecidableEq (ChanceNode S) :=
  inferInstanceAs (DecidableEq {nd : Fin n // S.kind nd = .chance})

instance (S : Struct Player n) (p : Player) : DecidableEq (DecisionNode S p) :=
  inferInstanceAs (DecidableEq {nd : Fin n // S.kind nd = .decision p})

instance (S : Struct Player n) (p : Player) : DecidableEq (UtilityNode S p) :=
  inferInstanceAs (DecidableEq {nd : Fin n // S.kind nd = .utility p})

instance (S : Struct Player n) (ps : Finset (Fin n)) : Fintype (Cfg S ps) :=
  inferInstance

instance (S : Struct Player n) (ps : Finset (Fin n)) : DecidableEq (Cfg S ps) :=
  inferInstanceAs (DecidableEq ((nd : ↥ps) → S.Val nd.val))

/-- Info set: which decision node + observed parent configuration. -/
def Infoset (S : Struct Player n) (p : Player) :=
  Σ (d : DecisionNode S p), Cfg S (S.obsParents d.val)

instance (S : Struct Player n) (p : Player) : Fintype (Infoset S p) :=
  Sigma.instFintype

instance (S : Struct Player n) (p : Player) : DecidableEq (Infoset S p) :=
  inferInstanceAs (DecidableEq (Σ (d : DecisionNode S p), Cfg S (S.obsParents d.val)))

-- ============================================================================
-- Perfect recall — defined on DAG ancestry
-- ============================================================================

/-- Perfect recall for a MAID, following Koller & Milgrom:

1. **Temporal ordering**: for each player, any two decision nodes are comparable
   by DAG ancestry (one is an ancestor of the other).
2. **Full observation**: if `d₁` is an ancestor of `d₂` (both owned by the same
   player), then `d₂` observes `d₁` and all of `d₁`'s observed parents.

Condition (1) ensures that a player's decision nodes form a directed path in the
DAG. Together with (2), this gives the standard perfect recall property: a player
remembers all previous observations and actions. -/
def Struct.PerfectRecall (S : Struct Player n) : Prop :=
  (∀ (p : Player) (d₁ d₂ : Fin n),
    S.kind d₁ = .decision p → S.kind d₂ = .decision p → d₁ ≠ d₂ →
    S.IsAncestor d₁ d₂ ∨ S.IsAncestor d₂ d₁) ∧
  (∀ (p : Player) (d₁ d₂ : Fin n),
    S.kind d₁ = .decision p → S.kind d₂ = .decision p →
    S.IsAncestor d₁ d₂ →
    d₁ ∈ S.obsParents d₂ ∧ S.obsParents d₁ ⊆ S.obsParents d₂)

-- ============================================================================
-- Semantics — evaluation
-- ============================================================================

/-- Semantic data for a MAID: chance CPDs and utility functions. -/
structure Sem (S : Struct Player n) where
  chanceCPD : (c : ChanceNode S) → Cfg S (S.parents c.val) → PMF (S.Val c.val)
  utilityFn : (p : Player) → (u : UtilityNode S p) → Cfg S (S.parents u.val) → ℝ

/-- Per-player strategy: maps each info set to a distribution over actions. -/
def PlayerStrategy (S : Struct Player n) (p : Player) :=
  (I : Infoset S p) → PMF (S.Val I.1.val)

/-- Joint policy: a strategy for every player. -/
def Policy (S : Struct Player n) := (p : Player) → PlayerStrategy S p

/-- Distribution at a single node, given the current total assignment.
    Dispatches by node kind using `match` on `S.kind nd`. -/
noncomputable def nodeDist (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (nd : Fin n) (a : TAssign S) : PMF (S.Val nd) :=
  match hk : S.kind nd with
  | .chance => sem.chanceCPD ⟨nd, hk⟩ (projCfg a (S.parents nd))
  | .decision p => pol p ⟨⟨nd, hk⟩, projCfg a (S.obsParents nd)⟩
  | .utility _ => PMF.pure default

/-- Update a total assignment at node `nd` with value `v`. -/
def updateAssign {S : Struct Player n} (a : TAssign S) (nd : Fin n) (v : S.Val nd) :
    TAssign S :=
  fun nd' => if h : nd' = nd then h ▸ v else a nd'

-- ============================================================================
-- Bayesian network factorization (order-free)
-- ============================================================================

/-- Probability of a total assignment: product of conditional probabilities at
each node. This is the standard Bayesian network factorization formula
`P(x₁,…,xₙ) = ∏ᵢ P(xᵢ | parents(xᵢ))`, which is manifestly independent of
any node ordering. -/
noncomputable def assignProb (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (a : TAssign S) : ENNReal :=
  ∏ nd : Fin n, (nodeDist S sem pol nd a) (a nd)

-- ============================================================================
-- Bayesian network marginal — private infrastructure
-- ============================================================================

/-- No node is its own parent (from acyclicity). -/
private theorem Struct.self_not_parent (S : Struct Player n) (nd : Fin n) :
    nd ∉ S.parents nd :=
  fun h => S.acyclic nd (Relation.TransGen.single h)

/-- In a topological order, a later node cannot be a parent of an earlier node. -/
private theorem topo_later_not_parent {S : Struct Player n}
    (σ : DAG.TopologicalOrder S.parents) {i k : Fin σ.order.length}
    (hik : i.val < k.val) :
    σ.order[k] ∉ S.parents σ.order[i] := by
  intro hp
  have hki := σ.ancestor_lt (Relation.TransGen.single hp) rfl rfl
  omega

/-- Updating at a node not in `ps` doesn't change a projection onto `ps`. -/
private theorem projCfg_update_irrel' {S : Struct Player n} (a : TAssign S)
    (nd : Fin n) (v : S.Val nd) (ps : Finset (Fin n)) (hnd : nd ∉ ps) :
    projCfg (updateAssign a nd v) ps = projCfg a ps := by
  ext ⟨nd', hnd'⟩
  simp only [projCfg, updateAssign]
  split
  · next h => exact absurd (h ▸ hnd') hnd
  · rfl

/-- `nodeDist` at `nd₂` is unchanged when we update at `nd₁`, provided `nd₁ ∉ S.parents nd₂`. -/
private theorem nodeDist_update_irrel' {S : Struct Player n} (sem : Sem S) (pol : Policy S)
    (nd₁ nd₂ : Fin n) (a : TAssign S) (v : S.Val nd₁)
    (h : nd₁ ∉ S.parents nd₂) :
    nodeDist S sem pol nd₂ (updateAssign a nd₁ v) = nodeDist S sem pol nd₂ a := by
  unfold nodeDist
  split
  · congr 1; exact projCfg_update_irrel' a nd₁ v _ h
  · congr 1; exact Sigma.ext rfl (heq_of_eq (projCfg_update_irrel' a nd₁ v _
      (fun hmem => h (S.obs_sub nd₂ hmem))))
  · rfl

/-- Fold invariant: after processing nodes `L` (a prefix of a topological order
starting from `defaultAssign`), the PMF at assignment `a` equals the product of
conditionals on `L` times an indicator that `a` agrees with `defaultAssign`
off `L`. -/
private theorem foldl_evalStep_invariant {S : Struct Player n}
    (sem : Sem S) (pol : Policy S)
    (L : List (Fin n)) (hnodup : L.Nodup)
    (htopo : ∀ (i : Fin L.length), ∀ p ∈ S.parents L[i],
      ∃ j : Fin L.length, j.val < i.val ∧ L[j] = p)
    (a : TAssign S) :
    (L.foldl (fun acc nd => acc.bind (fun a' =>
      (nodeDist S sem pol nd a').bind (fun v =>
        PMF.pure (updateAssign a' nd v))))
      (PMF.pure (defaultAssign S))) a =
    (L.toFinset.prod fun nd => (nodeDist S sem pol nd a) (a nd)) *
      (if ∀ nd, ¬ nd ∈ L → a nd = (defaultAssign S) nd then 1 else 0) := by
  induction L using List.reverseRecOn generalizing a with
  | nil =>
    simp only [List.foldl_nil, List.toFinset_nil, Finset.prod_empty, one_mul, PMF.pure_apply,
      List.not_mem_nil, not_false_eq_true, forall_true_left, funext_iff]
  | append_singleton L nd ih =>
    -- Extract nodup and topo hypotheses for L from (L ++ [nd])
    have hnodup_L : L.Nodup := by
      rw [List.nodup_append] at hnodup; exact hnodup.1
    have hnd_notin : nd ∉ L := by
      rw [List.nodup_append] at hnodup
      intro h; exact hnodup.2.2 nd h nd (List.mem_singleton.mpr rfl) rfl
    -- Helper: convert Fin-indexed getElem on (L ++ [nd]) to L or nd
    -- We use `show` to convert Fin-indexed to Nat-indexed getElem
    have getAppL' (j : Fin (L ++ [nd]).length) (hj : j.val < L.length) :
        (L ++ [nd])[j] = L[j.val]'hj := by
      change (L ++ [nd])[j.val]'j.isLt = L[j.val]'hj
      exact List.getElem_append_left hj
    have getAppNd' (j : Fin (L ++ [nd]).length) (hj : j.val = L.length) :
        (L ++ [nd])[j] = nd := by
      change (L ++ [nd])[j.val]'j.isLt = nd
      simp [hj]
    -- Parents of nd are all in L (from htopo at the last index)
    have hnd_parents_in_L : ∀ p ∈ S.parents nd, p ∈ L := by
      intro p hp
      have hlen : L.length < (L ++ [nd]).length := by simp
      let idx : Fin (L ++ [nd]).length := ⟨L.length, hlen⟩
      have hnd_get : (L ++ [nd])[idx] = nd := getAppNd' idx rfl
      have hp' : p ∈ S.parents (L ++ [nd])[idx] := hnd_get.symm ▸ hp
      obtain ⟨j, hj_lt, hj_eq⟩ := htopo idx p hp'
      have hj_lt_L : j.val < L.length := by omega
      rw [getAppL' j hj_lt_L] at hj_eq
      exact hj_eq ▸ List.getElem_mem ..
    -- Extract topo hypothesis for L
    have htopo_L : ∀ (i : Fin L.length), ∀ p ∈ S.parents L[i],
        ∃ j : Fin L.length, j.val < i.val ∧ L[j] = p := by
      intro i p hp
      have hi' : i.val < (L ++ [nd]).length := by have := i.isLt; simp
      let idx : Fin (L ++ [nd]).length := ⟨i.val, hi'⟩
      have hi_get : (L ++ [nd])[idx] = L[i] := getAppL' idx i.isLt
      have hp' : p ∈ S.parents (L ++ [nd])[idx] := hi_get.symm ▸ hp
      obtain ⟨j, hj_lt, hj_eq⟩ := htopo idx p hp'
      have hj_lt_L : j.val < L.length := by
        by_contra hc; push Not at hc
        have hj_len : j.val = L.length := by have := j.isLt; simp at this; omega
        rw [getAppNd' j hj_len] at hj_eq; subst hj_eq
        have hi_lt := i.isLt; change j.val < i.val at hj_lt; omega
      refine ⟨⟨j.val, hj_lt_L⟩, by omega, ?_⟩
      rw [getAppL' j hj_lt_L] at hj_eq; exact hj_eq
    -- Apply IH
    have ih_applied := ih hnodup_L htopo_L
    -- Rewrite foldl on L ++ [nd]
    rw [List.foldl_concat]
    -- Abbreviate the accumulated PMF
    set μ := L.foldl (fun acc nd => acc.bind (fun a' =>
      (nodeDist S sem pol nd a').bind (fun v =>
        PMF.pure (updateAssign a' nd v))))
      (PMF.pure (defaultAssign S)) with hμ_def
    -- Expand bind/pure
    simp only [PMF.bind_apply, PMF.pure_apply]
    -- Goal: ∑' a_1, μ a_1 * ∑' a_2, (nodeDist nd a_1) a_2 * [a = updateAssign a_1 nd a_2] = RHS
    -- Substitute IH into the outer tsum
    simp_rw [ih_applied]
    -- Now goal involves:
    --   ∑' a_1, (∏ ... * [a_1 agrees with default off L]) *
    --           ∑' a_2, (nodeDist nd a_1) a_2 * [a = updateAssign a_1 nd a_2]
    -- = (∏ ... over L ∪ {nd}) * [a agrees with default off L ∪ {nd}]
    --
    -- Step 1: Characterize when a = updateAssign a_1 nd a_2
    -- This holds iff a_2 = a nd and a_1 nd' = a nd' for all nd' ≠ nd
    have hupdate_iff : ∀ (a_1 : TAssign S) (a_2 : S.Val nd),
        (a = updateAssign a_1 nd a_2) ↔ (a_2 = a nd ∧ ∀ nd', nd' ≠ nd → a_1 nd' = a nd') := by
      intro a_1 a_2; constructor
      · intro h; constructor
        · have := congr_fun h nd; simp [updateAssign] at this; exact this.symm
        · intro nd' hne
          have := congr_fun h nd'; simp [updateAssign, hne] at this; exact this.symm
      · intro ⟨h1, h2⟩; funext nd'; simp only [updateAssign]; split
        · next h => subst h; exact h1.symm
        · next h => exact (h2 nd' h).symm
    simp_rw [hupdate_iff]
    -- Step 2: Factor the inner tsum: split [a_2 = a nd ∧ cond] into [a_2 = a nd] * [cond]
    -- Then collapse the a_2 sum
    have inner_simp : ∀ (a_1 : TAssign S),
        (∑' (a_2 : S.Val nd), (nodeDist S sem pol nd a_1) a_2 *
          if a_2 = a nd ∧ ∀ nd', nd' ≠ nd → a_1 nd' = a nd' then 1 else 0) =
        (nodeDist S sem pol nd a_1) (a nd) *
          if ∀ nd', nd' ≠ nd → a_1 nd' = a nd' then 1 else 0 := by
      intro a_1
      by_cases hcond : ∀ nd', nd' ≠ nd → a_1 nd' = a nd'
      · have hsimp : ∀ a_2,
            (if a_2 = a nd ∧ ∀ nd', nd' ≠ nd → a_1 nd' = a nd'
              then (1 : ENNReal) else 0) =
            if a_2 = a nd then 1 else 0 := by
          intro a_2; congr 1; simp only [eq_true hcond, and_true]
        simp_rw [hsimp, mul_ite, mul_one, mul_zero]
        rw [tsum_eq_single (a nd) (fun b hb => by simp [hb]), if_pos rfl, if_pos hcond]
      · have hsimp : ∀ a_2,
            (if a_2 = a nd ∧ ∀ nd', nd' ≠ nd → a_1 nd' = a nd'
              then (1 : ENNReal) else 0) = 0 := by
          intro a_2; rw [if_neg]; exact fun ⟨_, h⟩ => hcond h
        simp_rw [hsimp, mul_zero, tsum_zero, if_neg hcond, mul_zero]
    simp_rw [inner_simp]
    -- Step 3: Case-split on whether `a` agrees with default off L ++ [nd]
    -- This determines whether both sides are 0 or both equal the product.
    --
    -- Key observation: the two indicators in the LHS summand combine to pin down a_1
    -- uniquely (when both are 1). We show the tsum has at most one nonzero term.
    --
    -- Define the unique candidate a₀
    let a₀ : TAssign S := updateAssign a nd (defaultAssign S nd)
    -- Show a₀ satisfies both conditions iff a agrees with default off L ++ [nd]
    have ha₀_cond2 : ∀ nd', nd' ≠ nd → a₀ nd' = a nd' := by
      intro nd' hne; simp [a₀, updateAssign, hne]
    have ha₀_self : a₀ nd = defaultAssign S nd := by simp [a₀, updateAssign]
    have ha₀_cond1_iff : (∀ nd' ∉ L, a₀ nd' = defaultAssign S nd') ↔
        ∀ nd' ∉ L ++ [nd], a nd' = defaultAssign S nd' := by
      constructor
      · intro h nd' hnd'
        have hnd'' : nd' ∉ L ∧ nd' ≠ nd :=
          ⟨fun h => hnd' (List.mem_append.mpr (Or.inl h)),
           fun h => hnd' (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr h)))⟩
        rw [← ha₀_cond2 nd' hnd''.2]; exact h nd' hnd''.1
      · intro h nd' hnd'
        by_cases hne : nd' = nd
        · subst hne; exact ha₀_self
        · rw [ha₀_cond2 nd' hne]
          exact h nd' (by simp [List.mem_append, hnd', hne])
    -- Any a_1 ≠ a₀ contributes 0
    have hzero : ∀ (a_1 : TAssign S), a_1 ≠ a₀ →
        ((∏ nd' ∈ L.toFinset, (nodeDist S sem pol nd' a_1) (a_1 nd')) *
          if ∀ nd' ∉ L, a_1 nd' = defaultAssign S nd' then 1 else 0) *
        ((nodeDist S sem pol nd a_1) (a nd) *
          if ∀ nd', nd' ≠ nd → a_1 nd' = a nd' then 1 else 0) = 0 := by
      intro a_1 hne
      by_cases h1 : ∀ nd' ∉ L, a_1 nd' = defaultAssign S nd'
      · by_cases h2 : ∀ nd', nd' ≠ nd → a_1 nd' = a nd'
        · exfalso; apply hne; funext nd'
          by_cases hnd' : nd' = nd
          · subst hnd'; exact (h1 _ hnd_notin).trans ha₀_self.symm
          · exact (h2 nd' hnd').trans (ha₀_cond2 nd' hnd').symm
        · simp [if_neg h2]
      · simp [if_neg h1]
    rw [tsum_eq_single a₀ hzero]
    -- Evaluate at a₀: simplify the cond2 indicator
    rw [if_pos ha₀_cond2]
    -- Now the LHS has: (∏ nd' ∈ L.toFinset, (nodeDist nd' a₀) (a₀ nd')) *
    --                   [∀ nd' ∉ L, a₀ nd' = default] * (nodeDist nd a₀) (a nd)
    -- And the RHS has: (∏ nd' ∈ (L ++ [nd]).toFinset, (nodeDist nd' a) (a nd')) *
    --                   [∀ nd' ∉ L ++ [nd], a nd' = default]
    --
    -- Key facts:
    -- 1. (nodeDist nd' a₀) = (nodeDist nd' a) for nd' ∈ L (since nd ∉ parents of nd')
    -- 2. a₀ nd' = a nd' for nd' ≠ nd (by ha₀_cond2)
    -- 3. nodeDist nd a₀ = nodeDist nd a (nd ∉ parents nd)
    -- 4. Product over L ++ [nd] = (product over L) * (nodeDist nd a) (a nd)
    -- Simplify: mul_one on the RHS of second factor
    simp only [mul_one]
    -- Step 4: nodeDist nd a₀ = nodeDist nd a (since nd ∉ parents nd)
    have hnd_dist : nodeDist S sem pol nd a₀ = nodeDist S sem pol nd a :=
      nodeDist_update_irrel' sem pol nd nd a (defaultAssign S nd) (S.self_not_parent nd)
    rw [hnd_dist]
    -- Step 5: For nd' ∈ L, nodeDist nd' a₀ = nodeDist nd' a
    -- because nd is not a parent of nd' (topo ordering: nd comes after nd' in L ++ [nd])
    have hnd_not_parent_of_L : ∀ nd' ∈ L.toFinset, nd ∉ S.parents nd' := by
      intro nd' hnd' hp
      rw [List.mem_toFinset] at hnd'
      -- nd ∈ parents nd' and nd' ∈ L. By htopo, nd must appear before nd' in L ++ [nd].
      -- But nd only appears at index L.length, while nd' has index < L.length.
      -- So nd can't precede nd'. Thus (L ++ [nd])[j] = nd implies j.val < L.length,
      -- meaning nd ∈ L — contradicting hnd_notin.
      obtain ⟨i, hi_mem, hnd'_eq⟩ := List.getElem_of_mem
        (List.mem_append.mpr (Or.inl hnd') : nd' ∈ L ++ [nd])
      have hp' : nd ∈ S.parents (L ++ [nd])[i] := hnd'_eq ▸ hp
      obtain ⟨j, hj_lt, hj_eq⟩ := htopo ⟨i, hi_mem⟩ nd hp'
      have hj_in_L : j.val < L.length := by
        -- i < L.length (since (L ++ [nd])[i] = nd' ∈ L, and if i ≥ L.length then nd' = nd ∉ L)
        have hi_lt_L : i < L.length := by
          by_contra hc; push Not at hc
          have hi_eq : i = L.length := by simp at hi_mem; omega
          have h_eq_nd := getAppNd' ⟨i, hi_mem⟩ hi_eq
          rw [← hnd'_eq] at hnd'; exact hnd_notin (h_eq_nd ▸ hnd')
        -- j.val < ⟨i, hi_mem⟩.val = i < L.length
        have : (⟨i, hi_mem⟩ : Fin (L ++ [nd]).length).val = i := rfl
        omega
      rw [getAppL' j hj_in_L] at hj_eq
      exact hnd_notin (hj_eq ▸ List.getElem_mem ..)
    -- Replace nodeDist nd' a₀ with nodeDist nd' a for all nd' ∈ L.toFinset
    have hprod_eq : (∏ nd' ∈ L.toFinset, (nodeDist S sem pol nd' a₀) (a₀ nd')) =
        ∏ nd' ∈ L.toFinset, (nodeDist S sem pol nd' a) (a nd') := by
      apply Finset.prod_congr rfl
      intro nd' hnd'
      have hne : nd' ≠ nd := by
        intro h; subst h; exact hnd_notin (List.mem_toFinset.mp hnd')
      rw [ha₀_cond2 nd' hne]
      congr 1
      exact nodeDist_update_irrel' sem pol nd nd' a (defaultAssign S nd)
        (hnd_not_parent_of_L nd' hnd')
    rw [hprod_eq]
    -- Rewrite indicator using ha₀_cond1_iff
    rw [show (if ∀ nd' ∉ L, a₀ nd' = defaultAssign S nd' then (1 : ENNReal) else 0) =
        if ∀ nd' ∉ L ++ [nd], a nd' = defaultAssign S nd' then 1 else 0 from by
      congr 1; exact propext ha₀_cond1_iff]
    -- Now LHS = (∏ nd' ∈ L.toFinset, ...) * [cond] * (nodeDist nd a) (a nd)
    -- RHS = (∏ nd' ∈ (L ++ [nd]).toFinset, ...) * [cond]
    -- Extend product: (L ++ [nd]).toFinset = L.toFinset ∪ {nd}
    have hfs : (L ++ [nd]).toFinset = L.toFinset ∪ {nd} := by
      rw [List.toFinset_append]; simp
    rw [hfs, Finset.prod_union (by
      rw [Finset.disjoint_singleton_right]; rwa [List.mem_toFinset])]
    simp only [Finset.prod_singleton]
    ring

/-- Bayesian network marginal: folding node-by-node evaluation along a topological
prefix `L` gives the product of conditionals, with an indicator for agreement with
the default assignment off `L`.

This is the core Bayesian network factorization lemma, stated without naming any
intermediate fold construction. It is used by `assignProb_hasSum` and by
`FoldEval.evalFold_eq_assignProb`. -/
theorem bayesian_marginal_fold {S : Struct Player n}
    (sem : Sem S) (pol : Policy S)
    (L : List (Fin n)) (hnodup : L.Nodup)
    (htopo : ∀ (i : Fin L.length), ∀ p ∈ S.parents L[i],
      ∃ j : Fin L.length, j.val < i.val ∧ L[j] = p)
    (a : TAssign S) :
    (L.foldl (fun acc nd => acc.bind (fun a' =>
      (nodeDist S sem pol nd a').bind (fun v =>
        PMF.pure (updateAssign a' nd v))))
      (PMF.pure (defaultAssign S))) a =
    (L.toFinset.prod fun nd => (nodeDist S sem pol nd a) (a nd)) *
      (if ∀ nd, ¬ nd ∈ L → a nd = (defaultAssign S) nd then 1 else 0) :=
  foldl_evalStep_invariant sem pol L hnodup htopo a

-- ============================================================================
-- Order-free evaluation (the canonical API)
-- ============================================================================

/-- The Bayesian network factorization defines a valid probability distribution. -/
private theorem assignProb_hasSum (S : Struct Player n) (sem : Sem S) (pol : Policy S) :
    HasSum (assignProb S sem pol) 1 := by
  have σ := (topologicalOrder_exists S).some
  -- Construct a PMF by folding node-by-node (local, not an exported definition)
  let μ : PMF (TAssign S) := σ.order.foldl (fun acc nd => acc.bind (fun a =>
    (nodeDist S sem pol nd a).bind (fun v => PMF.pure (updateAssign a nd v))))
    (PMF.pure (defaultAssign S))
  suffices h : μ.val = assignProb S sem pol from h ▸ μ.2
  funext a
  change μ a = assignProb S sem pol a
  change (σ.order.foldl (fun acc nd => acc.bind (fun a' =>
    (nodeDist S sem pol nd a').bind (fun v => PMF.pure (updateAssign a' nd v))))
    (PMF.pure (defaultAssign S))) a = _
  rw [bayesian_marginal_fold sem pol σ.order σ.nodup
    (fun i p hp => σ.respects i p hp) a]
  have hmem : ∀ nd : Fin n, nd ∈ σ.order := σ.mem
  have hcond : (∀ nd, ¬ nd ∈ σ.order → a nd = (defaultAssign S) nd) = True :=
    propext ⟨fun _ => trivial, fun _ nd h => absurd (hmem nd) h⟩
  simp only [hcond, ite_true, mul_one, assignProb]
  congr 1
  have hfs : σ.order.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup σ.nodup, σ.length, Fintype.card_fin]
  rw [hfs]

/-- Joint distribution over total assignments, defined as the product of
conditional distributions (Bayesian network factorization).

This is manifestly independent of any topological order. -/
noncomputable def evalAssignDist (S : Struct Player n) (sem : Sem S) (pol : Policy S) :
    PMF (TAssign S) :=
  ⟨assignProb S sem pol, assignProb_hasSum S sem pol⟩

/-- Payoff for a player: sum of utility values over that player's utility nodes. -/
noncomputable def utilityOf (S : Struct Player n) (sem : Sem S)
    (a : TAssign S) (p : Player) : ℝ :=
  Finset.univ.sum (fun (u : UtilityNode S p) =>
    sem.utilityFn p u (projCfg a (S.parents u.val)))

-- ============================================================================
-- Game — KernelGame bridge
-- ============================================================================

/-- Convert a MAID to a kernel-based game. The outcome kernel is the
order-free Bayesian network factorization. -/
noncomputable def toKernelGame (S : Struct Player n) (sem : Sem S) :
    GameTheory.KernelGame Player where
  Strategy := PlayerStrategy S
  Outcome := TAssign S
  utility := fun a => utilityOf S sem a
  outcomeKernel := fun pol => evalAssignDist S sem pol

-- ============================================================================
-- Order-independence — swap lemmas
-- ============================================================================

/-- Two nodes have no direct edge between them. -/
def NoDirectEdge (S : Struct Player n) (u v : Fin n) : Prop :=
  u ∉ S.parents v ∧ v ∉ S.parents u

/-- Updating at a node not in `ps` doesn't change a projection onto `ps`. -/
theorem projCfg_update_irrel {S : Struct Player n} (a : TAssign S)
    (nd : Fin n) (v : S.Val nd) (ps : Finset (Fin n)) (hnd : nd ∉ ps) :
    projCfg (updateAssign a nd v) ps = projCfg a ps := by
  ext ⟨nd', hnd'⟩
  simp only [projCfg, updateAssign]
  split
  · next h => exact absurd (h ▸ hnd') hnd
  · rfl

/-- Updating at a node in `ps` and projecting gives the new value at that node. -/
theorem projCfg_update_self {S : Struct Player n} (a : TAssign S)
    (nd : Fin n) (v : S.Val nd) (ps : Finset (Fin n)) (hnd : nd ∈ ps) :
    projCfg (updateAssign a nd v) ps ⟨nd, hnd⟩ = v := by
  simp [projCfg, updateAssign]

/-- `nodeDist` at `nd₂` is unchanged when we update at `nd₁`, provided `nd₁ ∉ S.parents nd₂`. -/
theorem nodeDist_update_irrel {S : Struct Player n} (sem : Sem S) (pol : Policy S)
    (nd₁ nd₂ : Fin n) (a : TAssign S) (v : S.Val nd₁)
    (h : nd₁ ∉ S.parents nd₂) :
    nodeDist S sem pol nd₂ (updateAssign a nd₁ v) = nodeDist S sem pol nd₂ a := by
  unfold nodeDist
  split
  · congr 1; exact projCfg_update_irrel a nd₁ v _ h
  · congr 1; exact Sigma.ext rfl (heq_of_eq (projCfg_update_irrel a nd₁ v _
      (fun hmem => h (S.obs_sub nd₂ hmem))))
  · rfl

/-- Reading `updateAssign` at a different node returns the old value. -/
theorem updateAssign_get_ne {S : Struct Player n} (a : TAssign S)
    (nd nd' : Fin n) (v : S.Val nd) (hne : nd' ≠ nd) :
    updateAssign a nd v nd' = a nd' := by
  simp [updateAssign, hne]

/-- Reading `updateAssign` at the same node returns the new value. -/
theorem updateAssign_get_self {S : Struct Player n} (a : TAssign S)
    (nd : Fin n) (v : S.Val nd) :
    updateAssign a nd v nd = v := by
  simp [updateAssign]

/-- `updateAssign` commutes on distinct nodes. -/
theorem updateAssign_comm {S : Struct Player n} (a : TAssign S)
    (nd₁ nd₂ : Fin n) (v₁ : S.Val nd₁) (v₂ : S.Val nd₂) (hne : nd₁ ≠ nd₂) :
    updateAssign (updateAssign a nd₁ v₁) nd₂ v₂ =
    updateAssign (updateAssign a nd₂ v₂) nd₁ v₁ := by
  ext nd'
  simp only [updateAssign]
  split <;> split <;> simp_all only [ne_eq]
  · next h₁ h₂ => exact absurd (h₂.symm ▸ h₁) hne

-- ============================================================================
-- Pure strategies
-- ============================================================================

/-- A pure strategy for player `p`: choose a value at each info set. -/
def PureStrategy (S : Struct Player n) (p : Player) :=
  (I : Infoset S p) → S.Val I.1.val

/-- A pure policy: a pure strategy for every player. -/
def PurePolicy (S : Struct Player n) := (p : Player) → PureStrategy S p

instance (S : Struct Player n) (p : Player) : Fintype (PureStrategy S p) :=
  Pi.instFintype

instance (S : Struct Player n) (p : Player) : Nonempty (PureStrategy S p) :=
  ⟨fun _ => default⟩

instance (S : Struct Player n) : Fintype (PurePolicy S) :=
  Pi.instFintype

instance (S : Struct Player n) : Nonempty (PurePolicy S) :=
  ⟨fun _ _ => default⟩

/-- Lift a pure strategy to a behavioral (deterministic) player strategy. -/
noncomputable def pureToPlayerStrategy {S : Struct Player n} {p : Player}
    (σ : PureStrategy S p) : PlayerStrategy S p :=
  fun I => PMF.pure (σ I)

/-- Lift a pure policy to a (deterministic) policy. -/
noncomputable def pureToPolicy {S : Struct Player n}
    (π : PurePolicy S) : Policy S :=
  fun p => pureToPlayerStrategy (π p)

end MAID
