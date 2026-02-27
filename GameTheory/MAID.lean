import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

import GameTheory.KernelGame

/-!
# Multi-Agent Influence Diagrams (MAID) — Typed Redesign

EFG-style typed MAID: illegality is untypeable.
Nodes indexed by `Fin n`, values typed by `Val S nd = Fin (S.domainSize nd)`.

## Sections
- § 1. Core — `NodeKind`, `Struct`, typed assignments
- § 2. Semantics — `Sem`, strategies, evaluation
- § 3. Game — `KernelGame` bridge
- § 4. Order-independence — swap lemmas
-/

namespace MAID

-- ============================================================================
-- Core — pure structure
-- ============================================================================

/-- The kind of a node in a MAID. -/
inductive NodeKind (Player : Type) where
  | chance
  | decision (agent : Player)
  | utility (agent : Player)
deriving DecidableEq, Repr

/-- A MAID structure: DAG with typed nodes over `Fin n`. -/
structure Struct (Player : Type) [DecidableEq Player] [Fintype Player]
    (n : Nat) where
  kind : Fin n → NodeKind Player
  parents    : Fin n → Finset (Fin n)
  obsParents : Fin n → Finset (Fin n)
  domainSize : Fin n → Nat
  topoOrder  : List (Fin n)
  -- Invariants
  obs_sub        : ∀ nd, obsParents nd ⊆ parents nd
  obs_eq_nondec  : ∀ nd, (¬ ∃ a, kind nd = .decision a) → obsParents nd = parents nd
  utility_domain : ∀ nd a, kind nd = .utility a → domainSize nd = 1
  nonutility_pos : ∀ nd, (¬ ∃ a, kind nd = .utility a) → 0 < domainSize nd
  topo_nodup     : topoOrder.Nodup
  topo_length    : topoOrder.length = n
  topo_acyclic   : ∀ (i : Fin topoOrder.length),
    ∀ p ∈ parents (topoOrder[i]),
      ∃ j : Fin topoOrder.length, j.val < i.val ∧ topoOrder[j] = p

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

/-- Chance node subtype. -/
abbrev ChanceNode (S : Struct Player n) := {nd : Fin n // S.kind nd = .chance}

/-- Decision node subtype for a given player. -/
abbrev DecisionNode (S : Struct Player n) (p : Player) :=
  {nd : Fin n // S.kind nd = .decision p}

/-- Utility node subtype for a given player. -/
abbrev UtilityNode (S : Struct Player n) (p : Player) :=
  {nd : Fin n // S.kind nd = .utility p}

/-- Every node has positive domain size. -/
theorem Struct.dom_pos (S : Struct Player n) (nd : Fin n) :
    0 < S.domainSize nd := by
  by_cases h : ∃ a, S.kind nd = .utility a
  · obtain ⟨a, ha⟩ := h
    rw [S.utility_domain nd a ha]; exact Nat.one_pos
  · exact S.nonutility_pos nd h

/-- Every node appears in the topological order. -/
theorem Struct.topo_mem (S : Struct Player n) (nd : Fin n) :
    nd ∈ S.topoOrder := by
  have hfs : S.topoOrder.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup S.topo_nodup, S.topo_length, Fintype.card_fin]
  rw [← List.mem_toFinset]
  rw [hfs]
  exact Finset.mem_univ nd

/-- Perfect recall for a MAID: for each player, every later decision node
    (in topo order) observes earlier decision nodes and their observations. -/
def Struct.PerfectRecall (S : Struct Player n) : Prop :=
  ∀ (p : Player) (d₁ d₂ : Fin n),
    S.kind d₁ = .decision p → S.kind d₂ = .decision p →
    (∃ i₁ i₂ : Fin S.topoOrder.length,
      S.topoOrder[i₁] = d₁ ∧ S.topoOrder[i₂] = d₂ ∧ i₁.val < i₂.val) →
    d₁ ∈ S.obsParents d₂ ∧ S.obsParents d₁ ⊆ S.obsParents d₂

/-- Typed value at a node. -/
abbrev Val (S : Struct Player n) (nd : Fin n) := Fin (S.domainSize nd)

/-- Configuration: values at a subset of nodes. -/
abbrev Cfg (S : Struct Player n) (ps : Finset (Fin n)) :=
  (nd : ↥ps) → Val S nd.val

/-- Total assignment: a value at every node. -/
abbrev TAssign (S : Struct Player n) := ∀ nd : Fin n, Val S nd

/-- Project a total assignment to a configuration on a subset. -/
def projCfg {S : Struct Player n} (a : TAssign S) (ps : Finset (Fin n)) :
    Cfg S ps :=
  fun nd => a nd.val

/-- Default assignment: 0 at every node. -/
def defaultAssign (S : Struct Player n) : TAssign S :=
  fun nd => ⟨0, S.dom_pos nd⟩

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
  inferInstanceAs (DecidableEq ((nd : ↥ps) → Val S nd.val))

/-- Info set: which decision node + observed parent configuration. -/
def Infoset (S : Struct Player n) (p : Player) :=
  Σ (d : DecisionNode S p), Cfg S (S.obsParents d.val)

instance (S : Struct Player n) (p : Player) : Fintype (Infoset S p) :=
  Sigma.instFintype

instance (S : Struct Player n) (p : Player) : DecidableEq (Infoset S p) :=
  inferInstanceAs (DecidableEq (Σ (d : DecisionNode S p), Cfg S (S.obsParents d.val)))

-- ============================================================================
-- Semantics — evaluation
-- ============================================================================

/-- Semantic data for a MAID: chance CPDs and utility functions. -/
structure Sem (S : Struct Player n) where
  chanceCPD : (c : ChanceNode S) → Cfg S (S.parents c.val) → PMF (Val S c.val)
  utilityFn : (p : Player) → (u : UtilityNode S p) → Cfg S (S.parents u.val) → ℝ

/-- Per-player strategy: maps each info set to a distribution over actions. -/
def PlayerStrategy (S : Struct Player n) (p : Player) :=
  (I : Infoset S p) → PMF (Val S I.1.val)

/-- Joint policy: a strategy for every player. -/
def Policy (S : Struct Player n) := (p : Player) → PlayerStrategy S p

/-- Distribution at a single node, given the current total assignment.
    Dispatches by node kind using `match` on `S.kind nd`. -/
noncomputable def nodeDist (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (nd : Fin n) (a : TAssign S) : PMF (Val S nd) :=
  match hk : S.kind nd with
  | .chance => sem.chanceCPD ⟨nd, hk⟩ (projCfg a (S.parents nd))
  | .decision p => pol p ⟨⟨nd, hk⟩, projCfg a (S.obsParents nd)⟩
  | .utility _ => PMF.pure ⟨0, by rw [S.utility_domain nd _ hk]; exact Nat.one_pos⟩

/-- Update a total assignment at node `nd` with value `v`. -/
def updateAssign {S : Struct Player n} (a : TAssign S) (nd : Fin n) (v : Val S nd) :
    TAssign S :=
  fun nd' => if h : nd' = nd then h ▸ v else a nd'

/-- One step of the evaluation fold: draw a value at `nd` and update the assignment. -/
noncomputable def evalStep (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (acc : PMF (TAssign S)) (nd : Fin n) : PMF (TAssign S) :=
  acc.bind (fun a =>
    (nodeDist S sem pol nd a).bind (fun v =>
      PMF.pure (updateAssign a nd v)))

/-- Joint distribution over total assignments, by folding over the topological order. -/
noncomputable def evalAssignDist (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    : PMF (TAssign S) :=
  S.topoOrder.foldl (evalStep S sem pol) (PMF.pure (defaultAssign S))

/-- Payoff for a player: sum of utility values over that player's utility nodes. -/
noncomputable def utilityOf (S : Struct Player n) (sem : Sem S)
    (a : TAssign S) (p : Player) : ℝ :=
  Finset.univ.sum (fun (u : UtilityNode S p) =>
    sem.utilityFn p u (projCfg a (S.parents u.val)))

-- ============================================================================
-- Game — KernelGame bridge
-- ============================================================================

/-- Convert a typed MAID to a kernel-based game. -/
noncomputable def toKernelGame (S : Struct Player n) (sem : Sem S) :
    GameTheory.KernelGame Player where
  Strategy := PlayerStrategy S
  Outcome := TAssign S
  utility := fun a => utilityOf S sem a
  outcomeKernel := fun σ => evalAssignDist S sem σ

-- ============================================================================
-- Order-independence — swap lemmas
-- ============================================================================

/-- Two nodes have no direct edge between them. -/
def NoDirectEdge (S : Struct Player n) (u v : Fin n) : Prop :=
  u ∉ S.parents v ∧ v ∉ S.parents u

/-- Updating at a node not in `ps` doesn't change a projection onto `ps`. -/
theorem projCfg_update_irrel {S : Struct Player n} (a : TAssign S)
    (nd : Fin n) (v : Val S nd) (ps : Finset (Fin n)) (hnd : nd ∉ ps) :
    projCfg (updateAssign a nd v) ps = projCfg a ps := by
  ext ⟨nd', hnd'⟩
  simp only [projCfg, updateAssign]
  split
  · next h => exact absurd (h ▸ hnd') hnd
  · rfl

/-- Updating at a node in `ps` and projecting gives the new value at that node. -/
theorem projCfg_update_self {S : Struct Player n} (a : TAssign S)
    (nd : Fin n) (v : Val S nd) (ps : Finset (Fin n)) (hnd : nd ∈ ps) :
    projCfg (updateAssign a nd v) ps ⟨nd, hnd⟩ = v := by
  simp [projCfg, updateAssign]

/-- `nodeDist` at `nd₂` is unchanged when we update at `nd₁`, provided `nd₁ ∉ S.parents nd₂`. -/
theorem nodeDist_update_irrel {S : Struct Player n} (sem : Sem S) (pol : Policy S)
    (nd₁ nd₂ : Fin n) (a : TAssign S) (v : Val S nd₁)
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
    (nd nd' : Fin n) (v : Val S nd) (hne : nd' ≠ nd) :
    updateAssign a nd v nd' = a nd' := by
  simp [updateAssign, hne]

/-- Reading `updateAssign` at the same node returns the new value. -/
theorem updateAssign_get_self {S : Struct Player n} (a : TAssign S)
    (nd : Fin n) (v : Val S nd) :
    updateAssign a nd v nd = v := by
  simp [updateAssign]

/-- `updateAssign` commutes on distinct nodes. -/
theorem updateAssign_comm {S : Struct Player n} (a : TAssign S)
    (nd₁ nd₂ : Fin n) (v₁ : Val S nd₁) (v₂ : Val S nd₂) (hne : nd₁ ≠ nd₂) :
    updateAssign (updateAssign a nd₁ v₁) nd₂ v₂ =
    updateAssign (updateAssign a nd₂ v₂) nd₁ v₁ := by
  ext nd'
  simp only [updateAssign]
  split <;> split <;> simp_all only [ne_eq]
  · next h₁ h₂ => exact absurd (h₂.symm ▸ h₁) hne

/-- Swapping two adjacent independent nodes in `evalStep` gives the same result. -/
theorem evalStep_swap {S : Struct Player n} (sem : Sem S) (pol : Policy S)
    (nd₁ nd₂ : Fin n) (hne : nd₁ ≠ nd₂)
    (hindep : NoDirectEdge S nd₁ nd₂)
    (acc : PMF (TAssign S)) :
    evalStep S sem pol (evalStep S sem pol acc nd₁) nd₂ =
    evalStep S sem pol (evalStep S sem pol acc nd₂) nd₁ := by
  simp only [evalStep, PMF.bind_bind, PMF.pure_bind]
  congr 1; funext a
  simp_rw [nodeDist_update_irrel sem pol nd₁ nd₂ a _ hindep.1]
  simp_rw [nodeDist_update_irrel sem pol nd₂ nd₁ a _ hindep.2]
  simp_rw [updateAssign_comm a nd₁ nd₂ _ _ hne]
  exact PMF.bind_comm _ _ _

/-- Swap two adjacent elements in a list. -/
def swapAdj (l : List α) (i : Nat) (hi : i + 1 < l.length) : List α :=
  let a := l[i]'(by omega)
  let b := l[i + 1]'hi
  (l.set i b).set (i + 1) a

/-- General lemma: swapping adjacent elements in a `foldl` is invariant when
    the fold function commutes on those two elements (for any accumulator). -/
theorem foldl_swapAdj {α β : Type*} (f : α → β → α) (init : α) (l : List β)
    (i : Nat) (hi : i + 1 < l.length)
    (hcomm : ∀ acc, f (f acc (l[i]'(by omega))) (l[i + 1]'hi) =
                     f (f acc (l[i + 1]'hi)) (l[i]'(by omega))) :
    l.foldl f init = (swapAdj l i hi).foldl f init := by
  induction i generalizing l init with
  | zero =>
    match l, hi with
    | a :: b :: rest, _ =>
      simp only [swapAdj, List.getElem_cons_zero, List.getElem_cons_succ,
                  List.set_cons_zero, List.set_cons_succ, List.set_cons_zero,
                  List.foldl_cons]
      have h := hcomm init
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
      rw [h]
  | succ j ih =>
    match l, hi with
    | x :: xs, hi' =>
      simp only [List.foldl_cons]
      have hlen : j + 1 < xs.length := by
        simp only [List.length_cons] at hi'; omega
      have hswap : swapAdj (x :: xs) (j + 1) hi' = x :: swapAdj xs j hlen := by
        unfold swapAdj
        simp [List.getElem_cons_succ, List.set_cons_succ]
      rw [hswap, List.foldl_cons]
      exact ih (f init x) xs hlen (fun acc => by
        have := hcomm acc
        simp only [List.getElem_cons_succ] at this
        exact this)

/-- Swapping two adjacent independent nodes in the topological order
    doesn't change `evalAssignDist`. -/
theorem evalAssignDist_swap_adj {S : Struct Player n} (sem : Sem S) (pol : Policy S)
    (i : Nat) (hi : i + 1 < S.topoOrder.length)
    (hne : S.topoOrder[i]'(by omega) ≠ S.topoOrder[i + 1]'hi)
    (hindep : NoDirectEdge S (S.topoOrder[i]'(by omega)) (S.topoOrder[i + 1]'hi)) :
    evalAssignDist S sem pol =
    (swapAdj S.topoOrder i hi).foldl (evalStep S sem pol) (PMF.pure (defaultAssign S)) := by
  simp only [evalAssignDist]
  exact foldl_swapAdj _ _ _ i hi (fun acc =>
    evalStep_swap sem pol _ _ hne hindep acc)

end MAID
