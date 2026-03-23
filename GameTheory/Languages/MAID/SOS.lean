import GameTheory.Languages.MAID.Syntax
import GameTheory.Languages.InfoModel.SemanticForm
import Math.PMFProduct

/-!
# GameTheory.Languages.MAID.SOS

Native frontier semantics for MAIDs.

A MAID state is a partial assignment. One step assigns the entire enabled
frontier simultaneously:
- chance nodes sample from their CPDs
- decision nodes take values from the players' frontier actions
- utility nodes are deterministic (their domain is singleton)

This keeps the source-language semantics close to the DAG's partial order rather
than forcing an arbitrary node-by-node schedule.
-/

namespace MAID

open GameTheory

variable {Player : Type} [DecidableEq Player] [fp : Fintype Player] {n : Nat}

/-- A partial MAID assignment together with its assigned-node domain. -/
structure FrontierCfg (S : Struct Player n) where
  assigned : Finset (Fin n)
  values : Cfg S assigned

/-- Initial frontier configuration: no node has been assigned yet. -/
def initialCfg (S : Struct Player n) : FrontierCfg S where
  assigned := ∅
  values := fun
    | ⟨_, hmem⟩ => by
        simp at hmem

/-- Nodes enabled by the current partial assignment. -/
def enabled (S : Struct Player n) (cfg : FrontierCfg S) (nd : Fin n) : Prop :=
  nd ∉ cfg.assigned ∧ S.parents nd ⊆ cfg.assigned

/-- The current enabled frontier. -/
noncomputable def frontier (S : Struct Player n) (cfg : FrontierCfg S) : Finset (Fin n) :=
  by
    classical
    exact Finset.filter (enabled S cfg) Finset.univ

/-- Frontier nodes listed in canonical order. -/
noncomputable def frontierList (S : Struct Player n) (cfg : FrontierCfg S) : List (Fin n) :=
  (frontier S cfg).toList

/-- Player action alphabet for one frontier step: a partial assignment over all
of that player's decision nodes. Only currently enabled decision nodes are read
by the SOS step relation. -/
abbrev FrontierAct (S : Struct Player n) (p : Player) :=
  (d : DecisionNode S p) → Option (S.Val d.1)

/-- Restrict a partial assignment to a smaller parent set. -/
def restrictCfg {S : Struct Player n}
    (cfg : FrontierCfg S) (ps : Finset (Fin n)) (hps : ps ⊆ cfg.assigned) :
    Cfg S ps :=
  fun nd => cfg.values ⟨nd.1, hps nd.2⟩

/-- The info available to player `p` at the current frontier: all enabled
frontier decision nodes owned by `p`, with their observed-parent values. -/
noncomputable def frontierInfosets (S : Struct Player n) (cfg : FrontierCfg S) (p : Player) :
    List (Infoset S p) :=
  (frontier S cfg).toList.filterMap fun nd =>
    if hEnabled : nd ∈ frontier S cfg then
      match hk : S.kind nd with
      | .decision q =>
          if hq : q = p then
            let hParents : S.obsParents nd ⊆ cfg.assigned :=
              fun x hx =>
                have hen : enabled S cfg nd := by
                  simpa [frontier] using hEnabled
                have hx' : x ∈ S.parents nd := by
                  simpa [hq] using (S.obs_sub nd hx)
                hen.2 hx'
            have hk' : S.kind nd = .decision p := by simpa [hq] using hk
            some ⟨⟨nd, hk'⟩, restrictCfg cfg (S.obsParents nd) hParents⟩
          else
            none
      | _ => none
    else
      none

/-- Default value for deterministic utility nodes on the frontier. -/
noncomputable def utilityValue
    (S : Struct Player n) (nd : Fin n) (_h : ∃ p, S.kind nd = .utility p) :
    S.Val nd :=
  default

/-- A simultaneous assignment of values to the current frontier. -/
abbrev FrontierValues (S : Struct Player n) (cfg : FrontierCfg S) :=
  (nd : ↥(frontier S cfg)) → S.Val nd.1

/-- Extend a partial assignment by assigning the whole current frontier. -/
noncomputable def extendFrontier (S : Struct Player n) (cfg : FrontierCfg S)
    (vals : FrontierValues S cfg) : FrontierCfg S where
  assigned := cfg.assigned ∪ frontier S cfg
  values := fun nd =>
    if hOld : nd.1 ∈ cfg.assigned then
      cfg.values ⟨nd.1, hOld⟩
    else
      vals ⟨nd.1, by
        exact (Finset.mem_union.mp nd.2).resolve_left hOld⟩

/-- Per-node distribution over values at a frontier node. Chance nodes sample
from their CPDs, decision nodes use the player's action (defaulting to 0),
and utility nodes take their deterministic value. -/
noncomputable def nodeDistrib (S : Struct Player n) (sem : Sem S)
    (cfg : FrontierCfg S) (acts : ∀ p : Player, Option (FrontierAct S p))
    (nd : ↥(frontier S cfg)) : PMF (S.Val nd.1) :=
  have hEnabled : enabled S cfg nd.1 := by
    have := nd.2; simp only [frontier, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  match hk : S.kind nd.1 with
  | .chance =>
      sem.chanceCPD ⟨nd.1, hk⟩ (restrictCfg cfg (S.parents nd.1) hEnabled.2)
  | .decision p =>
      match acts p with
      | some α =>
          match α ⟨nd.1, hk⟩ with
          | some v => PMF.pure v
          | none   => PMF.pure default
      | none => PMF.pure default
  | .utility _ =>
      PMF.pure (utilityValue S nd.1 ⟨_, hk⟩)

/-- A proposed frontier value is allowed iff the per-node distribution assigns
it nonzero probability. -/
def FrontierValueAllowed (S : Struct Player n) (sem : Sem S)
    (cfg : FrontierCfg S)
    (acts : ∀ p : Player, Option (FrontierAct S p))
    (nd : ↥(frontier S cfg)) (v : S.Val nd.1) : Prop :=
  nodeDistrib S sem cfg acts nd v ≠ 0

/-- One frontier step in the native MAID SOS semantics. -/
inductive Step (S : Struct Player n) (sem : Sem S) :
    (∀ p : Player, Option (FrontierAct S p)) → FrontierCfg S → FrontierCfg S → Prop where
  | mk {cfg : FrontierCfg S}
      {acts : ∀ p : Player, Option (FrontierAct S p)}
      {vals : FrontierValues S cfg} :
      (∀ nd : ↥(frontier S cfg),
        FrontierValueAllowed S sem cfg acts nd (vals nd)) →
      Step S sem acts cfg (extendFrontier S cfg vals)

/-- Reachability in the native frontier semantics. -/
abbrev ReachBy (S : Struct Player n) (sem : Sem S) :=
  Semantics.Transition.ReachBy (Step S sem)

-- ============================================================================
-- Policy-driven frontier evaluation
-- ============================================================================

/-- Per-node distribution under a policy. Chance nodes sample from their CPDs,
decision nodes use the policy, utility nodes are deterministic. -/
noncomputable def nodeDistPol (S : Struct Player n) (sem : Sem S)
    (pol : Policy S) (cfg : FrontierCfg S)
    (nd : ↥(frontier S cfg)) : PMF (S.Val nd.1) :=
  have hEnabled : enabled S cfg nd.1 := by
    have := nd.2; simp only [frontier, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  match hk : S.kind nd.1 with
  | .chance =>
      sem.chanceCPD ⟨nd.1, hk⟩ (restrictCfg cfg (S.parents nd.1) hEnabled.2)
  | .decision p =>
      pol p ⟨⟨nd.1, hk⟩, restrictCfg cfg (S.obsParents nd.1)
        (fun x hx => hEnabled.2 (S.obs_sub nd.1 hx))⟩
  | .utility _ =>
      PMF.pure (utilityValue S nd.1 ⟨_, hk⟩)

/-- One frontier step under a policy: sample independently at each frontier node
then extend the configuration. -/
noncomputable def frontierStepPol (S : Struct Player n) (sem : Sem S)
    (pol : Policy S) (cfg : FrontierCfg S) : PMF (FrontierCfg S) :=
  Math.ProbabilityMassFunction.pushforward
    (Math.PMFProduct.pmfPi (nodeDistPol S sem pol cfg))
    (extendFrontier S cfg)

/-- Extract total assignment from a frontier config (default 0 for unassigned). -/
def extractTAssign (S : Struct Player n)
    (cfg : FrontierCfg S) : TAssign S :=
  fun nd => if h : nd ∈ cfg.assigned then cfg.values ⟨nd, h⟩
            else default

/-- Frontier evaluation: iterate frontier steps, extract terminal assignment.
`n` steps suffice (each step assigns ≥1 node while unassigned nodes remain). -/
noncomputable def frontierEval (S : Struct Player n) (sem : Sem S)
    (pol : Policy S) : PMF (TAssign S) :=
  (Nat.iterate (fun d => d.bind (frontierStepPol S sem pol)) n
    (PMF.pure (initialCfg S))).map (extractTAssign S)

-- ============================================================================
-- Frontier infrastructure lemmas
-- ============================================================================

/-- An enabled node is not yet assigned. -/
theorem frontier_not_assigned (S : Struct Player n) (cfg : FrontierCfg S) (nd : Fin n)
    (h : nd ∈ frontier S cfg) : nd ∉ cfg.assigned := by
  classical
  have : enabled S cfg nd := (Finset.mem_filter.mp h).2
  exact this.1

/-- After `extendFrontier`, the old frontier is assigned. -/
theorem frontier_sub_extendFrontier_assigned (S : Struct Player n)
    (cfg : FrontierCfg S) (vals : FrontierValues S cfg) :
    frontier S cfg ⊆ (extendFrontier S cfg vals).assigned := by
  intro nd hnd
  simp only [extendFrontier, Finset.mem_union]
  exact Or.inr hnd

/-- After `extendFrontier`, old assigned nodes stay assigned. -/
theorem assigned_sub_extendFrontier (S : Struct Player n)
    (cfg : FrontierCfg S) (vals : FrontierValues S cfg) :
    cfg.assigned ⊆ (extendFrontier S cfg vals).assigned := by
  intro nd hnd
  simp only [extendFrontier, Finset.mem_union]
  exact Or.inl hnd

/-- `extendFrontier` is injective on frontier values (for a fixed `cfg`). -/
theorem extendFrontier_vals_injective (S : Struct Player n) (cfg : FrontierCfg S)
    (vals₁ vals₂ : FrontierValues S cfg)
    (h : extendFrontier S cfg vals₁ = extendFrontier S cfg vals₂) :
    vals₁ = vals₂ := by
  funext ⟨nd, hnd⟩
  have hna : nd ∉ cfg.assigned := frontier_not_assigned S cfg nd hnd
  let extract : FrontierCfg S → S.Val nd :=
    fun c => if hm : nd ∈ c.assigned then c.values ⟨nd, hm⟩ else default
  have h1 : extract (extendFrontier S cfg vals₁) = vals₁ ⟨nd, hnd⟩ := by
    simp only [extract, extendFrontier, Finset.mem_union, hnd, or_true, dite_true, hna,
      dite_false]
  have h2 : extract (extendFrontier S cfg vals₂) = vals₂ ⟨nd, hnd⟩ := by
    simp only [extract, extendFrontier, Finset.mem_union, hnd, or_true, dite_true, hna,
      dite_false]
  rw [← h1, ← h2]
  exact congrArg extract h

/-- `frontier` depends only on `assigned`: equal assigned sets give equal frontiers. -/
theorem frontier_eq_of_assigned_eq (S : Struct Player n)
    (cfg₁ cfg₂ : FrontierCfg S)
    (h : cfg₁.assigned = cfg₂.assigned) :
    frontier S cfg₁ = frontier S cfg₂ := by
  simp only [frontier]
  congr 1; ext nd
  simp only [enabled]
  rw [h]

/-- `extendFrontier` preserves values at already-assigned nodes. -/
theorem extendFrontier_preserves_old (S : Struct Player n)
    (cfg : FrontierCfg S) (vals : FrontierValues S cfg)
    (nd : Fin n) (hOld : nd ∈ cfg.assigned)
    (hNew : nd ∈ (extendFrontier S cfg vals).assigned) :
    (extendFrontier S cfg vals).values ⟨nd, hNew⟩ = cfg.values ⟨nd, hOld⟩ := by
  simp only [extendFrontier, hOld, dite_true]

/-- `extendFrontier` sets frontier values at frontier nodes. -/
theorem extendFrontier_sets_frontier (S : Struct Player n)
    (cfg : FrontierCfg S) (vals : FrontierValues S cfg)
    (nd : Fin n) (hFr : nd ∈ frontier S cfg)
    (hNew : nd ∈ (extendFrontier S cfg vals).assigned) :
    (extendFrontier S cfg vals).values ⟨nd, hNew⟩ = vals ⟨nd, hFr⟩ := by
  have hna : nd ∉ cfg.assigned := frontier_not_assigned S cfg nd hFr
  simp only [extendFrontier, hna, dite_false]

/-- If the assigned set does not cover all nodes, the frontier is nonempty. -/
theorem frontier_nonempty_of_ne_univ (S : Struct Player n)
    (cfg : FrontierCfg S) (h : cfg.assigned ≠ Finset.univ) :
    (frontier S cfg).Nonempty := by
  classical
  -- There exists an unassigned node
  have hne : (Finset.univ \ cfg.assigned).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact h (Finset.eq_univ_of_forall (fun x => hsub (Finset.mem_univ x)))
  -- WellFounded parent relation from acyclicity
  have wf := S.acyclic.wellFounded
  -- Find minimal unassigned node under the parent relation
  set U := (Finset.univ \ cfg.assigned : Finset (Fin n))
  have hne' : (U : Set (Fin n)).Nonempty := Finset.coe_nonempty.mpr hne
  set m := wf.min (U : Set (Fin n)) hne'
  have hm_mem : m ∈ U := wf.min_mem _ hne'
  have hm_min : ∀ y, y ∈ S.parents m → y ∉ U := by
    intro y hy hyU
    exact wf.not_lt_min _ hne' hyU hy
  -- m is in the frontier: unassigned with all parents assigned
  have hm_unassigned : m ∉ cfg.assigned := by
    simp only [U, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm_mem
    exact hm_mem
  have hm_parents : S.parents m ⊆ cfg.assigned := by
    intro p hp
    by_contra h'
    exact hm_min p hp (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h'⟩)
  exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hm_unassigned, hm_parents⟩⟩⟩

end MAID
