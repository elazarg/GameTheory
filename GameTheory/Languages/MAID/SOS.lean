import GameTheory.Languages.MAID.Syntax
import GameTheory.Model.SemanticForm

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

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

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
  (d : DecisionNode S p) → Option (Val S d.1)

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
    (S : Struct Player n) (nd : Fin n) (h : ∃ p, S.kind nd = .utility p) :
    Val S nd := by
  let p := Classical.choose h
  let hp : S.kind nd = .utility p := Classical.choose_spec h
  refine ⟨0, ?_⟩
  rw [S.utility_domain nd p hp]
  exact Nat.one_pos

/-- A simultaneous assignment of values to the current frontier. -/
abbrev FrontierValues (S : Struct Player n) (cfg : FrontierCfg S) :=
  (nd : ↥(frontier S cfg)) → Val S nd.1

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

/-- A proposed frontier value is compatible with the MAID semantics and the
players' simultaneous frontier controls. -/
def FrontierValueAllowed (S : Struct Player n) (sem : Sem S)
    (cfg : FrontierCfg S)
    (acts : ∀ p : Player, Option (FrontierAct S p))
    (nd : Fin n) (hnd : nd ∈ frontier S cfg) (v : Val S nd) : Prop :=
  match hk : S.kind nd with
  | .chance =>
      let hParents : S.parents nd ⊆ cfg.assigned := by
        intro x hx
        have hen : enabled S cfg nd := by
          simpa [frontier] using hnd
        exact hen.2 hx
      sem.chanceCPD ⟨nd, hk⟩ (restrictCfg cfg (S.parents nd) hParents) v ≠ 0
  | .decision p =>
      ∃ α : FrontierAct S p,
        acts p = some α ∧ α ⟨nd, hk⟩ = some v
  | .utility _ =>
      v = utilityValue S nd ⟨_, hk⟩

/-- One frontier step in the native MAID SOS semantics. -/
inductive Step (S : Struct Player n) (sem : Sem S) :
    (∀ p : Player, Option (FrontierAct S p)) → FrontierCfg S → FrontierCfg S → Prop where
  | mk {cfg : FrontierCfg S}
      {acts : ∀ p : Player, Option (FrontierAct S p)}
      {vals : FrontierValues S cfg} :
      (∀ nd : ↥(frontier S cfg),
        FrontierValueAllowed S sem cfg acts nd.1 nd.2 (vals nd)) →
      Step S sem acts cfg (extendFrontier S cfg vals)

/-- Reachability in the native frontier semantics. -/
abbrev ReachBy (S : Struct Player n) (sem : Sem S) :=
  Semantics.Transition.ReachBy (Step S sem)

end MAID
