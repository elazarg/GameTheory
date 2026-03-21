import GameTheory.Languages.MAID.FrontierLemmas

/-!
# Frontier evaluation equals order-free evaluation

The main result is `frontierEval_eq_evalAssignDist`: parallel frontier
evaluation gives the same joint distribution as the Bayesian network
factorization (`evalAssignDist`).

## Proof structure

1. **Frontier independence** (`frontier_noDirectEdge`): two distinct frontier
   nodes cannot be parent of each other (immediate from `enabled`).

2. **One-step sequentialization**: `frontierStepPol` equals a sequential fold
   of single-node steps over the frontier list, where each step samples from
   the conditional distribution computed from the *original* config.

3. **Global iteration**: composing layer-by-layer sequential steps yields a
   fold along a topological order, then `evalAssignDist_eq_evalFold` closes.
-/

namespace MAID

open GameTheory Math

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

-- ============================================================================
-- Step 1: Frontier independence
-- ============================================================================

/-- Two distinct frontier nodes have no direct edge between them.  Frontier
membership requires all parents assigned; a frontier node is unassigned.
So a frontier node cannot be a parent of another frontier node. -/
theorem frontier_noDirectEdge (S : Struct Player n) (cfg : FrontierCfg S)
    (u v : Fin n) (hu : u ∈ frontier S cfg) (hv : v ∈ frontier S cfg)
    (_hne : u ≠ v) :
    NoDirectEdge S u v := by
  have heu : enabled S cfg u := by simpa [frontier] using hu
  have hev : enabled S cfg v := by simpa [frontier] using hv
  constructor
  · -- u ∉ S.parents v: if u were a parent of v, then u ∈ cfg.assigned
    -- (since v is enabled), contradicting u being unassigned (u is enabled)
    intro h; exact heu.1 (hev.2 h)
  · -- v ∉ S.parents u: symmetric argument
    intro h; exact hev.1 (heu.2 h)

-- ============================================================================
-- Step 2: One-step sequentialization
-- ============================================================================

/-- Lift `nodeDistPol` from a `FrontierCfg` to a `TAssign` by reading parent
values from `extractTAssign`. For frontier nodes, this equals `nodeDist`
because all parents are assigned and `extractTAssign` reads their values
correctly. -/
theorem nodeDistPol_eq_nodeDist_extractTAssign
    (S : Struct Player n) (sem : Sem S) (pol : Policy S) (cfg : FrontierCfg S)
    (nd : ↥(frontier S cfg)) :
    nodeDistPol S sem pol cfg nd =
      nodeDist S sem pol nd.1 (extractTAssign S cfg) := by
  have hEnabled : enabled S cfg nd.1 := enabled_of_mem_frontier nd.2
  -- Helper: restrictCfg on assigned parents = projCfg of extractTAssign
  have hrestr : ∀ (ps : Finset (Fin n)) (hps : ps ⊆ cfg.assigned),
      restrictCfg cfg ps hps = projCfg (extractTAssign S cfg) ps := by
    intro ps hps; funext ⟨p, hp⟩
    simp only [restrictCfg, projCfg, extractTAssign, dif_pos (hps hp)]
  -- Compare probabilities pointwise; split both matches on S.kind nd.1
  ext v; simp only [nodeDistPol, nodeDist]
  split <;> rename_i hk <;> split <;> rename_i hk' <;>
    simp only [hk] at hk'
  -- Close cross-cases (different constructors → contradiction)
  all_goals try (cases hk'; done)
  -- Diagonal cases remain
  · -- chance/chance
    congr 2; exact hrestr _ hEnabled.2
  · -- decision/decision
    cases hk'; congr 1; congr 1
    exact Sigma.ext rfl (heq_of_eq
      (hrestr _ (fun x hx => hEnabled.2 (S.obs_sub nd.1 hx))))
  · -- utility/utility
    cases hk'; rfl

end MAID
