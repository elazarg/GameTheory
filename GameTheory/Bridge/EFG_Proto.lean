import GameTheory.Protocol.ProtoZermelo
import GameTheory.EFG.Refinements

/-!
# EFG → Protocol Encoding

Encodes extensive-form games into the Protocol abstraction.

## Encoding design

- **State** = `GameTree S Outcome` (the current subtree)
- **View** = `GameTree S Outcome` (full state as view — gives perfect info)
- **Action** = `ℕ` (universal action index, interpreted modulo arity)
- **Signal** = `ℕ` (for chance branches: broadcasts branch index to all players)

At each round, the state is the current subtree:
- Terminal nodes are absorbing (state doesn't change)
- Decision nodes: the active player submits an action (mod arity), advancing the tree
- Chance nodes: the signal draws a branch from the chance distribution

The `depth`-many identical rounds handle all tree levels.

## Main definitions

- `GameTree.treeDepth` — tree depth (longest root-to-terminal path)
- `efgRound` — the generic one-step round
- `EFGGame.toProtocol` — Protocol with `treeDepth` rounds
- `EFGGame.pureToProto` — strategy correspondence (EFG → Protocol)

## Theorems (sorry'd, to be filled from existing proofs)

- `EFGGame.toProtocol_perfectInfo` — PI transfers
- `EFGGame.toProtocol_sequential` — sequential property
- `EFGGame.proto_zermelo` — Zermelo for EFG via Protocol

-/

namespace EFG

open GameTheory

-- ============================================================================
-- Tree depth
-- ============================================================================

/-- Depth of a game tree: longest path from root to a terminal node. -/
noncomputable def GameTree.treeDepth {S : InfoStructure} {Outcome : Type} :
    GameTree S Outcome → Nat
  | .terminal _ => 0
  | .chance k _μ _hk next =>
      Finset.sup Finset.univ (fun (b : Fin k) => (next b).treeDepth) + 1
  | .decision (p := _) I next =>
      Finset.sup Finset.univ (fun (a : S.Act I) => (next a).treeDepth) + 1

-- ============================================================================
-- The one-step round
-- ============================================================================

/-- The generic one-step round for an EFG.
    - Signal: at chance nodes, draws a branch from the distribution (broadcast
      as ℕ to all players). At other nodes, trivial.
    - View: the full state (= GameTree). Gives perfect information.
    - Transition: at decision nodes, reads the active player's action (mod arity).
      At chance nodes, reads player 0's action as the relayed branch index.
      At terminal nodes, absorbing. -/
noncomputable def efgRound (inf : InfoStructure) (Outcome : Type)
    [NeZero inf.n] :
    Round inf.n (GameTree inf Outcome) (GameTree inf Outcome × ℕ) ℕ ℕ where
  signal state :=
    match state with
    | .chance _k μ _hk _next =>
        μ.map (fun b => fun _ => b.val)
    | _ => PMF.pure (fun _ => 0)
  view _i state sig := (state, sig)
  transition state acts :=
    match state with
    | .terminal z => .terminal z
    | .chance k _μ hk next =>
        -- Read player 0's action as the relayed branch index
        let b := (acts ⟨0, NeZero.pos inf.n⟩).getD 0
        next ⟨b % k, Nat.mod_lt b hk⟩
    | .decision (p := p) I next =>
        match acts p with
        | some a => next ⟨a % (inf.arity p I), Nat.mod_lt a (inf.arity_pos p I)⟩
        | none => next ⟨0, inf.arity_pos p I⟩

-- ============================================================================
-- Protocol construction
-- ============================================================================

/-- Protocol encoding of an EFG game: `treeDepth` copies of `efgRound`. -/
noncomputable def EFGGame.toProtocol (G : EFGGame)
    [NeZero G.inf.n] :
    Protocol G.inf.n (GameTree G.inf G.Outcome)
      (GameTree G.inf G.Outcome × ℕ) ℕ ℕ where
  init := G.tree
  rounds := List.replicate G.tree.treeDepth (efgRound G.inf G.Outcome)

-- ============================================================================
-- Strategy correspondence
-- ============================================================================

open Classical in
/-- Convert an EFG pure profile to a Protocol pure profile.
    At a decision node for player `i` with info-set `I`, submits the
    action index from the EFG strategy. At chance nodes, relays the
    signal (branch index) as the action. Otherwise, returns `none`. -/
noncomputable def EFGGame.pureToProto (G : EFGGame)
    (σ : PureProfile G.inf) :
    GameTheory.PureProfile G.inf.n (GameTree G.inf G.Outcome × ℕ) ℕ :=
  fun i view =>
    match view.1 with
    | .decision (p := p) I _next =>
        if h : p = i then
          have I' : G.inf.Infoset i := h ▸ I
          some (σ i I').val
        else none
    | .chance _ _ _ _ => some view.2  -- relay the signal
    | .terminal _ => none

-- ============================================================================
-- Utility on Protocol state space
-- ============================================================================

/-- Utility function on the Protocol state space: extracts outcome from
    terminal nodes; non-terminal nodes get 0 utility. -/
noncomputable def EFGGame.protoUtility (G : EFGGame) :
    GameTree G.inf G.Outcome → Fin G.inf.n → ℝ
  | .terminal z => G.utility z
  | _ => fun _ => 0

-- ============================================================================
-- Perfect information
-- ============================================================================

set_option linter.unusedFintypeInType false in
/-- The Protocol encoding of a perfect-info EFG satisfies `Protocol.IsPerfectInfo`:
    since the view is the full state, equal views imply equal states. -/
theorem EFGGame.toProtocol_perfectInfo (G : EFGGame)
    [NeZero G.inf.n]
    (_hPI : IsPerfectInfo G.tree) :
    G.toProtocol.IsPerfectInfo := by
  intro r hr i s₁ s₂ sig₁ sig₂ hview
  -- r ∈ replicate _ (efgRound ...) → r = efgRound ...
  have : r = efgRound G.inf G.Outcome := List.eq_of_mem_replicate hr
  subst this
  -- Now view unfolds: (s₁, sig₁ i) = (s₂, sig₂ i)
  exact (Prod.mk.inj hview).1

-- ============================================================================
-- Sequential property
-- ============================================================================

set_option linter.unusedFintypeInType false in
/-- The Protocol encoding is sequential: at each state, at most one player's
    action affects the transition. At decision nodes, only the active player
    matters. At terminal/chance nodes, either no actions matter or only
    the relay player matters. -/
theorem EFGGame.toProtocol_sequential (G : EFGGame)
    [NeZero G.inf.n] :
    G.toProtocol.IsSequential := by
  intro r hr s
  have hr_eq : r = efgRound G.inf G.Outcome := List.eq_of_mem_replicate hr
  subst hr_eq
  match s with
  | .terminal z =>
    exact ⟨⟨0, NeZero.pos G.inf.n⟩, fun j _ _sig acts a' => rfl⟩
  | .chance k μ hk next =>
    refine ⟨⟨0, NeZero.pos G.inf.n⟩, fun j hj _sig acts a' => ?_⟩
    simp only [efgRound]
    congr 1
    congr 3
    exact Function.update_of_ne (Ne.symm hj) a' acts
  | .decision (p := p) I next =>
    refine ⟨p, fun j hj _sig acts a' => ?_⟩
    simp only [efgRound]
    congr 1
    exact Function.update_of_ne (Ne.symm hj) a' acts

-- ============================================================================
-- Corollary: Zermelo for EFG
-- ============================================================================

-- **Note**: Zermelo for EFG via Protocol requires a finite-action encoding.
-- The current encoding uses `ℕ` as the universal action type, which is not finite.
-- `Protocol.zermelo` requires `[Fintype A]`.
--
-- The EFG-specific Zermelo theorem is available directly in `EFGRefinements.lean`.
-- A finite-action Protocol encoding (using `Fin (maxArity)` instead of `ℕ`) would
-- enable this corollary.

-- ============================================================================
-- Corollary: ODP for EFG
-- ============================================================================

set_option linter.unusedFintypeInType false in
/-- The one-shot deviation principle for EFG via Protocol encoding:
    under ViewSeparated conditions, SPE ↔ no one-shot deviation. -/
theorem EFGGame.proto_odp (G : EFGGame)
    [NeZero G.inf.n]
    [Fintype (GameTree G.inf G.Outcome)]
    (σ : GameTheory.PureProfile G.inf.n (GameTree G.inf G.Outcome × ℕ) ℕ)
    (hVS : G.toProtocol.ViewSeparated) :
    G.toProtocol.IsSubgamePerfect G.protoUtility σ ↔
      G.toProtocol.HasNoOneShotDeviation G.protoUtility σ :=
  G.toProtocol.odp G.protoUtility σ hVS

end EFG
