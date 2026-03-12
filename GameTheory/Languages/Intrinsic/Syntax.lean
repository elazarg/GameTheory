import Mathlib.Data.Fintype.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Games in Intrinsic Form (W-Games)

Formalization of Witsenhausen's intrinsic model adapted to games,
following Heymann–De Lara–Chancelier (2020).

## Key ideas

The intrinsic form replaces the tree structure of extensive-form games
with a **product structure**. Each agent is equipped with a decision set
and an information equivalence relation on the configuration space
`H = Ω × ∏ₐ Uₐ`. Strategies are functions from configurations to
decisions that are measurable w.r.t. the agent's information (i.e.,
constant on equivalence classes).

There is no hardcoded temporal ordering — the time arrow emerges from
the information structure via the causality property.

## Main definitions

- `WModel` — Witsenhausen's intrinsic model: agents, nature, decisions,
  information equivalence relations
- `WGame` — a W-model extended with players and preference relations
- `PureStrategy` — information-measurable decision function for one agent
- `PureProfile` — a family of pure strategies, one per agent
- `Solvable` — unique solution to the closed-loop equations
- `ConfigOrdering` — a configuration-dependent ordering of agents
- `Causal` — information of agent κ⋆ depends only on predecessors' decisions
-/

namespace Intrinsic

-- ============================================================================
-- Configuration space
-- ============================================================================

/-- The configuration space `H = Ω × ∏ₐ Uₐ`. A configuration bundles a
    state of nature with all agents' decisions. -/
structure Config (Ω : Type) (A : Type) (U : A → Type) where
  /-- State of nature. -/
  nature : Ω
  /-- Decision of each agent. -/
  decision : ∀ a : A, U a

instance {Ω A : Type} {U : A → Type} [Fintype Ω] [DecidableEq A] [Fintype A]
    [∀ a, Fintype (U a)] : Fintype (Config Ω A U) :=
  Fintype.ofEquiv (Ω × (∀ a, U a))
    { toFun := fun ⟨ω, u⟩ => ⟨ω, u⟩
      invFun := fun c => ⟨c.nature, c.decision⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }

-- ============================================================================
-- Witsenhausen's intrinsic model (finite case)
-- ============================================================================

/-- A finite Witsenhausen model (W-model), Definition 1 of the paper.

    - `A` : finite set of agents
    - `Ω` : finite set of states of nature
    - `U a` : finite decision set for agent `a`
    - `info a` : information equivalence relation for agent `a` on the
      configuration space `H = Ω × ∏ₐ Uₐ`

    The information field `Iₐ` of the paper (a sub-σ-field of the product
    field) corresponds, in the finite case, to the partition induced by
    `info a`. Two configurations are equivalent iff they belong to the
    same atom of `Iₐ`. -/
structure WModel where
  /-- Finite set of agents. -/
  A : Type
  [finA : Fintype A]
  [decA : DecidableEq A]
  /-- Finite set of states of nature. -/
  Ω : Type
  [finΩ : Fintype Ω]
  /-- Finite decision set for each agent. -/
  U : A → Type
  [finU : ∀ a, Fintype (U a)]
  [neU : ∀ a, Nonempty (U a)]
  /-- Information equivalence relation for agent `a` on the configuration
      space. Two configurations are `info a`-equivalent iff they belong
      to the same atom of agent `a`'s information field. -/
  info : A → Setoid (Config Ω A U)

attribute [instance] WModel.finA WModel.decA WModel.finΩ WModel.finU
  WModel.neU

/-- The configuration space of a W-model. -/
abbrev WModel.H (M : WModel) : Type := Config M.Ω M.A M.U

-- ============================================================================
-- Pure strategies and profiles
-- ============================================================================

/-- A pure W-strategy for agent `a`: a function from configurations to
    decisions that is measurable w.r.t. the agent's information field.
    Measurability means the function is constant on equivalence classes
    (Proposition 2, condition 4b). -/
structure PureStrategy (M : WModel) (a : M.A) where
  /-- The decision function. -/
  act : M.H → M.U a
  /-- Measurability: equivalent configurations yield the same decision. -/
  meas : ∀ h h' : M.H, (M.info a).r h h' → act h = act h'

/-- A pure W-strategy profile: one pure strategy per agent. -/
abbrev PureProfile (M : WModel) : Type := ∀ a : M.A, PureStrategy M a

-- ============================================================================
-- Solvability
-- ============================================================================

/-- The closed-loop equations (15a): given nature state `ω` and strategy
    profile `strat`, a decision profile `u` is a **fixed point** when
    `u a = strat_a(ω, u)` for all agents `a`. -/
def isFixedPoint (M : WModel) (strat : PureProfile M) (ω : M.Ω)
    (u : ∀ a, M.U a) : Prop :=
  ∀ a, u a = (strat a).act ⟨ω, u⟩

/-- A W-model is **solvable** if for every pure strategy profile and every
    state of nature, the closed-loop equations have exactly one solution
    (Definition 4). -/
def Solvable (M : WModel) : Prop :=
  ∀ (strat : PureProfile M) (ω : M.Ω), ∃! u : (∀ a, M.U a),
    isFixedPoint M strat ω u

/-- The solution map `M_λ(ω)` (equation 15b): given solvability, the unique
    decision profile solving the closed-loop equations. -/
noncomputable def solutionMap (M : WModel) (hsolv : Solvable M)
    (strat : PureProfile M) (ω : M.Ω) : ∀ a, M.U a :=
  (hsolv strat ω).choose

theorem solutionMap_spec (M : WModel) (hsolv : Solvable M)
    (strat : PureProfile M) (ω : M.Ω) :
    isFixedPoint M strat ω (solutionMap M hsolv strat ω) :=
  (hsolv strat ω).choose_spec.1

theorem solutionMap_unique (M : WModel) (hsolv : Solvable M)
    (strat : PureProfile M) (ω : M.Ω) (u : ∀ a, M.U a)
    (hu : isFixedPoint M strat ω u) :
    u = solutionMap M hsolv strat ω := by
  unfold solutionMap
  exact (hsolv strat ω).choose_spec.2 u hu

-- ============================================================================
-- Configuration-orderings and causality
-- ============================================================================

/-- A total ordering of all agents: a list that is a permutation covering
    every agent exactly once. -/
def TotalOrdering (M : WModel) :=
  { l : List M.A // l.Nodup ∧ ∀ a, a ∈ l }

/-- A configuration-ordering maps each configuration to a total ordering
    of agents (Definition 5). -/
def ConfigOrdering (M : WModel) := M.H → TotalOrdering M

/-- Given a configuration-ordering `ϕ` and a prefix `κ` (a list of agents),
    the set of configurations where the first `|κ|` agents in `ϕ(h)`
    match `κ` (equation 17). -/
def configSet (M : WModel) (ϕ : ConfigOrdering M) (κ : List M.A) :
    Set M.H :=
  { h | (ϕ h).val.take κ.length = κ }

/-- Two configurations agree on nature and on the decisions of agents
    in the set `B` (captures the sub-σ-field `H_B`, equation 9b). -/
def agreeOnSubset (M : WModel) (B : Finset M.A) (h h' : M.H) : Prop :=
  h.nature = h'.nature ∧ ∀ a ∈ B, h.decision a = h'.decision a

/-- A W-model is **causal** if there exists a configuration-ordering such
    that for any ordering prefix `κ`, the information of the last agent
    `κ⋆` refines `H_{‖κ⁻‖}` on the set `H^ϕ_κ` (Definition 6).

    Informally: when agent `κ⋆` is called to play, what they know cannot
    depend on decisions of agents that are not their predecessors. -/
def Causal (M : WModel) : Prop :=
  ∃ ϕ : ConfigOrdering M,
    ∀ (κ : List M.A) (hne : κ ≠ []),
      let predecessors : Finset M.A := κ.dropLast.toFinset
      let last := κ.getLast hne
      ∀ h h' : M.H,
        h ∈ configSet M ϕ κ →
        h' ∈ configSet M ϕ κ →
        (M.info last).r h h' →
        agreeOnSubset M predecessors h h'

-- /-- Causality implies solvability (Witsenhausen's result).
--     In a causal W-model, the closed-loop equations can be solved
--     sequentially following the configuration-ordering. -/
-- theorem causal_implies_solvable (M : WModel) (hc : Causal M) :
--     Solvable M := by
--   sorry

-- ============================================================================
-- W-Games (Definition 7)
-- ============================================================================

/-- A finite game in intrinsic form (W-game), Definition 7.

    Extends a W-model with:
    - A partition of agents into players
    - Utility functions and a prior over Ω -/
structure WGame extends WModel where
  /-- Finite set of players. -/
  P : Type
  [finP : Fintype P]
  [decP : DecidableEq P]
  /-- Assignment of each agent to a player (the sets `Aₚ`). -/
  owner : A → P
  /-- Utility function for each player, defined on configurations. -/
  utility : P → Config Ω A U → ℝ
  /-- Prior distribution over states of nature. -/
  prior : PMF Ω

attribute [instance] WGame.finP WGame.decP

/-- The set of agents belonging to player `p`. -/
def WGame.agents (G : WGame) (p : G.P) : Finset G.A :=
  Finset.univ.filter (fun a => G.owner a = p)

end Intrinsic
