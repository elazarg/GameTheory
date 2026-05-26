/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Math.Probability

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
- `CausalWith` — information of agent κ⋆ depends only on predecessors'
  decisions for a fixed configuration-ordering
-/

namespace Intrinsic

open Math.Probability

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

/-- An outcome law maps each state of nature to a distribution over complete
    decision profiles. This is the outcome object compared by W-game
    preferences in the paper. -/
abbrev OutcomeLaw (M : WModel) : Type := M.Ω → PMF (∀ a : M.A, M.U a)

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

/-- A valid ordering prefix: a nodup list of agents. It may or may not be
    realized as an initial segment at a particular configuration. -/
def OrderingPrefix (M : WModel) := { l : List M.A // l.Nodup }

namespace OrderingPrefix

/-- Agents before the last element of a nonempty prefix. -/
def predecessors {M : WModel} (κ : OrderingPrefix M) : Finset M.A :=
  κ.val.dropLast.toFinset

/-- The final agent of a nonempty prefix. -/
def last {M : WModel} (κ : OrderingPrefix M) (hne : κ.val ≠ []) : M.A :=
  κ.val.getLast hne

end OrderingPrefix

/-- Given a configuration-ordering `ϕ` and a prefix `κ` (a list of agents),
    the set of configurations where the first `|κ|` agents in `ϕ(h)`
    match `κ` (equation 17). -/
def configSet (M : WModel) (ϕ : ConfigOrdering M) (κ : OrderingPrefix M) :
    Set M.H :=
  { h | (ϕ h).val.take κ.val.length = κ.val }

/-- Two configurations agree on nature and on the decisions of agents
    in the set `B` (captures the sub-σ-field `H_B`, equation 9b). -/
def agreeOnSubset (M : WModel) (B : Finset M.A) (h h' : M.H) : Prop :=
  h.nature = h'.nature ∧ ∀ a ∈ B, h.decision a = h'.decision a

/-- The coordinate-agreement setoid for `H_B`: two configurations agree on
    nature and on all decision coordinates in `B`. -/
def coordinateAgreeSetoid (M : WModel) (B : Finset M.A) : Setoid M.H where
  r := agreeOnSubset M B
  iseqv := {
    refl := fun _ => ⟨rfl, fun _ _ => rfl⟩
    symm := fun h => ⟨h.1.symm, fun a ha => (h.2 a ha).symm⟩
    trans := fun h₁ h₂ =>
      ⟨h₁.1.trans h₂.1, fun a ha => (h₁.2 a ha).trans (h₂.2 a ha)⟩
  }

/-- A W-model is causal with respect to a fixed configuration-ordering `ϕ`
    if, for any nonempty ordering prefix `κ`, agreement on nature and on the
    predecessor decisions implies that the last agent `κ⋆` has the same
    information atom on `H^ϕ_κ` (Definition 6).

    Informally: when agent `κ⋆` is called to play, what they know cannot
    depend on decisions of agents that are not their predecessors. -/
def CausalWith (M : WModel) (ϕ : ConfigOrdering M) : Prop :=
  ∀ (κ : OrderingPrefix M) (hne : κ.val ≠ []),
    let predecessors : Finset M.A := κ.predecessors
    let last := κ.last hne
    ∀ h h' : M.H,
      h ∈ configSet M ϕ κ →
      h' ∈ configSet M ϕ κ →
      agreeOnSubset M predecessors h h' →
      (M.info last).r h h'

-- ============================================================================
-- W-Games (Definition 7)
-- ============================================================================

/-- A finite game in intrinsic form (W-game), Definition 7.

    Extends a W-model with:
    - A partition of agents into players
    - A nonempty ownership condition for every player
    - Preferences over outcome laws -/
structure WGame extends WModel where
  /-- Finite set of players. -/
  P : Type
  [finP : Fintype P]
  [decP : DecidableEq P]
  /-- Assignment of each agent to a player (the sets `Aₚ`). -/
  owner : A → P
  /-- Every player owns at least one agent. -/
  owner_nonempty : ∀ p : P, ∃ a : A, owner a = p
  /-- Preference relation over outcome laws. -/
  pref : P → (Ω → PMF (∀ a : A, U a)) →
    (Ω → PMF (∀ a : A, U a)) → Prop

attribute [instance] WGame.finP WGame.decP

/-- The set of agents belonging to player `p`. -/
def WGame.agents (G : WGame) (p : G.P) : Finset G.A :=
  Finset.univ.filter (fun a => G.owner a = p)

-- ============================================================================
-- Expected-utility W-games
-- ============================================================================

/-- A convenience wrapper for expected-utility intrinsic games. The paper-level
    `WGame` only needs preferences over outcome laws; this wrapper carries the
    utility/prior data used by the library's `KernelGame` compiler. -/
structure EUWGame extends WModel where
  /-- Finite set of players. -/
  P : Type
  [finP : Fintype P]
  [decP : DecidableEq P]
  /-- Assignment of each agent to a player. -/
  owner : A → P
  /-- Every player owns at least one agent. -/
  owner_nonempty : ∀ p : P, ∃ a : A, owner a = p
  /-- Utility function for each player, defined on configurations. -/
  utility : P → Config Ω A U → ℝ
  /-- Prior distribution over states of nature. -/
  prior : PMF Ω

attribute [instance] EUWGame.finP EUWGame.decP

/-- The distribution over full configurations induced by an outcome law and
    the expected-utility wrapper's prior. -/
noncomputable def EUWGame.configLaw (G : EUWGame)
    (law : OutcomeLaw G.toWModel) : PMF G.toWModel.H :=
  G.prior.bind (fun ω => (law ω).map (fun u => ⟨ω, u⟩))

/-- Expected utility of an outcome law for player `p`. -/
noncomputable def EUWGame.expectedUtilityLaw (G : EUWGame) (p : G.P)
    (law : OutcomeLaw G.toWModel) : ℝ :=
  expect (G.configLaw law) (fun h => G.utility p h)

/-- Forget expected-utility data to the paper-level W-game, using expected
    utility to induce preferences over outcome laws. -/
noncomputable def EUWGame.toWGame (G : EUWGame) : WGame :=
  { G.toWModel with
    P := G.P
    owner := G.owner
    owner_nonempty := G.owner_nonempty
    pref := fun p law law' =>
      G.expectedUtilityLaw p law ≤ G.expectedUtilityLaw p law' }

end Intrinsic
