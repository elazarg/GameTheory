/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.DAG

/-!
# Multi-Decision Ownership for Open-Game Shapes

An ownership map groups node-indexed contingent plans into one strategy per
player. The induced NFG uses player-level deviations: one deviation replaces
every plan owned by that player.

For a transport-free API, a player strategy supplies a total stage profile;
realization reads only that player's owned coordinates. Off-owner coordinates
are semantically irrelevant. This redundant presentation avoids quotienting
proof-indexed products while preserving exactly the intended deviations.

`OwnedProfile` is the representation-independent core. `ShapeSeqDep` and
`ShapeDAG` expose thin specializations for sequential stages and sparse DAG
nodes. Player-form Nash is intentionally distinct from the shapes' nodewise
open-game equilibrium (agent-form Nash); the two coincide under injective
ownership but diverge in general.
-/

namespace OpenGames

/-! ## Representation-independent ownership -/

/-! Generic ownership operations for any dependent family of node plans.

The intentionally redundant player strategy gives each player a total node
profile; realization reads only the coordinates owned by that player. This is
the transport-free core shared by sequential and sparse-DAG presentations. -/
namespace OwnedProfile

variable {Node Player Outcome : Type} [DecidableEq Player]
variable {Plan : Node → Type}

/-- A player supplies a total plan profile; only owned coordinates are read. -/
abbrev PlayerStrategy (_owner : Node → Player) (Plan : Node → Type)
    (_player : Player) := ∀ node, Plan node

/-- Regroup a node-indexed profile into redundant player-indexed profiles. -/
def group (owner : Node → Player) (σ : ∀ node, Plan node) :
    ∀ player, PlayerStrategy owner Plan player :=
  fun _ => σ

/-- Recover the plan at each node from the profile supplied by its owner. -/
def ungroup (owner : Node → Player)
    (σ : ∀ player, PlayerStrategy owner Plan player) : ∀ node, Plan node :=
  fun node => σ (owner node) node

omit [DecidableEq Player] in
@[simp] theorem ungroup_group (owner : Node → Player)
    (σ : ∀ node, Plan node) : ungroup owner (group owner σ) = σ := rfl

/-- A single-node update is representable as a deviation by that node's
owner, even when the owner controls other nodes. -/
theorem ungroup_update_group [DecidableEq Node] (owner : Node → Player)
    (σ : ∀ node, Plan node) (node : Node) (deviation : Plan node) :
    ungroup owner
        (Function.update (group owner σ) (owner node)
          (group owner (Function.update σ node deviation) (owner node))) =
      Function.update σ node deviation := by
  funext other
  by_cases howner : owner other = owner node
  · simp [ungroup, group, Function.update, howner]
  · have hne : other ≠ node := by
      intro h
      exact howner (congrArg owner h)
    simp [ungroup, group, Function.update, howner, hne]

/-- Under injective ownership, every owner deviation changes at most one
node. -/
theorem ungroup_update_of_injective [DecidableEq Node]
    {owner : Node → Player} (howner : Function.Injective owner)
    (σ : ∀ node, Plan node) (node : Node) (deviation : ∀ node, Plan node) :
    ungroup owner (Function.update (group owner σ) (owner node) deviation) =
      Function.update σ node (deviation node) := by
  funext other
  by_cases hne : other = node
  · subst other
    simp [ungroup, Function.update]
  · have hownerNe : owner other ≠ owner node := by
      intro h
      exact hne (howner h)
    simp [ungroup, group, Function.update, hownerNe, hne]

/-- The NFG whose unilateral deviations replace all plans owned by one
player. -/
def ownedNFG (owner : Node → Player) (outcome : (∀ node, Plan node) → Outcome)
    (utility : Outcome → Player → ℝ) :
    NFG.NFGGame Player (PlayerStrategy owner Plan) where
  Outcome := Outcome
  outcome σ := outcome (ungroup owner σ)
  utility := utility

/-- Compile a representation-independent owned profile game. -/
noncomputable def compileOwned (owner : Node → Player)
    (outcome : (∀ node, Plan node) → Outcome)
    (utility : Outcome → Player → ℝ) : GameTheory.KernelGame Player :=
  (ownedNFG owner outcome utility).toKernelGame

/-- Player-form Nash under an ownership map. -/
def IsPlayerNash (owner : Node → Player)
    (outcome : (∀ node, Plan node) → Outcome)
    (utility : Outcome → Player → ℝ) (σ : ∀ node, Plan node) : Prop :=
  NFG.IsNashPure (ownedNFG owner outcome utility) (group owner σ)

/-- Agent-form equilibrium tests one node at a time with its owner's
utility. -/
def IsAgentEquilibrium [DecidableEq Node] (owner : Node → Player)
    (outcome : (∀ node, Plan node) → Outcome)
    (utility : Outcome → Player → ℝ) (σ : ∀ node, Plan node) : Prop :=
  ∀ node (deviation : Plan node),
    utility (outcome (Function.update σ node deviation)) (owner node) ≤
      utility (outcome σ) (owner node)

/-- Player-form Nash implies agent-form equilibrium for every owned profile
representation. -/
theorem IsPlayerNash.isAgentEquilibrium [DecidableEq Node]
    {owner : Node → Player} {outcome : (∀ node, Plan node) → Outcome}
    {utility : Outcome → Player → ℝ} {σ : ∀ node, Plan node}
    (hσ : IsPlayerNash owner outcome utility σ) :
    IsAgentEquilibrium owner outcome utility σ := by
  intro node deviation
  have hdev := hσ (owner node)
    (group owner (Function.update σ node deviation) (owner node))
  change
    utility (outcome (Function.update σ node deviation)) (owner node) ≤
      utility (outcome σ) (owner node)
  simpa [IsPlayerNash, ownedNFG, NFG.deviate,
    ungroup_update_group] using hdev

/-- Injective ownership identifies player-form and agent-form deviations for
an arbitrary dependent plan family. -/
theorem isAgentEquilibrium_iff_isPlayerNash_of_injective [DecidableEq Node]
    {owner : Node → Player} (howner : Function.Injective owner)
    (outcome : (∀ node, Plan node) → Outcome)
    (utility : Outcome → Player → ℝ) (σ : ∀ node, Plan node) :
    IsAgentEquilibrium owner outcome utility σ ↔
      IsPlayerNash owner outcome utility σ := by
  constructor
  · intro hσ player deviation
    change utility (outcome (ungroup owner
        (Function.update (group owner σ) player deviation))) player ≤
      utility (outcome σ) player
    by_cases hp : ∃ node, owner node = player
    · rcases hp with ⟨node, hnode⟩
      have hlocal := hσ node (deviation node)
      have hprofile : ungroup owner
          (Function.update (group owner σ) player deviation) =
          Function.update σ node (deviation node) := by
        rw [← hnode]
        exact ungroup_update_of_injective howner σ node deviation
      rw [hprofile, ← hnode]
      exact hlocal
    · have hprofile : ungroup owner
          (Function.update (group owner σ) player deviation) = σ := by
        funext node
        have hne : owner node ≠ player := by
          intro h
          exact hp ⟨node, h⟩
        simp [ungroup, group, Function.update, hne]
      rw [hprofile]
  · exact IsPlayerNash.isAgentEquilibrium

/-- Player-form Nash is exactly Nash of the generic compiled owned game. -/
theorem isPlayerNash_iff_kernelNash (owner : Node → Player)
    (outcome : (∀ node, Plan node) → Outcome)
    (utility : Outcome → Player → ℝ) (σ : ∀ node, Plan node) :
    IsPlayerNash owner outcome utility σ ↔
      (compileOwned owner outcome utility).IsNash (group owner σ) := by
  exact NFG.IsNashPure_iff_kernelGame (ownedNFG owner outcome utility)
    (group owner σ)

end OwnedProfile

/-! ## Sequential-shape specialization -/

namespace ShapeSeqDep

variable {n : Nat} {ι : Type} [DecidableEq ι]
variable {A : Fin n → Type}

/-- A player supplies a total plan profile; only owned coordinates are read. -/
abbrev PlayerStrategy (owner : Fin n → ι) (A : Fin n → Type) (p : ι) :=
  OwnedProfile.PlayerStrategy owner (fun i => History A i → A i) p

/-- Regroup stage-indexed plans into player-indexed strategies. -/
abbrev group (owner : Fin n → ι) (σ : Strategy A) :
    ∀ p, PlayerStrategy owner A p :=
  OwnedProfile.group owner σ

/-- Forget ownership grouping and recover the plan at each stage. -/
abbrev ungroup (owner : Fin n → ι)
    (σ : ∀ p, PlayerStrategy owner A p) : Strategy A :=
  OwnedProfile.ungroup owner σ

omit [DecidableEq ι] in
@[simp] theorem ungroup_group (owner : Fin n → ι) (σ : Strategy A) :
    ungroup owner (group owner σ) = σ :=
  OwnedProfile.ungroup_group owner σ

/-- Replacing the strategy of `owner i` by a regrouped single-stage update
has exactly the intended stage-level effect. -/
theorem ungroup_update_group (owner : Fin n → ι) (σ : Strategy A)
    (i : Fin n) (deviation : History A i → A i) :
    ungroup owner
        (Function.update (group owner σ) (owner i)
          (group owner (Function.update σ i deviation) (owner i))) =
      Function.update σ i deviation :=
  OwnedProfile.ungroup_update_group owner σ i deviation

/-- With at most one stage per owner, an owner-level deviation is exactly the
corresponding single-stage update. -/
theorem ungroup_update_of_injective {owner : Fin n → ι}
    (howner : Function.Injective owner) (σ : Strategy A) (i : Fin n)
    (deviation : Strategy A) :
    ungroup owner
        (Function.update (group owner σ) (owner i) deviation) =
      Function.update σ i (deviation i) :=
  OwnedProfile.ungroup_update_of_injective howner σ i deviation

/-- The strategic-form game whose deviations replace every plan owned by one
player. -/
def ownedNFG (owner : Fin n → ι) (A : Fin n → Type)
    (u : (∀ i, A i) → ι → ℝ) :
    NFG.NFGGame ι (PlayerStrategy owner A) :=
  OwnedProfile.ownedNFG owner realize u

/-- Compile the player-form sequential game through the existing NFG bridge. -/
noncomputable def compileOwned (owner : Fin n → ι) (A : Fin n → Type)
    (u : (∀ i, A i) → ι → ℝ) : GameTheory.KernelGame ι :=
  OwnedProfile.compileOwned owner realize u

/-- Player-form Nash for a stage profile under an ownership map. -/
def IsPlayerNash (owner : Fin n → ι) (u : (∀ i, A i) → ι → ℝ)
    (σ : Strategy A) : Prop :=
  OwnedProfile.IsPlayerNash owner realize u σ

/-- Agent-form equilibrium tests one owned decision at a time, using its
owner's utility. -/
def IsAgentEquilibrium (owner : Fin n → ι)
    (u : (∀ i, A i) → ι → ℝ) (σ : Strategy A) : Prop :=
  OwnedProfile.IsAgentEquilibrium owner realize u σ

/-- Player-form Nash implies agent-form equilibrium: every single-stage
deviation is a special case of replacing all plans owned by that player. -/
theorem IsPlayerNash.isAgentEquilibrium {owner : Fin n → ι}
    {u : (∀ i, A i) → ι → ℝ} {σ : Strategy A}
    (hσ : IsPlayerNash owner u σ) :
    IsAgentEquilibrium owner u σ :=
  OwnedProfile.IsPlayerNash.isAgentEquilibrium hσ

/-- If no player owns two stages, agent-form and player-form deviations
coincide. Unowned players are harmless because their total plan coordinates
are never read. -/
theorem isAgentEquilibrium_iff_isPlayerNash_of_injective
    {owner : Fin n → ι} (howner : Function.Injective owner)
    (u : (∀ i, A i) → ι → ℝ) (σ : Strategy A) :
    IsAgentEquilibrium owner u σ ↔ IsPlayerNash owner u σ :=
  OwnedProfile.isAgentEquilibrium_iff_isPlayerNash_of_injective
    howner realize u σ

/-- Player-form Nash is exactly Nash in the compiled kernel game. -/
theorem isPlayerNash_iff_kernelNash (owner : Fin n → ι)
    (u : (∀ i, A i) → ι → ℝ) (σ : Strategy A) :
    IsPlayerNash owner u σ ↔
      (compileOwned owner A u).IsNash (group owner σ) :=
  OwnedProfile.isPlayerNash_iff_kernelNash owner realize u σ

end ShapeSeqDep
end OpenGames

/-! ## Sparse-DAG specialization -/

namespace OpenGames.ShapeDAG

variable {n : Nat} {Player : Type} [DecidableEq Player]
variable {A : Fin n → Type}

/-- The player-form strategic game of a sparse decision DAG. A unilateral
deviation replaces every node plan owned by that player. -/
def ownedNFG (D : DecisionDAG n) (owner : Fin n → Player)
    (A : Fin n → Type) (utility : (∀ i, A i) → Player → ℝ) :
    NFG.NFGGame Player
      (OwnedProfile.PlayerStrategy owner
        (fun i => History D A i → A i)) :=
  OwnedProfile.ownedNFG owner (realize D) utility

/-- Compile sparse-DAG player-form deviations to the common kernel game. -/
noncomputable def compileOwned (D : DecisionDAG n)
    (owner : Fin n → Player) (A : Fin n → Type)
    (utility : (∀ i, A i) → Player → ℝ) : GameTheory.KernelGame Player :=
  OwnedProfile.compileOwned owner (realize D) utility

/-- Player-form Nash for a sparse DAG under a node-ownership map. -/
def IsPlayerNash (D : DecisionDAG n) (owner : Fin n → Player)
    (utility : (∀ i, A i) → Player → ℝ) (σ : Strategy D A) : Prop :=
  OwnedProfile.IsPlayerNash owner (realize D) utility σ

/-- Agent-form equilibrium tests one DAG decision node at a time. -/
def IsAgentEquilibrium (D : DecisionDAG n) (owner : Fin n → Player)
    (utility : (∀ i, A i) → Player → ℝ) (σ : Strategy D A) : Prop :=
  OwnedProfile.IsAgentEquilibrium owner (realize D) utility σ

omit [DecidableEq Player] in
/-- The generic agent-form ownership predicate is definitionally the plain
sparse open-game equilibrium with each node evaluated by its owner's utility. -/
theorem isAgentEquilibrium_iff_openGame (D : DecisionDAG n)
    (owner : Fin n → Player) (utility : (∀ i, A i) → Player → ℝ)
    (σ : Strategy D A) :
    IsAgentEquilibrium D owner utility σ ↔
      (OpenGames.ShapeDAG D A).IsEquilibriumIn ()
        (fun path i => utility path (owner i)) σ :=
  Iff.rfl

/-- Player-form Nash implies the sparse open game's nodewise agent-form
equilibrium. -/
theorem IsPlayerNash.isAgentEquilibrium {D : DecisionDAG n}
    {owner : Fin n → Player} {utility : (∀ i, A i) → Player → ℝ}
    {σ : Strategy D A} (hσ : IsPlayerNash D owner utility σ) :
    IsAgentEquilibrium D owner utility σ :=
  OwnedProfile.IsPlayerNash.isAgentEquilibrium hσ

/-- If no player owns two DAG nodes, player-form and agent-form deviations
coincide. -/
theorem isAgentEquilibrium_iff_isPlayerNash_of_injective
    {D : DecisionDAG n} {owner : Fin n → Player}
    (howner : Function.Injective owner)
    (utility : (∀ i, A i) → Player → ℝ) (σ : Strategy D A) :
    IsAgentEquilibrium D owner utility σ ↔
      IsPlayerNash D owner utility σ :=
  OwnedProfile.isAgentEquilibrium_iff_isPlayerNash_of_injective
    howner (realize D) utility σ

/-- Sparse-DAG player-form Nash is exactly Nash in its compiled kernel game. -/
theorem isPlayerNash_iff_kernelNash (D : DecisionDAG n)
    (owner : Fin n → Player) (utility : (∀ i, A i) → Player → ℝ)
    (σ : Strategy D A) :
    IsPlayerNash D owner utility σ ↔
      (compileOwned D owner A utility).IsNash
        (OwnedProfile.group owner σ) :=
  OwnedProfile.isPlayerNash_iff_kernelNash owner (realize D) utility σ

end OpenGames.ShapeDAG

/-! ## Strict agent-form/player-form separation -/

namespace OpenGames.ShapeSeqDep.OwnershipExample

/-- Both stages are owned by the same player. -/
def owner : Fin 2 → Unit := fun _ => ()

/-- The baseline plan chooses `false` at both stages and histories. -/
def allFalse : Strategy (fun _ : Fin 2 => Bool) :=
  fun _ _ => false

/-- A joint deviation choosing `true` at both stages. -/
def allTrue : Strategy (fun _ : Fin 2 => Bool) :=
  fun _ _ => true

/-- The sole player is rewarded only when both realized actions are true. -/
def utility (path : Fin 2 → Bool) (_ : Unit) : ℝ :=
  if path 0 && path 1 then 1 else 0

@[simp] theorem realize_allFalse (i : Fin 2) :
    realize allFalse i = false := by
  change realizeAt allFalse i = false
  rw [realizeAt]
  rfl

@[simp] theorem realize_allTrue (i : Fin 2) :
    realize allTrue i = true := by
  change realizeAt allTrue i = true
  rw [realizeAt]
  rfl

theorem realize_update_allFalse_of_ne (i j : Fin 2)
    (deviation : History (fun _ : Fin 2 => Bool) i → Bool)
    (hji : j ≠ i) :
    realize (Function.update allFalse i deviation) j = false := by
  change realizeAt (Function.update allFalse i deviation) j = false
  rw [realizeAt, Function.update_of_ne hji]
  rfl

/-- The all-false profile is stable against every one-stage deviation. -/
theorem allFalse_isAgentEquilibrium :
    IsAgentEquilibrium owner utility allFalse := by
  intro i deviation
  fin_cases i
  · have hlater := realize_update_allFalse_of_ne 0 1 deviation (by decide)
    simp [utility, hlater]
  · have hearlier := realize_update_allFalse_of_ne 1 0 deviation (by decide)
    simp [utility, hearlier]

/-- The same profile is not player-form Nash: its single owner can change both
plans jointly and reach `(true, true)`. -/
theorem allFalse_not_isPlayerNash :
    ¬IsPlayerNash owner utility allFalse := by
  intro h
  have hdev := h () allTrue
  have hprofile :
      ungroup owner (Function.update (group owner allFalse) () allTrue) =
        allTrue := by
    funext i history
    simp [ungroup, group, OwnedProfile.ungroup, owner]
  change
    utility (realize
      (ungroup owner
        (Function.update (group owner allFalse) () allTrue))) () ≤
      utility (realize (ungroup owner (group owner allFalse))) () at hdev
  rw [hprofile, ungroup_group] at hdev
  norm_num [utility] at hdev

/-- Multi-decision ownership strictly separates agent-form equilibrium from
player-form Nash. -/
theorem agentForm_not_playerForm :
    IsAgentEquilibrium owner utility allFalse ∧
      ¬IsPlayerNash owner utility allFalse :=
  ⟨allFalse_isAgentEquilibrium, allFalse_not_isPlayerNash⟩

end OpenGames.ShapeSeqDep.OwnershipExample
