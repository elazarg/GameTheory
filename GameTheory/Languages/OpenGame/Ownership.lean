/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Sequential

/-!
# Multi-Decision Ownership for Sequential Shapes

An ownership map `owner : Fin n → ι` groups the stage-indexed contingent plans
of `ShapeSeqDep` into one strategy per player. The induced NFG uses
player-level deviations: one deviation replaces every contingent plan owned
by that player.

For a transport-free API, a player strategy supplies a total stage profile;
realization reads only that player's owned coordinates. Off-owner coordinates
are semantically irrelevant. This redundant presentation avoids quotienting
proof-indexed products while preserving exactly the intended deviations.

This is intentionally distinct from `ShapeSeqDep`'s open-game equilibrium,
which tests one stage at a time.  The former is player-form Nash; the latter is
agent-form Nash.  The definitions below make the boundary available without
silently identifying the two notions.
-/

namespace OpenGames.ShapeSeqDep

variable {n : Nat} {ι : Type} [DecidableEq ι]
variable {A : Fin n → Type}

/-- A player supplies a total plan profile; only owned coordinates are read. -/
abbrev PlayerStrategy (_owner : Fin n → ι) (A : Fin n → Type) (_p : ι) :=
  Strategy A

/-- Regroup stage-indexed plans into player-indexed strategies. -/
def group (owner : Fin n → ι) (σ : Strategy A) :
    ∀ p, PlayerStrategy owner A p :=
  fun _p => σ

/-- Forget ownership grouping and recover the plan at each stage. -/
def ungroup (owner : Fin n → ι)
    (σ : ∀ p, PlayerStrategy owner A p) : Strategy A :=
  fun i => σ (owner i) i

omit [DecidableEq ι] in
@[simp] theorem ungroup_group (owner : Fin n → ι) (σ : Strategy A) :
    ungroup owner (group owner σ) = σ := rfl

/-- Replacing the strategy of `owner i` by a regrouped single-stage update
has exactly the intended stage-level effect. -/
theorem ungroup_update_group (owner : Fin n → ι) (σ : Strategy A)
    (i : Fin n) (deviation : History A i → A i) :
    ungroup owner
        (Function.update (group owner σ) (owner i)
          (group owner (Function.update σ i deviation) (owner i))) =
      Function.update σ i deviation := by
  funext j h
  by_cases howner : owner j = owner i
  · simp [ungroup, group, Function.update, howner]
  · have hji : j ≠ i := by
      intro h
      exact howner (congrArg owner h)
    simp [ungroup, group, Function.update, howner, hji]

/-- With at most one stage per owner, an owner-level deviation is exactly the
corresponding single-stage update. -/
theorem ungroup_update_of_injective {owner : Fin n → ι}
    (howner : Function.Injective owner) (σ : Strategy A) (i : Fin n)
    (deviation : Strategy A) :
    ungroup owner
        (Function.update (group owner σ) (owner i) deviation) =
      Function.update σ i (deviation i) := by
  funext j h
  by_cases hji : j = i
  · subst j
    simp [ungroup, Function.update]
  · have hne : owner j ≠ owner i := by
      intro h
      exact hji (howner h)
    simp [ungroup, group, Function.update, hne, hji]

/-- The strategic-form game whose deviations replace every plan owned by one
player. -/
def ownedNFG (owner : Fin n → ι) (A : Fin n → Type)
    (u : (∀ i, A i) → ι → ℝ) :
    NFG.NFGGame ι (PlayerStrategy owner A) where
  Outcome := ∀ i, A i
  outcome σ := realize (ungroup owner σ)
  utility := u

/-- Compile the player-form sequential game through the existing NFG bridge. -/
noncomputable def compileOwned (owner : Fin n → ι) (A : Fin n → Type)
    (u : (∀ i, A i) → ι → ℝ) : GameTheory.KernelGame ι :=
  (ownedNFG owner A u).toKernelGame

/-- Player-form Nash for a stage profile under an ownership map. -/
def IsPlayerNash (owner : Fin n → ι) (u : (∀ i, A i) → ι → ℝ)
    (σ : Strategy A) : Prop :=
  NFG.IsNashPure (ownedNFG owner A u) (group owner σ)

/-- Agent-form equilibrium tests one owned decision at a time, using its
owner's utility. -/
def IsAgentEquilibrium (owner : Fin n → ι)
    (u : (∀ i, A i) → ι → ℝ) (σ : Strategy A) : Prop :=
  (ShapeSeqDep A).IsEquilibriumIn ()
    (fun path i => u path (owner i)) σ

/-- Player-form Nash implies agent-form equilibrium: every single-stage
deviation is a special case of replacing all plans owned by that player. -/
theorem IsPlayerNash.isAgentEquilibrium {owner : Fin n → ι}
    {u : (∀ i, A i) → ι → ℝ} {σ : Strategy A}
    (hσ : IsPlayerNash owner u σ) :
    IsAgentEquilibrium owner u σ := by
  intro i deviation
  have hdev := hσ (owner i)
    (group owner (Function.update σ i deviation) (owner i))
  change
    u (realize (Function.update σ i deviation)) (owner i) ≤
      u (realize σ) (owner i)
  simpa [IsPlayerNash, ownedNFG, NFG.deviate,
    ungroup_update_group] using hdev

/-- If no player owns two stages, agent-form and player-form deviations
coincide. Unowned players are harmless because their total plan coordinates
are never read. -/
theorem isAgentEquilibrium_iff_isPlayerNash_of_injective
    {owner : Fin n → ι} (howner : Function.Injective owner)
    (u : (∀ i, A i) → ι → ℝ) (σ : Strategy A) :
    IsAgentEquilibrium owner u σ ↔ IsPlayerNash owner u σ := by
  constructor
  · intro hσ p deviation
    change
      u (realize (ungroup owner
          (Function.update (group owner σ) p deviation))) p ≤
        u (realize σ) p
    by_cases hp : ∃ i, owner i = p
    · rcases hp with ⟨i, hi⟩
      have hstage := hσ i (deviation i)
      change
        u (realize (Function.update σ i (deviation i))) (owner i) ≤
          u (realize σ) (owner i) at hstage
      have hprofile :
          ungroup owner
              (Function.update (group owner σ) p deviation) =
            Function.update σ i (deviation i) := by
        rw [← hi]
        exact ungroup_update_of_injective howner σ i deviation
      rw [hprofile, ← hi]
      exact hstage
    · have hprofile :
          ungroup owner
              (Function.update (group owner σ) p deviation) = σ := by
        funext i history
        have hip : owner i ≠ p := by
          intro hi
          exact hp ⟨i, hi⟩
        simp [ungroup, group, Function.update, hip]
      rw [hprofile]
  · exact IsPlayerNash.isAgentEquilibrium

/-- Player-form Nash is exactly Nash in the compiled kernel game. -/
theorem isPlayerNash_iff_kernelNash (owner : Fin n → ι)
    (u : (∀ i, A i) → ι → ℝ) (σ : Strategy A) :
    IsPlayerNash owner u σ ↔
      (compileOwned owner A u).IsNash (group owner σ) := by
  exact NFG.IsNashPure_iff_kernelGame (ownedNFG owner A u)
    (group owner σ)

end OpenGames.ShapeSeqDep

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
    simp [ungroup, Function.update]
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
