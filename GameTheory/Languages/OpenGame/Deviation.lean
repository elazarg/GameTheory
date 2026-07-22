/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Ownership

/-!
# Deviation Families

A deviation family records, for each baseline profile and acting index, which
replacement profiles are admissible.  This separates the scope of a deviation
from the payoff comparison used to test it.

For dependent stage profiles this module supplies:

* `single`: change at most one stage;
* `fiber`: change any stages owned by one player;
* `coalition`: change any stages owned by a member of a coalition.

The generic stability predicate recovers the existing agent-form and
player-form sequential equilibrium notions exactly.  Coalition scopes are
provided without choosing a coalition objective or aggregation rule.
-/

namespace OpenGames

/-- Admissible replacement profiles, indexed by the acting agent or block. -/
abbrev DeviationFamily (Actor Strategy : Type*) :=
  Strategy → Actor → Set Strategy

namespace DeviationFamily

variable {Actor Strategy Outcome Payoff : Type*}

/-- Pointwise inclusion of admissible deviations. -/
def Refines (D E : DeviationFamily Actor Strategy) : Prop :=
  ∀ σ actor, D σ actor ⊆ E σ actor

@[refl] theorem Refines.refl (D : DeviationFamily Actor Strategy) :
    D.Refines D :=
  fun _ _ => Set.Subset.rfl

@[trans] theorem Refines.trans {D E F : DeviationFamily Actor Strategy}
    (hDE : D.Refines E) (hEF : E.Refines F) : D.Refines F :=
  fun σ actor => Set.Subset.trans (hDE σ actor) (hEF σ actor)

/-- Stability against every deviation admitted by `D`. -/
def IsStableUnder [Preorder Payoff]
    (D : DeviationFamily Actor Strategy)
    (outcome : Strategy → Outcome) (utility : Outcome → Actor → Payoff)
    (σ : Strategy) : Prop :=
  ∀ actor τ, τ ∈ D σ actor →
    utility (outcome τ) actor ≤ utility (outcome σ) actor

/-- Enlarging the deviation family strengthens stability. -/
theorem IsStableUnder.mono [Preorder Payoff]
    {D E : DeviationFamily Actor Strategy}
    {outcome : Strategy → Outcome} {utility : Outcome → Actor → Payoff}
    {σ : Strategy} (hDE : D.Refines E)
    (hE : E.IsStableUnder outcome utility σ) :
    D.IsStableUnder outcome utility σ :=
  fun actor τ hτ => hE actor τ (hDE σ actor hτ)

variable {Stage Player : Type*} {S : Stage → Type*}

/-- Profiles which differ from the baseline only at stage `i`. -/
def single : DeviationFamily Stage (∀ i, S i) :=
  fun σ i => {τ | ∀ j, j ≠ i → τ j = σ j}

/-- Profiles which differ from the baseline only at stages owned by `p`. -/
def fiber (owner : Stage → Player) :
    DeviationFamily Player (∀ i, S i) :=
  fun σ p => {τ | ∀ j, owner j ≠ p → τ j = σ j}

/-- Profiles which differ from the baseline only at stages owned by members
of `coalition`. -/
def coalition (owner : Stage → Player) :
    DeviationFamily (Set Player) (∀ i, S i) :=
  fun σ members => {τ | ∀ j, owner j ∉ members → τ j = σ j}

theorem single_update_mem [DecidableEq Stage]
    (σ : ∀ i, S i) (i : Stage) (deviation : S i) :
    Function.update σ i deviation ∈ single σ i := by
  intro j hji
  simp [Function.update, hji]

theorem update_single_eq [DecidableEq Stage]
    {σ τ : ∀ i, S i} {i : Stage} (hτ : τ ∈ single σ i) :
    Function.update σ i (τ i) = τ := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [Function.update, hji, hτ j hji]

theorem single_refines_fiber
    (owner : Stage → Player) (i : Stage) (σ : ∀ i, S i) :
    single σ i ⊆ fiber owner σ (owner i) := by
  intro τ hτ j howner
  have hji : j ≠ i := by
    intro h
    exact howner (congrArg owner h)
  exact hτ j hji

theorem fiber_eq_singletonCoalition
    (owner : Stage → Player) (σ : ∀ i, S i) (p : Player) :
    fiber owner σ p = coalition owner σ ({p} : Set Player) := by
  classical
  ext τ
  simp [fiber, coalition]

end DeviationFamily

namespace OwnedProfile

open DeviationFamily

variable {Node Player Outcome : Type} [DecidableEq Node]
variable {Plan : Node → Type}

/-- Single-node deviation-family stability is exactly generic agent-form
owned-profile equilibrium. -/
theorem isStableUnder_single_iff_isAgentEquilibrium
    (owner : Node → Player) (outcome : (∀ node, Plan node) → Outcome)
    (utility : Outcome → Player → ℝ) (σ : ∀ node, Plan node) :
    IsStableUnder (single (S := Plan)) outcome
        (fun result node => utility result (owner node)) σ ↔
      IsAgentEquilibrium owner outcome utility σ := by
  constructor
  · intro h node deviation
    exact h node (Function.update σ node deviation)
      (single_update_mem σ node deviation)
  · intro h node τ hτ
    have hdev := h node (τ node)
    rw [update_single_eq hτ] at hdev
    exact hdev

variable [DecidableEq Player]

omit [DecidableEq Node] in
/-- Owner-fibre deviation-family stability is exactly generic player-form
Nash. -/
theorem isStableUnder_fiber_iff_isPlayerNash
    (owner : Node → Player) (outcome : (∀ node, Plan node) → Outcome)
    (utility : Outcome → Player → ℝ) (σ : ∀ node, Plan node) :
    IsStableUnder (fiber (S := Plan) owner) outcome utility σ ↔
      IsPlayerNash owner outcome utility σ := by
  constructor
  · intro h player deviation
    let τ := ungroup owner (Function.update (group owner σ) player deviation)
    have hmem : τ ∈ fiber owner σ player := by
      intro node howner
      simp [τ, ungroup, group, Function.update, howner]
    exact h player τ hmem
  · intro h player τ hτ
    have hdev := h player τ
    have hprofile : ungroup owner
        (Function.update (group owner σ) player τ) = τ := by
      funext node
      by_cases howner : owner node = player
      · simp [ungroup, Function.update, howner]
      · simp [ungroup, group, Function.update, howner, hτ node howner]
    change utility (outcome (ungroup owner
      (Function.update (group owner σ) player τ))) player ≤
        utility (outcome σ) player at hdev
    rw [hprofile] at hdev
    exact hdev

end OwnedProfile

namespace ShapeSeqDep

open DeviationFamily

variable {n : Nat} {ι : Type} [DecidableEq ι]
variable {A : Fin n → Type}

omit [DecidableEq ι] in
/-- Stability under single-stage deviation families is exactly the existing
agent-form open-game equilibrium. -/
theorem isStableUnder_single_iff_isAgentEquilibrium
    (owner : Fin n → ι) (u : (∀ i, A i) → ι → ℝ)
    (σ : Strategy A) :
    IsStableUnder (single (S := fun i => History A i → A i))
        realize (fun path i => u path (owner i)) σ ↔
      IsAgentEquilibrium owner u σ :=
  OwnedProfile.isStableUnder_single_iff_isAgentEquilibrium
    owner realize u σ

/-- Stability under owner-fibre deviation families is exactly player-form
Nash for the ownership presentation. -/
theorem isStableUnder_fiber_iff_isPlayerNash
    (owner : Fin n → ι) (u : (∀ i, A i) → ι → ℝ)
    (σ : Strategy A) :
    IsStableUnder (fiber (S := fun i => History A i → A i) owner)
        realize u σ ↔ IsPlayerNash owner u σ :=
  OwnedProfile.isStableUnder_fiber_iff_isPlayerNash owner realize u σ

end ShapeSeqDep

namespace ShapeDAG

open DeviationFamily

variable {n : Nat} {Player : Type} [DecidableEq Player]
variable {A : Fin n → Type}

omit [DecidableEq Player] in
/-- Single-node deviation-family stability recovers sparse-DAG agent-form
equilibrium exactly. -/
theorem isStableUnder_single_iff_isAgentEquilibrium
    (D : DecisionDAG n) (owner : Fin n → Player)
    (utility : (∀ i, A i) → Player → ℝ) (σ : Strategy D A) :
    IsStableUnder
        (single (S := fun i => History D A i → A i))
        (realize D) (fun path i => utility path (owner i)) σ ↔
      IsAgentEquilibrium D owner utility σ :=
  OwnedProfile.isStableUnder_single_iff_isAgentEquilibrium
    owner (realize D) utility σ

/-- Owner-fibre deviation-family stability recovers sparse-DAG player-form
Nash exactly. -/
theorem isStableUnder_fiber_iff_isPlayerNash
    (D : DecisionDAG n) (owner : Fin n → Player)
    (utility : (∀ i, A i) → Player → ℝ) (σ : Strategy D A) :
    IsStableUnder
        (fiber (S := fun i => History D A i → A i) owner)
        (realize D) utility σ ↔ IsPlayerNash D owner utility σ :=
  OwnedProfile.isStableUnder_fiber_iff_isPlayerNash
    owner (realize D) utility σ

end ShapeDAG

end OpenGames
