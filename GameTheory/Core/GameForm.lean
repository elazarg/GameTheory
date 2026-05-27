/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.KernelGame
import Math.Probability

/-!
# GameTheory.Core.GameForm

A `GameForm` is a `KernelGame` minus utility: the pure protocol layer of a game.
It captures strategies, outcomes, and the stochastic outcome mechanism, but says
nothing about player preferences.

This decomposition makes explicit a key structural observation:
- **Protocol** (GameForm): strategy spaces, outcome kernel, deviation structure
- **Behavior** (utility/preferences): what players want
- **Solution concepts** (Nash, dominance): protocol + behavior composed

## Main definitions

- `GameForm` -- strategy-indexed outcome kernel without utility
- `GameForm.Profile`, `GameForm.outcomeDist`, `GameForm.correlatedOutcome`
- `GameForm.deviateProfile` -- unilateral deviation (derivable, not primitive)
- `GameForm.withUtility` -- attach utility to recover a `KernelGame`
- `KernelGame.toGameForm` -- strip utility

## Classification of game-theoretic concepts

**Pure protocol** (definable on `GameForm` alone):
- Strategy spaces, outcome distributions, deviation structure
- Kuhn's theorem (behavioral <-> mixed strategies)
- `evalDist`, perfect recall, information sets
- Symmetry of the game form

**Quasi-linear** (behavioral structure that references outcome space):
- Expected utility `eu` -- linear functional on outcome distributions
- Social welfare functions -- aggregate utility over outcomes
-/

namespace GameTheory

open Math.Probability

-- ============================================================================
-- GameForm structure
-- ============================================================================

/-- A game form: the protocol layer of a game, without utility.
    Captures strategy spaces, outcomes, and the stochastic mechanism
    mapping strategy profiles to outcome distributions. -/
structure GameForm (ι : Type) where
  Strategy : ι → Type
  Outcome : Type
  outcomeKernel : Kernel (∀ i, Strategy i) Outcome

namespace GameForm

variable {ι : Type}

/-- A strategy profile: one strategy per player. -/
abbrev Profile (F : GameForm ι) := ∀ i, F.Strategy i

/-- Outcome distribution under a strategy profile. -/
noncomputable def outcomeDist (F : GameForm ι) (σ : F.Profile) : PMF F.Outcome :=
  F.outcomeKernel σ

/-- Outcome distribution under a correlated profile distribution (correlation device). -/
noncomputable def correlatedOutcome (F : GameForm ι)
    (μ : PMF (F.Profile)) : PMF F.Outcome :=
  Kernel.pushforward F.outcomeKernel μ

/-- A point-mass profile distribution induces the same outcome distribution
    as direct evaluation at that profile. -/
@[simp] theorem correlatedOutcome_pure (F : GameForm ι) (σ : F.Profile) :
    F.correlatedOutcome (PMF.pure σ) = F.outcomeKernel σ := by
  simp [correlatedOutcome]

-- ============================================================================
-- Derivable protocol operations
-- ============================================================================

section UpdateOps
variable [DecidableEq ι]

open Classical in
/-- Unilateral deviation: replace player `who`'s strategy in profile `σ`. -/
noncomputable def deviateProfile (F : GameForm ι) (σ : F.Profile)
    (who : ι) (s' : F.Strategy who) : F.Profile :=
  Function.update σ who s'

open Classical in
/-- Outcome distribution after a unilateral deviation. -/
noncomputable def deviateOutcome (F : GameForm ι) (σ : F.Profile)
    (who : ι) (s' : F.Strategy who) : PMF F.Outcome :=
  F.outcomeKernel (F.deviateProfile σ who s')

open Classical in
/-- Push a profile distribution through unilateral deviation to get
    the resulting outcome distribution. -/
noncomputable def deviateDistribution (F : GameForm ι)
    (μ : PMF (F.Profile)) (who : ι) (s' : F.Strategy who) : PMF F.Outcome :=
  μ.bind (fun σ => F.outcomeKernel (F.deviateProfile σ who s'))

open Classical in
/-- Constant deviation: every profile in the support gets the same deviation applied. -/
noncomputable def constDeviateDistribution (F : GameForm ι)
    (σ : F.Profile) (who : ι) (s' : F.Strategy who) : PMF F.Outcome :=
  F.outcomeKernel (F.deviateProfile σ who s')

open Classical in
@[simp] theorem deviateProfile_same (F : GameForm ι) (σ : F.Profile)
    (who : ι) : F.deviateProfile σ who (σ who) = σ := by
  simp [deviateProfile]

open Classical in
@[simp] theorem deviateOutcome_same (F : GameForm ι) (σ : F.Profile)
    (who : ι) : F.deviateOutcome σ who (σ who) = F.outcomeKernel σ := by
  simp [deviateOutcome]

-- ============================================================================
-- Function-based deviation (for correlated equilibrium)
-- ============================================================================

open Classical in
/-- Profile-level deviation with a deviation function: replace player `who`'s
    strategy by applying `dev` to their current strategy. -/
noncomputable def deviateProfileFn (F : GameForm ι) (σ : F.Profile)
    (who : ι) (dev : F.Strategy who → F.Strategy who) : F.Profile :=
  Function.update σ who (dev (σ who))

/-- Push a profile distribution through a recommendation-dependent deviation. -/
noncomputable def deviateDistributionFn (F : GameForm ι)
    (μ : PMF F.Profile) (who : ι)
    (dev : F.Strategy who → F.Strategy who) : PMF F.Profile :=
  μ.bind (fun σ => PMF.pure (F.deviateProfileFn σ who dev))

open Classical in
/-- Push a profile distribution through a constant unilateral deviation. -/
noncomputable def constDeviateDistributionFn (F : GameForm ι)
    (μ : PMF F.Profile) (who : ι) (s' : F.Strategy who) : PMF F.Profile :=
  μ.bind (fun σ => PMF.pure (Function.update σ who s'))

open Classical in
@[simp] theorem constDeviateDistributionFn_pure (F : GameForm ι)
    (σ : F.Profile) (who : ι) (s' : F.Strategy who) :
    F.constDeviateDistributionFn (PMF.pure σ) who s' =
      PMF.pure (Function.update σ who s') := by
  simp [constDeviateDistributionFn]

end UpdateOps

-- ============================================================================
-- Bridge to KernelGame
-- ============================================================================

/-- Attach a utility function to a game form to get a full kernel game. -/
def withUtility (F : GameForm ι) (u : F.Outcome → Payoff ι) : KernelGame ι where
  Strategy := F.Strategy
  Outcome := F.Outcome
  utility := u
  outcomeKernel := F.outcomeKernel

end GameForm

namespace KernelGame

variable {ι : Type}

/-- Strip utility from a kernel game to get its underlying game form. -/
def toGameForm (G : KernelGame ι) : GameForm ι where
  Strategy := G.Strategy
  Outcome := G.Outcome
  outcomeKernel := G.outcomeKernel

@[simp] theorem toGameForm_Strategy (G : KernelGame ι) :
    G.toGameForm.Strategy = G.Strategy := rfl

@[simp] theorem toGameForm_Outcome (G : KernelGame ι) :
    G.toGameForm.Outcome = G.Outcome := rfl

@[simp] theorem toGameForm_outcomeKernel (G : KernelGame ι) :
    G.toGameForm.outcomeKernel = G.outcomeKernel := rfl

/-- Round-trip: stripping utility then reattaching recovers the original game. -/
@[simp] theorem toGameForm_withUtility (G : KernelGame ι) :
    G.toGameForm.withUtility G.utility = G := by
  cases G; rfl

end KernelGame

namespace GameForm

variable {ι : Type}

@[simp] theorem withUtility_Strategy (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).Strategy = F.Strategy := rfl

@[simp] theorem withUtility_Outcome (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).Outcome = F.Outcome := rfl

@[simp] theorem withUtility_outcomeKernel (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).outcomeKernel = F.outcomeKernel := rfl

@[simp] theorem withUtility_utility (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).utility = u := rfl

/-- Round-trip: attaching utility then stripping recovers the original form. -/
@[simp] theorem withUtility_toGameForm (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).toGameForm = F := by
  cases F; rfl

-- ============================================================================
-- Functorial operations
-- ============================================================================

/-- Push outcomes through a function. Strategies and kernel structure unchanged;
    only the interpretation of outcomes changes. -/
noncomputable def map (F : GameForm ι) (f : F.Outcome → β) : GameForm ι where
  Strategy := F.Strategy
  Outcome := β
  outcomeKernel := fun σ => (F.outcomeKernel σ).bind (fun ω => PMF.pure (f ω))

@[simp] theorem map_Strategy (F : GameForm ι) (f : F.Outcome → β) :
    (F.map f).Strategy = F.Strategy := rfl

@[simp] theorem map_Outcome (F : GameForm ι) (f : F.Outcome → β) :
    (F.map f).Outcome = β := rfl

theorem map_outcomeKernel (F : GameForm ι) (f : F.Outcome → β) (σ : F.Profile) :
    (F.map f).outcomeKernel σ = (F.outcomeKernel σ).bind (fun ω => PMF.pure (f ω)) := rfl

/-- Mapping by `id` is the identity (up to the bind-pure law). -/
theorem map_id (F : GameForm ι) :
    F.map id = F := by
  cases F
  simp [map, PMF.bind_pure]

/-- Mapping composes: `map g . map f = map (g . f)`. -/
theorem map_comp (F : GameForm ι) (f : F.Outcome → β) (g : β → γ) :
    (F.map f).map g = F.map (g ∘ f) := by
  simp [map, PMF.bind_bind, PMF.pure_bind]

-- ============================================================================
-- Product of game forms
-- ============================================================================

/-- Independent product of two game forms: players choose a strategy pair,
    outcomes are drawn independently from each form's kernel, and the result
    is a pair of outcomes. -/
noncomputable def product (F₁ F₂ : GameForm ι) : GameForm ι where
  Strategy := fun i => F₁.Strategy i × F₂.Strategy i
  Outcome := F₁.Outcome × F₂.Outcome
  outcomeKernel := fun σ =>
    (F₁.outcomeKernel (fun i => (σ i).1)).bind (fun ω₁ =>
      (F₂.outcomeKernel (fun i => (σ i).2)).bind (fun ω₂ =>
        PMF.pure (ω₁, ω₂)))

@[simp] theorem product_Outcome (F₁ F₂ : GameForm ι) :
    (F₁.product F₂).Outcome = (F₁.Outcome × F₂.Outcome) := rfl

/-- Left projection of a product game form recovers the first form's outcome distribution. -/
theorem product_map_fst (F₁ F₂ : GameForm ι) (σ : (F₁.product F₂).Profile) :
    ((F₁.product F₂).outcomeKernel σ).bind (fun p => PMF.pure p.1) =
      F₁.outcomeKernel (fun i => (σ i).1) := by
  simp [product, PMF.bind_bind, PMF.pure_bind, PMF.bind_pure]

/-- Right projection of a product game form recovers the second form's outcome distribution. -/
theorem product_map_snd (F₁ F₂ : GameForm ι) (σ : (F₁.product F₂).Profile) :
    ((F₁.product F₂).outcomeKernel σ).bind (fun p => PMF.pure p.2) =
      F₂.outcomeKernel (fun i => (σ i).2) := by
  simp [product, PMF.bind_bind, PMF.pure_bind]

-- ============================================================================
-- Protocol maps (CT-oriented overlay)
-- ============================================================================

/-- A protocol-preserving map between game forms.

Mnemonic-first interpretation:
- relabel strategies via `stratMap`,
- relabel outcomes via `outcomeMap`,
- preserve induced outcome distributions.

CT-oriented view: this is a morphism in the category of game forms. -/
structure ProtocolMap (F F' : GameForm ι) where
  stratMap : ∀ i, F.Strategy i → F'.Strategy i
  outcomeMap : F.Outcome → F'.Outcome
  outcomeKernel_preserved : ∀ σ : F.Profile,
    F'.outcomeKernel (fun i => stratMap i (σ i)) =
      (F.outcomeKernel σ).bind (fun ω => PMF.pure (outcomeMap ω))

namespace ProtocolMap

/-- Identity protocol map. -/
def id (F : GameForm ι) : ProtocolMap F F where
  stratMap := fun _i => _root_.id
  outcomeMap := _root_.id
  outcomeKernel_preserved := by intro σ; simp

/-- Composition of protocol maps. -/
def comp {F F' F'' : GameForm ι}
    (g : ProtocolMap F' F'') (f : ProtocolMap F F') : ProtocolMap F F'' where
  stratMap := fun i => g.stratMap i ∘ f.stratMap i
  outcomeMap := g.outcomeMap ∘ f.outcomeMap
  outcomeKernel_preserved := by
    intro σ
    simp [g.outcomeKernel_preserved, f.outcomeKernel_preserved, PMF.bind_bind]

@[simp] theorem id_stratMap (F : GameForm ι) (i : ι) :
    (id F).stratMap i = _root_.id := rfl

@[simp] theorem id_outcomeMap (F : GameForm ι) :
    (id F).outcomeMap = _root_.id := rfl

@[simp] theorem comp_stratMap {F F' F'' : GameForm ι}
    (g : ProtocolMap F' F'') (f : ProtocolMap F F') (i : ι) :
    (comp g f).stratMap i = g.stratMap i ∘ f.stratMap i := rfl

@[simp] theorem comp_outcomeMap {F F' F'' : GameForm ι}
    (g : ProtocolMap F' F'') (f : ProtocolMap F F') :
    (comp g f).outcomeMap = g.outcomeMap ∘ f.outcomeMap := rfl

@[simp] theorem id_comp {F F' : GameForm ι} (f : ProtocolMap F F') :
    comp (id F') f = f := by
  cases f
  rfl

@[simp] theorem comp_id {F F' : GameForm ι} (f : ProtocolMap F F') :
    comp f (id F) = f := by
  cases f
  rfl

theorem comp_assoc {F F' F'' F''' : GameForm ι}
    (h : ProtocolMap F'' F''') (g : ProtocolMap F' F'') (f : ProtocolMap F F') :
    comp h (comp g f) = comp (comp h g) f := by
  cases h; cases g; cases f
  rfl

end ProtocolMap

section DeviateId
variable [DecidableEq ι]

open Classical in
/-- The identity deviation leaves the profile distribution unchanged. -/
theorem deviateDistributionFn_id (F : GameForm ι) (μ : PMF F.Profile) (who : ι) :
    F.deviateDistributionFn μ who _root_.id = μ := by
  simp only [deviateDistributionFn, deviateProfileFn, _root_.id]
  conv_lhs => arg 2; ext σ; rw [Function.update_eq_self]
  exact PMF.bind_pure μ

end DeviateId

end GameForm

end GameTheory
