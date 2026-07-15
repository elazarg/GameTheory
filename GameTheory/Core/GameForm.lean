/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Basic
import Math.Probability
import Math.PMFProduct

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
- `GameForm.mixedExtension` -- utility-free independent randomization

The bridges `GameForm.withUtility` and `KernelGame.toGameForm` are defined in
`GameTheory.Core.KernelGame`, keeping this raw semantic module independent of
the utility-bearing structure.

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
-- Mixed extension
-- ============================================================================

open Classical in
/-- The utility-free mixed extension of a game form. Each player's strategy is
lifted to a probability distribution, independently sampled, and then evaluated
by the original outcome kernel. -/
noncomputable def mixedExtension (F : GameForm ι) [Fintype ι] : GameForm ι where
  Strategy := fun i => PMF (F.Strategy i)
  Outcome := F.Outcome
  outcomeKernel := fun σ => (Math.PMFProduct.pmfPi σ).bind F.outcomeKernel

@[simp] theorem mixedExtension_Strategy (F : GameForm ι) [Fintype ι] :
    F.mixedExtension.Strategy = fun i => PMF (F.Strategy i) := rfl

@[simp] theorem mixedExtension_Outcome (F : GameForm ι) [Fintype ι] :
    F.mixedExtension.Outcome = F.Outcome := rfl

theorem mixedExtension_outcomeKernel (F : GameForm ι) [Fintype ι]
    (σ : F.mixedExtension.Profile) :
    F.mixedExtension.outcomeKernel σ =
      (Math.PMFProduct.pmfPi σ).bind F.outcomeKernel := rfl

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

@[simp] theorem product_Strategy (F₁ F₂ : GameForm ι) :
    (F₁.product F₂).Strategy = fun i => F₁.Strategy i × F₂.Strategy i := rfl

@[simp] theorem product_Outcome (F₁ F₂ : GameForm ι) :
    (F₁.product F₂).Outcome = (F₁.Outcome × F₂.Outcome) := rfl

theorem product_outcomeKernel (F₁ F₂ : GameForm ι)
    (σ : (F₁.product F₂).Profile) :
    (F₁.product F₂).outcomeKernel σ =
      (F₁.outcomeKernel (fun i => (σ i).1)).bind (fun ω₁ =>
        (F₂.outcomeKernel (fun i => (σ i).2)).bind (fun ω₂ =>
          PMF.pure (ω₁, ω₂))) := rfl

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
