/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Equilibrium.GameFormSolutionConcepts
import GameTheory.Concepts.Foundations.Deviation
import Math.Probability

/-!
# GameTheory.Concepts.Equilibrium.SolutionConcepts

Solution concepts for kernel-based games: Nash equilibrium and dominance.

Provides:
- `KernelGame.IsNash` -- Nash equilibrium (no unilateral improvement)
- `KernelGame.IsDominant` -- dominant strategy
- `KernelGame.dominant_is_nash` -- a profile of dominant strategies is Nash

These are the single source of truth for EU-specific solution concepts. Concrete
representations (NFG, EFG, MAID) should bridge to these definitions
via their `toKernelGame` conversions.

Preference-parameterized concepts (`*For`) live on `GameForm` and are
re-exported here as `KernelGame.*For` via delegation.
-/

namespace GameTheory

open Math.Probability

open Classical in
/-- Build a KernelGame from a direct expected-utility function (no stochastic kernel).
    This is the "strategic form" special case: outcome = utility vector, kernel = point mass. -/
noncomputable def KernelGame.ofEU
    (Strategy : ι → Type) (eu : (∀ i, Strategy i) → Payoff ι) : KernelGame ι where
  Strategy := Strategy
  Outcome := Payoff ι
  utility := id
  outcomeKernel := fun σ => PMF.pure (eu σ)

variable {ι : Type}

/-- EU of a game built from `ofEU` is just the direct EU function. -/
@[simp] theorem KernelGame.eu_ofEU
    (S : ι → Type) (u : (∀ i, S i) → Payoff ι) (σ : ∀ i, S i) (i : ι) :
    (ofEU S u).eu σ i = u σ i := by
  simp [KernelGame.eu, ofEU, expect_pure]

/-- The Strategy field of `ofEU S u` is `S` by definition. Marked `@[simp]`
so that `Function.update` and `Profile` expressions reduce uniformly during
unification. -/
@[simp] theorem KernelGame.ofEU_Strategy
    (S : ι → Type) (u : (∀ i, S i) → Payoff ι) :
    (ofEU S u).Strategy = S := rfl

-- ============================================================================
-- EU-specific solution concepts
-- ============================================================================

section UpdateConcepts
variable [DecidableEq ι]

open Classical in
/-- A strategy profile `σ` is a Nash equilibrium if no player can
    improve their utility by unilateral deviation. -/
def KernelGame.IsNash (G : KernelGame ι) (σ : KernelGame.Profile G) : Prop :=
  ∀ (who : ι) (s' : G.Strategy who),
    G.eu σ who ≥ G.eu (Function.update σ who s') who

open Classical in
/-- Action `s` is dominant for player `who` if, regardless of others'
    actions, `s` yields at least as high a utility as any alternative. -/
def KernelGame.IsDominant (G : KernelGame ι) (who : ι) (s : G.Strategy who) : Prop :=
  ∀ (σ : KernelGame.Profile G) (s' : G.Strategy who),
    G.eu (Function.update σ who s) who ≥ G.eu (Function.update σ who s') who

/-- If every player has a dominant strategy, the profile of dominant
    strategies is a Nash equilibrium. -/
theorem KernelGame.dominant_is_nash (G : KernelGame ι) (σ : KernelGame.Profile G)
    (hdom : ∀ i, G.IsDominant i (σ i)) : G.IsNash σ := by
  intro who s'
  have h := hdom who σ s'
  simp only [Function.update_eq_self, ge_iff_le] at h
  exact h

-- ============================================================================
-- Preference-parameterized solution concepts (delegated to GameForm)
-- ============================================================================

/-- `KernelGame.IsNashFor` delegates to `GameForm.IsNashFor` on the underlying form. -/
def KernelGame.IsNashFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ : KernelGame.Profile G) : Prop :=
  G.toGameForm.IsNashFor pref σ

/-- `KernelGame.IsDominantFor` delegates to `GameForm.IsDominantFor`. -/
def KernelGame.IsDominantFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (who : ι) (s : G.Strategy who) : Prop :=
  G.toGameForm.IsDominantFor pref who s

/-- If every player has a dominant strategy w.r.t. `pref`, the profile of
    dominant strategies is Nash w.r.t. the same `pref`. -/
theorem KernelGame.dominant_is_nash_for (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ : KernelGame.Profile G)
    (hdom : ∀ i, G.IsDominantFor pref i (σ i)) : G.IsNashFor pref σ :=
  G.toGameForm.dominant_is_nash_for pref σ hdom

/-- The EU preference: player `who` weakly prefers `d₁` over `d₂` when expected
    utility under `d₁` is at least that under `d₂`. -/
def KernelGame.euPref (G : KernelGame ι) :
    ι → PMF G.Outcome → PMF G.Outcome → Prop :=
  fun who d₁ d₂ =>
    expect d₁ (fun ω => G.utility ω who) ≥ expect d₂ (fun ω => G.utility ω who)

/-- The strict EU preference: player `who` strictly prefers `d₁` over `d₂`. -/
def KernelGame.euStrictPref (G : KernelGame ι) :
    ι → PMF G.Outcome → PMF G.Outcome → Prop :=
  fun who d₁ d₂ =>
    expect d₁ (fun ω => G.utility ω who) > expect d₂ (fun ω => G.utility ω who)

-- ============================================================================
-- EU bridge theorems
-- ============================================================================

/-- `IsNash` is exactly `IsNashFor` with EU preference. -/
theorem KernelGame.IsNash_iff_IsNashFor_eu (G : KernelGame ι) (σ : KernelGame.Profile G) :
    G.IsNash σ ↔ G.IsNashFor G.euPref σ := by
  constructor
  · intro h
    exact (G.toGameForm.isNashFor_iff G.euPref σ).2 (fun who s' => by
      simpa [IsNash, KernelGame.euPref, KernelGame.eu] using h who s')
  · intro h who s'
    have h' := (G.toGameForm.isNashFor_iff G.euPref σ).1 h who s'
    simpa [IsNash, KernelGame.euPref, KernelGame.eu] using h'

/-- `IsDominant` is exactly `IsDominantFor` with EU preference. -/
theorem KernelGame.IsDominant_iff_IsDominantFor_eu (G : KernelGame ι)
    (who : ι) (s : G.Strategy who) :
    G.IsDominant who s ↔ G.IsDominantFor G.euPref who s :=
  ⟨fun h σ s' => h σ s', fun h σ s' => h σ s'⟩

namespace KernelGame

-- ============================================================================
-- Best response
-- ============================================================================

open Classical in
/-- `s` is a best response for `who` against opponents fixed by `σ`. -/
def IsBestResponse (G : KernelGame ι) (who : ι) (σ : Profile G) (s : G.Strategy who) : Prop :=
  ∀ (s' : G.Strategy who),
    G.eu (Function.update σ who s) who ≥ G.eu (Function.update σ who s') who

/-- `KernelGame.IsBestResponseFor` delegates to `GameForm.IsBestResponseFor`. -/
def IsBestResponseFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (who : ι) (σ : Profile G) (s : G.Strategy who) : Prop :=
  G.toGameForm.IsBestResponseFor pref who σ s

/-- EU best response is exactly `IsBestResponseFor` with `euPref`. -/
theorem IsBestResponse_iff_IsBestResponseFor_eu (G : KernelGame ι)
    (who : ι) (σ : Profile G) (s : G.Strategy who) :
    G.IsBestResponse who σ s ↔ G.IsBestResponseFor G.euPref who σ s := by
  simp [IsBestResponse, IsBestResponseFor, GameForm.IsBestResponseFor, euPref, eu]

-- ============================================================================
-- Strict Nash and strict dominance
-- ============================================================================

open Classical in
/-- Strict Nash equilibrium: every unilateral deviation strictly decreases utility. -/
def IsStrictNash (G : KernelGame ι) (σ : Profile G) : Prop :=
  ∀ (who : ι) (s' : G.Strategy who), s' ≠ σ who →
    G.eu σ who > G.eu (Function.update σ who s') who

open Classical in
/-- Strictly dominant strategy for player `who`. -/
def IsStrictDominant (G : KernelGame ι) (who : ι) (s : G.Strategy who) : Prop :=
  ∀ (σ : Profile G) (s' : G.Strategy who), s' ≠ s →
    G.eu (Function.update σ who s) who > G.eu (Function.update σ who s') who

/-- `KernelGame.IsStrictNashFor` delegates to `GameForm.IsStrictNashFor`. -/
def IsStrictNashFor (G : KernelGame ι)
    (spref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ : Profile G) : Prop :=
  G.toGameForm.IsStrictNashFor spref σ

/-- `KernelGame.IsStrictDominantFor` delegates to `GameForm.IsStrictDominantFor`. -/
def IsStrictDominantFor (G : KernelGame ι)
    (spref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (who : ι) (s : G.Strategy who) : Prop :=
  G.toGameForm.IsStrictDominantFor spref who s

/-- `IsStrictNash` is exactly `IsStrictNashFor` with EU strict preference. -/
theorem IsStrictNash_iff_IsStrictNashFor_eu (G : KernelGame ι) (σ : Profile G) :
    G.IsStrictNash σ ↔ G.IsStrictNashFor G.euStrictPref σ :=
  ⟨fun h who s' hne => h who s' hne, fun h who s' hne => h who s' hne⟩

/-- `IsStrictDominant` is exactly `IsStrictDominantFor` with EU strict preference. -/
theorem IsStrictDominant_iff_IsStrictDominantFor_eu (G : KernelGame ι)
    (who : ι) (s : G.Strategy who) :
    G.IsStrictDominant who s ↔ G.IsStrictDominantFor G.euStrictPref who s :=
  ⟨fun h σ s' hne => h σ s' hne, fun h σ s' hne => h σ s' hne⟩

-- ============================================================================
-- Weak and strict dominance
-- ============================================================================

open Classical in
/-- `s` weakly dominates `t` for player `who` in the reflexive-preorder sense:
its expected utility is at least that of `t` against every profile. -/
def WeaklyDominatesReflexive (G : KernelGame ι) (who : ι)
    (s t : G.Strategy who) : Prop :=
  ∀ (σ : Profile G),
    G.eu (Function.update σ who s) who ≥ G.eu (Function.update σ who t) who

open Classical in
/-- `s` strictly dominates `t` for player `who`. -/
def StrictlyDominates (G : KernelGame ι) (who : ι)
    (s t : G.Strategy who) : Prop :=
  ∀ (σ : Profile G),
    G.eu (Function.update σ who s) who > G.eu (Function.update σ who t) who

/-- `KernelGame.WeaklyDominatesReflexiveFor` delegates to
`GameForm.WeaklyDominatesReflexiveFor`. -/
def WeaklyDominatesReflexiveFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (who : ι) (s t : G.Strategy who) : Prop :=
  G.toGameForm.WeaklyDominatesReflexiveFor pref who s t

/-- `KernelGame.StrictlyDominatesFor` delegates to `GameForm.StrictlyDominatesFor`. -/
def StrictlyDominatesFor (G : KernelGame ι)
    (spref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (who : ι) (s t : G.Strategy who) : Prop :=
  G.toGameForm.StrictlyDominatesFor spref who s t

/-- `WeaklyDominatesReflexive` is exactly `WeaklyDominatesReflexiveFor` with
EU preference. -/
theorem WeaklyDominatesReflexive_iff_WeaklyDominatesReflexiveFor_eu
    (G : KernelGame ι)
    (who : ι) (s t : G.Strategy who) :
    G.WeaklyDominatesReflexive who s t ↔
      G.WeaklyDominatesReflexiveFor G.euPref who s t :=
  ⟨fun h σ => h σ, fun h σ => h σ⟩

/-- `StrictlyDominates` is exactly `StrictlyDominatesFor` with EU strict preference. -/
theorem StrictlyDominates_iff_StrictlyDominatesFor_eu (G : KernelGame ι)
    (who : ι) (s t : G.Strategy who) :
    G.StrictlyDominates who s t ↔ G.StrictlyDominatesFor G.euStrictPref who s t :=
  ⟨fun h σ => h σ, fun h σ => h σ⟩

-- ============================================================================
-- Correlated equilibrium (EU-specific)
-- ============================================================================

/-- Correlated expected utility for player `who`. -/
noncomputable def correlatedEu (G : KernelGame ι)
    (μ : PMF (Profile G)) (who : ι) : ℝ :=
  expect (G.correlatedOutcome μ) (fun ω => G.utility ω who)

/-- Correlated equilibrium: no player gains from recommendation-dependent deviation. -/
def IsCorrelatedEq (G : KernelGame ι) (μ : PMF (Profile G)) : Prop :=
  by
    classical
    exact ∀ (who : ι) (dev : G.Strategy who → G.Strategy who),
      G.correlatedEu μ who ≥ G.correlatedEu (G.unilateralDeviationDistribution μ who dev) who

/-- Coarse correlated equilibrium: no player gains from constant unilateral deviation. -/
def IsCoarseCorrelatedEq (G : KernelGame ι) (μ : PMF (Profile G)) : Prop :=
  by
    classical
    exact ∀ (who : ι) (s' : G.Strategy who),
      G.correlatedEu μ who ≥ G.correlatedEu (G.constantDeviationDistribution μ who s') who

-- ============================================================================
-- Equilibrium payoff sets
-- ============================================================================

/-- The set of player payoff vectors realized at some Nash equilibrium. -/
def nashPayoffSet (G : KernelGame ι) : Set (Payoff ι) :=
  {v | ∃ σ : Profile G, G.IsNash σ ∧ (fun i => G.eu σ i) = v}

/-- The set of player payoff vectors realized at some correlated equilibrium. -/
def correlatedPayoffSet (G : KernelGame ι) : Set (Payoff ι) :=
  {v | ∃ μ : PMF (Profile G), G.IsCorrelatedEq μ ∧ (fun i => G.correlatedEu μ i) = v}

/-- The set of player payoff vectors realized at some coarse correlated
equilibrium. -/
def coarseCorrelatedPayoffSet (G : KernelGame ι) : Set (Payoff ι) :=
  {v | ∃ μ : PMF (Profile G), G.IsCoarseCorrelatedEq μ ∧ (fun i => G.correlatedEu μ i) = v}

/-- `KernelGame.IsCorrelatedEqFor` delegates to `GameForm.IsCorrelatedEqFor`. -/
def IsCorrelatedEqFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (μ : PMF (Profile G)) : Prop :=
  G.toGameForm.IsCorrelatedEqFor pref μ

/-- `KernelGame.IsCoarseCorrelatedEqFor` delegates to `GameForm.IsCoarseCorrelatedEqFor`. -/
def IsCoarseCorrelatedEqFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (μ : PMF (Profile G)) : Prop :=
  G.toGameForm.IsCoarseCorrelatedEqFor pref μ

/-- EU CE is exactly CE with `euPref`. -/
theorem IsCorrelatedEq_iff_IsCorrelatedEqFor_eu (G : KernelGame ι)
    (μ : PMF (Profile G)) :
    G.IsCorrelatedEq μ ↔ G.IsCorrelatedEqFor G.euPref μ := by
  constructor
  · intro h who dev
    change (expect ((μ.bind fun σ => PMF.pure (Function.update σ who (dev (σ who)))).bind
        G.outcomeKernel) (fun ω => G.utility ω who)) ≤
      expect (μ.bind G.outcomeKernel) (fun ω => G.utility ω who)
    rw [PMF.bind_bind]
    simpa [KernelGame.correlatedEu, KernelGame.correlatedOutcome,
      KernelGame.unilateralDeviationDistribution, KernelGame.deviationDistribution,
      KernelGame.unilateralDeviation] using h who dev
  · intro h who dev
    have hh := h who dev
    change (expect ((μ.bind fun σ => PMF.pure (Function.update σ who (dev (σ who)))).bind
        G.outcomeKernel) (fun ω => G.utility ω who)) ≤
      expect (μ.bind G.outcomeKernel) (fun ω => G.utility ω who) at hh
    rw [PMF.bind_bind] at hh
    simpa [KernelGame.correlatedEu, KernelGame.correlatedOutcome,
      KernelGame.unilateralDeviationDistribution, KernelGame.deviationDistribution,
      KernelGame.unilateralDeviation] using hh

/-- EU CCE is exactly CCE with `euPref`. -/
theorem IsCoarseCorrelatedEq_iff_IsCoarseCorrelatedEqFor_eu (G : KernelGame ι)
    (μ : PMF (Profile G)) :
    G.IsCoarseCorrelatedEq μ ↔ G.IsCoarseCorrelatedEqFor G.euPref μ := by
  constructor
  · intro h who s'
    change (expect ((μ.bind fun σ => PMF.pure (Function.update σ who s')).bind
        G.outcomeKernel) (fun ω => G.utility ω who)) ≤
      expect (μ.bind G.outcomeKernel) (fun ω => G.utility ω who)
    rw [PMF.bind_bind]
    simpa [KernelGame.correlatedEu, KernelGame.correlatedOutcome,
      KernelGame.constantDeviationDistribution, KernelGame.deviationDistribution,
      KernelGame.constantDeviation] using h who s'
  · intro h who s'
    have hh := h who s'
    change (expect ((μ.bind fun σ => PMF.pure (Function.update σ who s')).bind
        G.outcomeKernel) (fun ω => G.utility ω who)) ≤
      expect (μ.bind G.outcomeKernel) (fun ω => G.utility ω who) at hh
    rw [PMF.bind_bind] at hh
    simpa [KernelGame.correlatedEu, KernelGame.correlatedOutcome,
      KernelGame.constantDeviationDistribution, KernelGame.deviationDistribution,
      KernelGame.constantDeviation] using hh

end KernelGame

end UpdateConcepts

end GameTheory
