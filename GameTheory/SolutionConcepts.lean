import GameTheory.KernelGame

/-!
# GameTheory.SolutionConcepts

Solution concepts for kernel-based games: Nash equilibrium and dominance.

Provides:
- `KernelGame.IsNash` — Nash equilibrium (no unilateral improvement)
- `KernelGame.IsDominant` — dominant strategy
- `KernelGame.dominant_is_nash` — a profile of dominant strategies is Nash

These are the single source of truth for solution concepts. Concrete
representations (NFG, EFG, MAID) should bridge to these definitions
via their `toKernelGame` conversions.
-/

namespace GameTheory

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
  classical
  intro who s'
  have h := hdom who σ s'
  simp only [Function.update_eq_self, ge_iff_le] at h
  exact h

-- ============================================================================
-- Preference-parameterized solution concepts
-- ============================================================================

open Classical in
/-- A strategy profile is a Nash equilibrium w.r.t. a preference `pref` on outcome
    distributions if no player prefers the distribution from any unilateral deviation.

    This generalizes `IsNash` beyond expected utility: `pref who d₁ d₂` means
    player `who` (weakly) prefers outcome distribution `d₁` over `d₂`. -/
def KernelGame.IsNashFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ : KernelGame.Profile G) : Prop :=
  ∀ (who : ι) (s' : G.Strategy who),
    pref who (G.outcomeKernel σ) (G.outcomeKernel (Function.update σ who s'))

open Classical in
/-- Action `s` is dominant for player `who` w.r.t. a preference on outcome distributions. -/
def KernelGame.IsDominantFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (who : ι) (s : G.Strategy who) : Prop :=
  ∀ (σ : KernelGame.Profile G) (s' : G.Strategy who),
    pref who (G.outcomeKernel (Function.update σ who s))
             (G.outcomeKernel (Function.update σ who s'))

/-- If every player has a dominant strategy w.r.t. `pref`, the profile of
    dominant strategies is Nash w.r.t. the same `pref`. -/
theorem KernelGame.dominant_is_nash_for (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ : KernelGame.Profile G)
    (hdom : ∀ i, G.IsDominantFor pref i (σ i)) : G.IsNashFor pref σ := by
  classical
  intro who s'
  have h := hdom who σ s'
  simp only [Function.update_eq_self] at h
  exact h

/-- The EU preference: player `who` weakly prefers `d₁` over `d₂` when expected
    utility under `d₁` is at least that under `d₂`. -/
def KernelGame.euPref (G : KernelGame ι) :
    ι → PMF G.Outcome → PMF G.Outcome → Prop :=
  fun who d₁ d₂ =>
    expect d₁ (fun ω => G.utility ω who) ≥ expect d₂ (fun ω => G.utility ω who)

/-- `IsNash` is exactly `IsNashFor` with EU preference. -/
theorem KernelGame.IsNash_iff_IsNashFor_eu (G : KernelGame ι) (σ : KernelGame.Profile G) :
    G.IsNash σ ↔ G.IsNashFor G.euPref σ := by
  simp [IsNash, IsNashFor, euPref, eu]

/-- `IsDominant` is exactly `IsDominantFor` with EU preference. -/
theorem KernelGame.IsDominant_iff_IsDominantFor_eu (G : KernelGame ι)
    (who : ι) (s : G.Strategy who) :
    G.IsDominant who s ↔ G.IsDominantFor G.euPref who s := by
  simp [IsDominant, IsDominantFor, euPref, eu]

namespace KernelGame

/-- Preference relation with per-player reflexivity/transitivity laws. -/
class PrefPreorder {α : Type} (pref : ι → α → α → Prop) : Prop where
  refl : ∀ i x, pref i x x
  trans : ∀ i x y z, pref i x y → pref i y z → pref i x z

open Classical in
/-- `s` is a best response for `who` against opponents fixed by `σ`. -/
def IsBestResponse (G : KernelGame ι) (who : ι) (σ : Profile G) (s : G.Strategy who) : Prop :=
  ∀ (s' : G.Strategy who),
    G.eu (Function.update σ who s) who ≥ G.eu (Function.update σ who s') who

open Classical in
/-- Preference-parameterized best response (on outcome distributions). -/
def IsBestResponseFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (who : ι) (σ : Profile G) (s : G.Strategy who) : Prop :=
  ∀ (s' : G.Strategy who),
    pref who (G.outcomeKernel (Function.update σ who s))
      (G.outcomeKernel (Function.update σ who s'))

/-- EU best response is exactly `IsBestResponseFor` with `euPref`. -/
theorem IsBestResponse_iff_IsBestResponseFor_eu (G : KernelGame ι)
    (who : ι) (σ : Profile G) (s : G.Strategy who) :
    G.IsBestResponse who σ s ↔ G.IsBestResponseFor G.euPref who σ s := by
  simp [IsBestResponse, IsBestResponseFor, euPref, eu]

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

open Classical in
/-- `s` weakly dominates `t` for player `who`. -/
def WeaklyDominates (G : KernelGame ι) (who : ι)
    (s t : G.Strategy who) : Prop :=
  ∀ (σ : Profile G),
    G.eu (Function.update σ who s) who ≥ G.eu (Function.update σ who t) who

open Classical in
/-- `s` strictly dominates `t` for player `who`. -/
def StrictlyDominates (G : KernelGame ι) (who : ι)
    (s t : G.Strategy who) : Prop :=
  ∀ (σ : Profile G),
    G.eu (Function.update σ who s) who > G.eu (Function.update σ who t) who

open Classical in
/-- Profile-level deviation map for correlated-play concepts. -/
noncomputable def deviateProfile (G : KernelGame ι) (σ : Profile G)
    (who : ι) (dev : G.Strategy who → G.Strategy who) : Profile G :=
  Function.update σ who (dev (σ who))

/-- Push a profile distribution through a recommendation-dependent deviation. -/
noncomputable def deviateDistribution (G : KernelGame ι)
    (μ : PMF (Profile G)) (who : ι)
    (dev : G.Strategy who → G.Strategy who) : PMF (Profile G) :=
  μ.bind (fun σ => PMF.pure (G.deviateProfile σ who dev))

open Classical in
/-- Push a profile distribution through a constant unilateral deviation. -/
noncomputable def constDeviateDistribution (G : KernelGame ι)
    (μ : PMF (Profile G)) (who : ι) (s' : G.Strategy who) : PMF (Profile G) :=
  μ.bind (fun σ => PMF.pure (Function.update σ who s'))

/-- Correlated expected utility for player `who`. -/
noncomputable def correlatedEu (G : KernelGame ι)
    (μ : PMF (Profile G)) (who : ι) : ℝ :=
  expect (G.correlatedOutcome μ) (fun ω => G.utility ω who)

/-- Correlated equilibrium: no player gains from recommendation-dependent deviation. -/
def IsCorrelatedEq (G : KernelGame ι) (μ : PMF (Profile G)) : Prop :=
  ∀ (who : ι) (dev : G.Strategy who → G.Strategy who),
    G.correlatedEu μ who ≥ G.correlatedEu (G.deviateDistribution μ who dev) who

/-- Coarse correlated equilibrium: no player gains from constant unilateral deviation. -/
def IsCoarseCorrelatedEq (G : KernelGame ι) (μ : PMF (Profile G)) : Prop :=
  ∀ (who : ι) (s' : G.Strategy who),
    G.correlatedEu μ who ≥ G.correlatedEu (G.constDeviateDistribution μ who s') who

/-- Preference-parameterized correlated equilibrium (on outcome distributions). -/
def IsCorrelatedEqFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (μ : PMF (Profile G)) : Prop :=
  ∀ (who : ι) (dev : G.Strategy who → G.Strategy who),
    pref who (G.correlatedOutcome μ)
      (G.correlatedOutcome (G.deviateDistribution μ who dev))

/-- Preference-parameterized coarse correlated equilibrium. -/
def IsCoarseCorrelatedEqFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (μ : PMF (Profile G)) : Prop :=
  ∀ (who : ι) (s' : G.Strategy who),
    pref who (G.correlatedOutcome μ)
      (G.correlatedOutcome (G.constDeviateDistribution μ who s'))

/-- EU CE is exactly CE with `euPref`. -/
theorem IsCorrelatedEq_iff_IsCorrelatedEqFor_eu (G : KernelGame ι)
    (μ : PMF (Profile G)) :
    G.IsCorrelatedEq μ ↔ G.IsCorrelatedEqFor G.euPref μ := by
  simp [IsCorrelatedEq, IsCorrelatedEqFor, correlatedEu, euPref]

/-- EU CCE is exactly CCE with `euPref`. -/
theorem IsCoarseCorrelatedEq_iff_IsCoarseCorrelatedEqFor_eu (G : KernelGame ι)
    (μ : PMF (Profile G)) :
    G.IsCoarseCorrelatedEq μ ↔ G.IsCoarseCorrelatedEqFor G.euPref μ := by
  simp [IsCoarseCorrelatedEq, IsCoarseCorrelatedEqFor, correlatedEu, euPref]

end KernelGame

end GameTheory
