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

## Scope-outs

- **Subgame perfection / sequential equilibrium** — needs belief systems
- **Correlated equilibrium** — `correlatedOutcome` exists in `KernelGame`;
  CE definition could be added later
-/

namespace GameTheory

/-- Build a KernelGame from a direct expected-utility function (no stochastic kernel).
    This is the "strategic form" special case: outcome = utility vector, kernel = point mass.
    Absorbs the former `StrategicForm.Game`. -/
noncomputable def KernelGame.ofEU [DecidableEq ι]
    (Strategy : ι → Type) (eu : (∀ i, Strategy i) → Payoff ι) : KernelGame ι where
  Strategy := Strategy
  Outcome := Payoff ι
  utility := id
  outcomeKernel := fun σ => PMF.pure (eu σ)

variable {ι : Type} [DecidableEq ι]

/-- EU of a game built from `ofEU` is just the direct EU function. -/
@[simp] theorem KernelGame.eu_ofEU
    (S : ι → Type) (u : (∀ i, S i) → Payoff ι) (σ : ∀ i, S i) (i : ι) :
    (ofEU S u).eu σ i = u σ i := by
  simp [KernelGame.eu, ofEU, expect_pure]

/-- A strategy profile `σ` is a Nash equilibrium if no player can
    improve their utility by unilateral deviation. -/
def KernelGame.IsNash (G : KernelGame ι) (σ : KernelGame.Profile G) : Prop :=
  ∀ (who : ι) (s' : G.Strategy who),
    G.eu σ who ≥ G.eu (Function.update σ who s') who

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
-- Preference-parameterized solution concepts
-- ============================================================================

/-- A strategy profile is a Nash equilibrium w.r.t. a preference `pref` on outcome
    distributions if no player prefers the distribution from any unilateral deviation.

    This generalizes `IsNash` beyond expected utility: `pref who d₁ d₂` means
    player `who` (weakly) prefers outcome distribution `d₁` over `d₂`. -/
def KernelGame.IsNashFor (G : KernelGame ι)
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ : KernelGame.Profile G) : Prop :=
  ∀ (who : ι) (s' : G.Strategy who),
    pref who (G.outcomeKernel σ) (G.outcomeKernel (Function.update σ who s'))

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

end GameTheory
