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
    improve their payoff by unilateral deviation. -/
def KernelGame.IsNash (G : KernelGame ι) (σ : KernelGame.Profile G) : Prop :=
  ∀ (who : ι) (s' : G.Strategy who),
    G.eu σ who ≥ G.eu (Function.update σ who s') who

/-- Action `s` is dominant for player `who` if, regardless of others'
    actions, `s` yields at least as high a payoff as any alternative. -/
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

end GameTheory
