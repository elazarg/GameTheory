import GameTheory.SolutionConcepts

/-!
# Bayesian Games (Games with Incomplete Information)

A Bayesian game models situations where players have private information
(types) that affect payoffs. Each player knows their own type but only
has a prior belief over other players' types. Harsanyi (1967-68) showed
that such games can be analyzed via the "type-agent" representation.

## Main definitions

* `BayesianGame` — Bayesian game structure with types, actions, and type-conditional payoffs
* `BayesianGame.toKernelGame` — reduction to a KernelGame (strategy = type → action)
* `BayesianGame.BayesNash` — Bayes-Nash equilibrium
* `BayesianGame.exAnteEU` — ex-ante expected utility

## Main results

* `BayesNash_iff_isNash` — Bayes-Nash equilibrium ↔ Nash of the type-agent game
-/

namespace GameTheory

/-- A Bayesian game with private types and common prior.

  Each player `i` has:
  - A type space `Θ i` (private information)
  - An action set `Act i`
  - A utility function depending on the joint type and joint action

  The common prior `μ` is a joint distribution over all types. -/
structure BayesianGame (ι : Type) [Fintype ι] where
  /-- Type space for each player. -/
  Θ : ι → Type
  [instFintypeΘ : ∀ i, Fintype (Θ i)]
  [instNonemptyΘ : ∀ i, Nonempty (Θ i)]
  /-- Action set for each player. -/
  Act : ι → Type
  [instFintypeAct : ∀ i, Fintype (Act i)]
  [instNonemptyAct : ∀ i, Nonempty (Act i)]
  /-- Common prior over joint types. -/
  prior : PMF (∀ i, Θ i)
  /-- Type-and-action-dependent payoff. -/
  utility : (∀ i, Θ i) → (∀ i, Act i) → ι → ℝ

attribute [instance] BayesianGame.instFintypeΘ BayesianGame.instNonemptyΘ
  BayesianGame.instFintypeAct BayesianGame.instNonemptyAct

namespace BayesianGame

variable {ι : Type} [Fintype ι]

/-- A (pure) strategy in a Bayesian game: a map from own type to action. -/
abbrev Strategy (B : BayesianGame ι) (i : ι) := B.Θ i → B.Act i

/-- A strategy profile: each player has a type-dependent strategy. -/
abbrev BProfile (B : BayesianGame ι) := ∀ i, B.Strategy i

/-- Ex-ante expected utility: expected payoff before types are drawn,
    given a strategy profile. -/
noncomputable def exAnteEU (B : BayesianGame ι) (σ : B.BProfile) (who : ι) : ℝ :=
  expect B.prior (fun θ => B.utility θ (fun i => σ i (θ i)) who)

open Classical in
/-- Reduce to a KernelGame where strategies are type-to-action maps. -/
noncomputable def toKernelGame (B : BayesianGame ι) : KernelGame ι :=
  KernelGame.ofEU B.Strategy (fun σ i => B.exAnteEU σ i)

/-- Bayes-Nash equilibrium: no player can improve ex-ante EU by changing
    their type-dependent strategy. -/
def BayesNash (B : BayesianGame ι) (σ : B.BProfile) : Prop :=
  B.toKernelGame.IsNash σ

/-- Bayes-Nash is exactly Nash of the induced strategic-form game. -/
theorem bayesNash_iff_isNash (B : BayesianGame ι) (σ : B.BProfile) :
    B.BayesNash σ ↔ B.toKernelGame.IsNash σ :=
  Iff.rfl

open Classical in
/-- Bayes-Nash equilibrium characterized directly: for each player and
    each alternative strategy, ex-ante EU doesn't improve. -/
theorem bayesNash_iff_exAnteEU (B : BayesianGame ι) (σ : B.BProfile) :
    B.BayesNash σ ↔ ∀ (who : ι) (s' : B.Strategy who),
      B.exAnteEU σ who ≥ B.exAnteEU (Function.update σ who s') who := by
  constructor
  · intro hN who s'
    have := hN who s'
    simp only [toKernelGame, KernelGame.eu, KernelGame.ofEU, expect_pure] at this
    exact this
  · intro h who s'
    simp only [toKernelGame, KernelGame.eu, KernelGame.ofEU, expect_pure]
    exact h who s'

end BayesianGame

end GameTheory
