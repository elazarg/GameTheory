/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Uniform

/-!
# The uniform-equilibrium existence conjecture

This file contains **the central open problem of stochastic game theory** and
nothing else: every finite stochastic game admits a uniform equilibrium payoff
from every initial state.

It is separated from `Uniform.lean`, which carries the definitions and the
semantic/quantitative equivalence and is fully proved, so that the `sorry`
warning emitted by a build names the conjecture rather than a definitions
module.

## Open declarations

`exists_uniformDeviationCapConstructor` is an **intentional open declaration**.
It is the quantitative form of the conjecture, equivalent to the semantic form
by `hasUniformDeviationCapConstructor_iff`, and the two derived theorems below
are one-line consequences of it.

Known cases: two-player zero-sum games (Mertens--Neyman 1981), two-player games
(Vieille 2000), three-player absorbing games (Solan 1999), and various
structured classes.  The general `n`-player case is open.

The repository's other intentional open declaration is
`quittingGame_exists_uniformEquilibriumPayoff` in `QuittingConjecture.lean`,
the *finite-quitting* case.  Discharging it would **not** discharge this file:
quitting games are a strict subclass, and no reduction from arbitrary finite
stochastic games to them is known.

## The `sorry` here does not assert belief

A counterexample to approximate-equilibrium existence in finite-state,
finite-action stochastic games is **claimed** in the literature: R. S. Simon,
*A Stochastic Game without Approximate Equilibria*, arXiv:2310.04217 (2023),
a four-player "Mousetrap".  Whether its hypotheses fall inside the ones stated
below -- in particular whether its payoff is a limit average of stage payoffs
and whether perfect monitoring survives its stage-combining reduction -- has
not been settled in this repository.  Until it is, read the `sorry` as *not
proved here*, not as *believed true*.  If the claim stands at these
hypotheses, this statement is false and must be replaced rather than proved.
-/

namespace GameTheory

namespace StochasticGame

variable {ι : Type}

/-- Quantitative form of the uniform-equilibrium existence problem.

This statement is logically equivalent to
`exists_uniformEquilibriumPayoff`; it is the proof-construction waist at
which analytic hierarchy, public-response, coupling, and sublinear-ledger
arguments meet. -/
theorem exists_uniformDeviationCapConstructor (G : StochasticGame ι)
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (s₀ : G.State) :
    ∃ v : Payoff ι, G.HasUniformDeviationCapConstructor s₀ v := by
  sorry

/-- **The uniform equilibrium existence problem.**

Every stochastic game with finitely many players, finitely many states, and
finitely many nonempty action sets admits a uniform equilibrium payoff from
every initial state.

This is the central open problem of stochastic game theory.  Known cases:
two-player zero-sum games (Mertens–Neyman 1981), two-player games
(Vieille 2000), three-player absorbing games (Solan 1999), and various
structured classes (recursive games, quitting games under conditions).  The
general n-player case is open.  The theorem is derived from the equivalent
quantitative constructor above; no weakening of the semantic statement is
involved. -/
theorem exists_uniformEquilibriumPayoff (G : StochasticGame ι)
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (s₀ : G.State) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  obtain ⟨v, hv⟩ := G.exists_uniformDeviationCapConstructor s₀
  exact ⟨v, (G.hasUniformDeviationCapConstructor_iff s₀ v).mp hv⟩

/-- For every `ε > 0`, some behavior profile is a uniform ε-equilibrium.
Derived from the uniform equilibrium existence problem through its exact
quantitative constructor formulation. -/
theorem exists_isUniformεEquilibrium (G : StochasticGame ι)
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (s₀ : G.State)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : G.BehaviorProfile, G.IsUniformεEquilibrium s₀ ε σ := by
  obtain ⟨v, hv⟩ := G.exists_uniformEquilibriumPayoff s₀
  obtain ⟨σ, T₀, h⟩ := hv ε hε
  exact ⟨σ, T₀, fun T hT => (h T hT).1⟩


end StochasticGame

end GameTheory
