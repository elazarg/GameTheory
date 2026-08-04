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
`quitting_zeroSolo_or_admissibleCycle` in `QuittingConjecture.lean`, which is
the remaining premise of the *finite-quitting* route.  Discharging it would
close finite quitting games and would **not** discharge this file: quitting
games are a strict subclass, and no reduction from arbitrary finite stochastic
games to them is known.
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
