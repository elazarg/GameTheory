/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Basic
import GameTheory.Concepts.Equilibrium.ApproximateNash

/-!
# Uniform Equilibrium in Stochastic Games

Uniform solution concepts for stochastic games under finite-horizon average
payoffs, and the statement of the **uniform equilibrium existence problem**:
every stochastic game with finitely many players, finitely many states, and
finitely many actions admits a uniform equilibrium payoff from every initial
state.

A behavior profile is a *uniform ε-equilibrium* if a single horizon threshold
`T₀`, depending only on `ε`, makes it an ε-Nash equilibrium of every game
with horizon at least `T₀`.  A payoff vector `v` is a *uniform equilibrium
payoff* if for every `ε > 0` some profile is a uniform ε-equilibrium whose
long finite-horizon average payoffs are all within `ε` of `v`.

The ε-formulation is essential: exact (`ε = 0`) uniform equilibria can fail
to exist even in two-player zero-sum games — the Big Match
(Blackwell–Ferguson 1968) has no optimal strategies, only ε-optimal ones.

## Status of the existence problem

* Two-player zero-sum games have a uniform value (Mertens–Neyman 1981).
* Two-player games admit uniform equilibrium payoffs (Vieille 2000).
* Three-player absorbing games admit them (Solan 1999).
* The general n-player case is **open**; it is the central open problem of
  the field (Mertens 1986; Solan–Vieille 2010).

The statement is recorded here as
`StochasticGame.exists_uniformEquilibriumPayoff` with a `sorry` that must
remain until the statement is actually proved.  Special cases proved in this
development so far live in `GameTheory.Concepts.Stochastic.Absorbing`.

## Main definitions

* `StochasticGame.IsεHorizonNash` — ε-Nash equilibrium of the `T`-stage game
  under expected average payoffs
* `StochasticGame.IsUniformεEquilibrium` — ε-Nash of every sufficiently long
  finite-horizon game, with one horizon threshold
* `StochasticGame.IsUniformEquilibriumPayoff` — uniform equilibrium payoff

## Main statements

* `StochasticGame.exists_uniformEquilibriumPayoff` — the open conjecture
  (stated with `sorry`)
* `StochasticGame.exists_isUniformεEquilibrium` — for every `ε > 0` some
  profile is a uniform ε-equilibrium (derived from the conjecture)
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

variable {ι : Type}

/-- `σ` is an ε-Nash equilibrium of the `T`-stage game from `s₀` under
expected average payoffs: no unilateral replacement of a whole behavior
strategy gains more than `ε`. -/
def IsεHorizonNash (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (T : ℕ) (ε : ℝ) (σ : G.BehaviorProfile) : Prop :=
  ∀ who (dev : G.BehaviorStrategy who),
    G.finiteAveragePayoff s₀ T σ who + ε ≥
      G.finiteAveragePayoff s₀ T (Function.update σ who dev) who

/-- Uniform ε-equilibrium from `s₀`: a single horizon threshold `T₀` past
which `σ` is an ε-Nash equilibrium of every longer finite-horizon game. -/
def IsUniformεEquilibrium (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (ε : ℝ) (σ : G.BehaviorProfile) : Prop :=
  ∃ T₀ : ℕ, ∀ T, T₀ ≤ T → G.IsεHorizonNash s₀ T ε σ

/-- `v` is a **uniform equilibrium payoff** of `G` from initial state `s₀`:
for every `ε > 0` there are a behavior profile `σ` and a horizon threshold
`T₀` such that in every game of horizon at least `T₀`, `σ` is an ε-Nash
equilibrium and every player's expected average payoff under `σ` is within
`ε` of `v`. -/
def IsUniformEquilibriumPayoff (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] (s₀ : G.State) (v : Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (σ : G.BehaviorProfile) (T₀ : ℕ), ∀ T, T₀ ≤ T →
    G.IsεHorizonNash s₀ T ε σ ∧
      ∀ who, |G.finiteAveragePayoff s₀ T σ who - v who| ≤ ε

/-- Finite-horizon approximate Nash is monotone in the error allowance. -/
theorem IsεHorizonNash.mono {G : StochasticGame ι} [Fintype ι]
    [DecidableEq ι] {s₀ : G.State} {T : ℕ} {ε ε' : ℝ}
    {σ : G.BehaviorProfile}
    (h : G.IsεHorizonNash s₀ T ε σ) (hε : ε ≤ ε') :
    G.IsεHorizonNash s₀ T ε' σ := by
  intro who dev
  have := h who dev
  linarith

/-- Uniform approximate equilibrium is monotone in the error allowance. -/
theorem IsUniformεEquilibrium.mono {G : StochasticGame ι} [Fintype ι]
    [DecidableEq ι] {s₀ : G.State} {ε ε' : ℝ} {σ : G.BehaviorProfile}
    (h : G.IsUniformεEquilibrium s₀ ε σ) (hε : ε ≤ ε') :
    G.IsUniformεEquilibrium s₀ ε' σ := by
  obtain ⟨T₀, hT₀⟩ := h
  exact ⟨T₀, fun T hT => (hT₀ T hT).mono hε⟩

/-- Per horizon, a stochastic game *is* a kernel game: `IsεHorizonNash` is
exactly `KernelGame.IsεNash` of the horizon game (`horizonGame`), whose
strategies are whole behavior strategies.  What is not a single kernel game
is the uniform concept, which quantifies over every horizon with one
profile. -/
theorem isεHorizonNash_iff_horizonGame (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] (s₀ : G.State) (T : ℕ) (ε : ℝ) (σ : G.BehaviorProfile) :
    G.IsεHorizonNash s₀ T ε σ ↔ (G.horizonGame s₀ T).IsεNash ε σ := by
  constructor
  · intro hN who dev
    rw [eu_horizonGame, eu_horizonGame]
    exact hN who dev
  · intro hN who dev
    have h := hN who dev
    rw [eu_horizonGame, eu_horizonGame] at h
    exact h

/-- **The uniform equilibrium existence problem.**

Every stochastic game with finitely many players, finitely many states, and
finitely many nonempty action sets admits a uniform equilibrium payoff from
every initial state.

This is the central open problem of stochastic game theory.  Known cases:
two-player zero-sum games (Mertens–Neyman 1981), two-player games
(Vieille 2000), three-player absorbing games (Solan 1999), and various
structured classes (recursive games, quitting games under conditions).  The
general n-player case is open; consequently this statement carries a `sorry`
that must remain until the statement is actually proved.  Do not remove the
`sorry` by weakening the statement. -/
theorem exists_uniformEquilibriumPayoff (G : StochasticGame ι)
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (s₀ : G.State) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  sorry

/-- For every `ε > 0`, some behavior profile is a uniform ε-equilibrium.
Derived from the uniform equilibrium existence problem
(`exists_uniformEquilibriumPayoff`), hence currently conditional on its
`sorry`. -/
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
