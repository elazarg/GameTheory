/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Uniform

/-!
# Asymptotic Payoff Functionals in Stochastic Games

This file connects uniform finite-horizon equilibria to arbitrary payoff
functionals obtained as pointwise limits of finite-average payoffs.  The main
application is to absorbing and quitting games, where the limiting functional
is expected terminal reward.

The convergence need not be uniform over unilateral deviations.  Each Nash
inequality fixes one deviation before its two sides are passed to the limit.

## Main results

* `StochasticGame.isεAsymptoticNash_of_isUniformεEquilibrium` — a uniform
  finite-horizon approximate equilibrium remains an approximate equilibrium
  for a pointwise limiting payoff functional
* `StochasticGame.not_exists_uniformEquilibriumPayoff_of_no_asymptoticNash` —
  the contrapositive interface used by counterexample arguments
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

open Filter

variable {ι : Type}

/-- Approximate Nash equilibrium for an arbitrary payoff functional on
behavior profiles. -/
def IsεAsymptoticNash (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (u : G.BehaviorProfile → ι → ℝ) (ε : ℝ)
    (σ : G.BehaviorProfile) : Prop :=
  ∀ who (dev : G.BehaviorStrategy who),
    u σ who + ε ≥ u (Function.update σ who dev) who

/-- A uniform finite-horizon epsilon-equilibrium is an epsilon-equilibrium
for every payoff functional obtained as the pointwise limit of finite-average
payoffs.

Only the on-path profile and one fixed deviation are used in each limiting
inequality, so pointwise convergence is sufficient. -/
theorem isεAsymptoticNash_of_isUniformεEquilibrium
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (u : G.BehaviorProfile → ι → ℝ)
    {ε : ℝ} {σ : G.BehaviorProfile}
    (hσ : G.IsUniformεEquilibrium s₀ ε σ)
    (hlim : ∀ (τ : G.BehaviorProfile) who,
      Tendsto (fun T => G.finiteAveragePayoff s₀ T τ who)
        atTop (nhds (u τ who))) :
    G.IsεAsymptoticNash u ε σ := by
  obtain ⟨T₀, hT₀⟩ := hσ
  intro who dev
  apply le_of_tendsto_of_tendsto
    (hlim (Function.update σ who dev) who)
    ((hlim σ who).add tendsto_const_nhds)
  filter_upwards [eventually_ge_atTop T₀] with T hT
  exact hT₀ T hT who dev

/-- A uniform equilibrium payoff supplies an approximate Nash equilibrium for
every pointwise limiting payoff functional. -/
theorem exists_isεAsymptoticNash_of_isUniformEquilibriumPayoff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (u : G.BehaviorProfile → ι → ℝ) (v : Payoff ι)
    (hv : G.IsUniformEquilibriumPayoff s₀ v)
    {ε : ℝ} (hε : 0 < ε)
    (hlim : ∀ (τ : G.BehaviorProfile) who,
      Tendsto (fun T => G.finiteAveragePayoff s₀ T τ who)
        atTop (nhds (u τ who))) :
    ∃ σ : G.BehaviorProfile, G.IsεAsymptoticNash u ε σ := by
  obtain ⟨σ, T₀, hσ⟩ := hv ε hε
  refine ⟨σ, G.isεAsymptoticNash_of_isUniformεEquilibrium s₀ u ?_ hlim⟩
  exact ⟨T₀, fun T hT => (hσ T hT).1⟩

/-- Contrapositive bridge for refutation arguments: if some positive error
admits no approximate Nash equilibrium for a pointwise limiting payoff
functional, then there is no uniform equilibrium payoff. -/
theorem not_exists_uniformEquilibriumPayoff_of_no_asymptoticNash
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (u : G.BehaviorProfile → ι → ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hno : ¬ ∃ σ : G.BehaviorProfile, G.IsεAsymptoticNash u ε σ)
    (hlim : ∀ (τ : G.BehaviorProfile) who,
      Tendsto (fun T => G.finiteAveragePayoff s₀ T τ who)
        atTop (nhds (u τ who))) :
    ¬ ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  rintro ⟨v, hv⟩
  exact hno (G.exists_isεAsymptoticNash_of_isUniformEquilibriumPayoff
    s₀ u v hv hε hlim)

end StochasticGame

end GameTheory
