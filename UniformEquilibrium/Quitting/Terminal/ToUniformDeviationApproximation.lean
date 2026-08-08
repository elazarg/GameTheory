/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.HorizonBridge

/-!
# From asymptotic Nash to uniform finite-horizon Nash

This file isolates the exact one-sided approximation needed to turn Nash
inequalities for a limiting payoff functional into uniform finite-horizon
Nash inequalities for the same profile.

For every long horizon and every finite-horizon deviation, the approximation
property supplies a (possibly different) deviation whose limiting payoff
dominates the finite-horizon deviation payoff up to a prescribed error.  This
is deliberately one-sided.  Uniform absolute convergence over all deviations
is stronger and is false in quitting games: a player can postpone a quit past
the current horizon.

The generic transfer theorem also uses ordinary pointwise convergence only
for the prescribed profile.  The quitting-specific content of
Solan--Vieille Proposition 2.13 is precisely to establish the one-sided
approximation property from the unique live history and stopping-time
structure of a quitting game.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter

variable {ι : Type}

/-- Every sufficiently long finite-horizon unilateral payoff is bounded by
the limiting payoff of some unilateral deviation, uniformly over the player
and the finite-horizon deviation. -/
def HasUniformDeviationUpperApproximation
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (initial : G.State) (u : G.BehaviorProfile → ι → ℝ)
    (profile : G.BehaviorProfile) : Prop :=
  ∀ error : ℝ, 0 < error →
    ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
      ∀ who (finiteDeviation : G.BehaviorStrategy who),
        ∃ limitingDeviation : G.BehaviorStrategy who,
          G.finiteAveragePayoff initial horizon
              (Function.update profile who finiteDeviation) who ≤
            u (Function.update profile who limitingDeviation) who + error

/-- The one-sided deviation approximation plus prescribed pointwise
convergence transfers an asymptotic epsilon-Nash inequality to every strictly
larger uniform finite-horizon error. -/
theorem isUniformεEquilibrium_of_isεAsymptoticNash_of_upperApproximation
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (initial : G.State) (u : G.BehaviorProfile → ι → ℝ)
    (profile : G.BehaviorProfile) {ε ε' : ℝ} (herror : ε < ε')
    (hnash : G.IsεAsymptoticNash u ε profile)
    (happrox : G.HasUniformDeviationUpperApproximation
      initial u profile)
    (hprescribed : ∀ who,
      Tendsto (fun horizon =>
        G.finiteAveragePayoff initial horizon profile who)
        atTop (nhds (u profile who))) :
    G.IsUniformεEquilibrium initial ε' profile := by
  let margin : ℝ := (ε' - ε) / 2
  have hmargin : 0 < margin := by
    dsimp [margin]
    linarith
  obtain ⟨deviationThreshold, hdeviation⟩ :=
    happrox margin hmargin
  have hprescribedEventually : ∀ᶠ horizon in atTop, ∀ who,
      |G.finiteAveragePayoff initial horizon profile who -
        u profile who| < margin := by
    apply Filter.eventually_all.mpr
    intro who
    have hball := (hprescribed who).eventually
      (Metric.ball_mem_nhds (u profile who) hmargin)
    filter_upwards [hball] with horizon hclose
    simpa only [Metric.mem_ball, Real.dist_eq] using hclose
  obtain ⟨prescribedThreshold, hprescribedThreshold⟩ :=
    Filter.eventually_atTop.1 hprescribedEventually
  refine ⟨max deviationThreshold prescribedThreshold,
    fun horizon hhorizon who finiteDeviation => ?_⟩
  obtain ⟨limitingDeviation, hfinite⟩ :=
    hdeviation horizon
      (le_trans (Nat.le_max_left _ _) hhorizon) who finiteDeviation
  have hterminal := hnash who limitingDeviation
  have honPath := hprescribedThreshold horizon
    (le_trans (Nat.le_max_right _ _) hhorizon) who
  rw [abs_lt] at honPath
  dsimp [margin] at hfinite honPath
  linarith

end StochasticGame
end GameTheory

