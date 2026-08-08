/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticBellmanHierarchy

/-!
# Endpoint decomposition of finite analytic bias

The forcing associated with a finite-bias seed has a mean-ergodic
decomposition into an endpoint-harmonic vector and a continuation residual.
Relative to a span of harmonic jets already processed, this gives three
purely linear-algebraic cases:

* the harmonic vector is zero, so the forcing has a Poisson correction;
* the nonzero harmonic vector is already in the processed span;
* adjoining the nonzero harmonic vector strictly decreases the remaining
  harmonic dimension.

This file does not construct a public response, a recurrent child, or a
punishment strategy.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm
namespace FiniteBiasSeed

omit [DecidableEq G.State] in
/-- Endpoint finite-bias forcing is Poisson-solvable, has a nonzero
harmonic obstruction already represented by the processed span, or has a
nonzero new harmonic obstruction whose adjunction strictly decreases the
remaining harmonic rank.

The correction is oriented so that every displayed decomposition uses
`forcing = harmonic - continuationResidual correction`. -/
theorem
    poissonCorrection_or_processedObstruction_or_rankDecrease
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) :
    (∃ correction : G.State → Payoff ι,
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          correction germ.endpointFinkPoint) ∨
    (∃ obstruction correction : G.State → Payoff ι,
      obstruction ≠ 0 ∧
      obstruction ∈ span.carrier ∧
      G.finkContinuationResidualVector
          obstruction germ.endpointFinkPoint = 0 ∧
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        obstruction -
          G.finkContinuationResidualVector
            correction germ.endpointFinkPoint) ∨
    ∃ obstruction correction : G.State → Payoff ι,
      ∃ harmonic :
          obstruction ∈ germ.endpointHarmonicSubmodule,
        obstruction ≠ 0 ∧
        obstruction ∉ span.carrier ∧
        G.finkBellmanForcingVector
            germ.endpointValue seed.H germ.endpointFinkPoint =
          obstruction -
            G.finkContinuationResidualVector
              correction germ.endpointFinkPoint ∧
        (span.extend obstruction harmonic).rank < span.rank := by
  obtain ⟨obstruction, rawCorrection, hharmonic, hforcing, _⟩ :=
    G.exists_finkBellmanForcing_harmonicObstruction_decomposition
      germ.endpointFinkPoint germ.endpointValue seed.H
  by_cases hzero : obstruction = 0
  · left
    refine ⟨-rawCorrection, ?_⟩
    rw [hforcing, hzero, zero_add,
      G.finkContinuationResidualVector_neg]
    simp
  · by_cases hprocessed : obstruction ∈ span.carrier
    · right
      left
      refine
        ⟨obstruction, -rawCorrection, hzero, hprocessed,
          hharmonic, ?_⟩
      rw [hforcing, G.finkContinuationResidualVector_neg]
      simp
    · right
      right
      have hHarmonic :
          obstruction ∈ germ.endpointHarmonicSubmodule :=
        (germ.mem_endpointHarmonicSubmodule_iff obstruction).2
          hharmonic
      refine
        ⟨obstruction, -rawCorrection, hHarmonic, hzero,
          hprocessed, ?_, ?_⟩
      · rw [hforcing, G.finkContinuationResidualVector_neg]
        simp
      · exact
          span.rank_extend_lt obstruction hHarmonic hprocessed

end FiniteBiasSeed
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
