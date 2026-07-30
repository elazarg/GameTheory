/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FiniteBiasEndpointDecomposition
import GameTheory.Concepts.Stochastic.PlayerNeutralBiasAlternative

/-!
# Finite-bias endpoint alternative

This file combines the mean-ergodic endpoint decomposition of a finite
analytic bias with the player-owned public-response alternative in its
Poisson-solvable branch.

The result is a four-way finite endpoint certificate. It makes no claim
that a public response has already been compiled into a punishment or that
a harmonic obstruction has already produced a recurrent child.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm
namespace FiniteBiasSeed

/-- A finite analytic endpoint bias yields exactly one of the certificate
forms needed by the next recursion step:

* the endpoint value is already a uniform equilibrium payoff;
* a fixed player-owned continuation-neutral action carries an operational
  public response for a Poisson-corrected bias;
* a nonzero harmonic obstruction is already in the processed span; or
* a new nonzero harmonic obstruction strictly decreases the remaining
  harmonic rank when adjoined to that span.

The public-response branch retains its Poisson correction and equation.
The harmonic branches retain the correction, forcing decomposition, and
the harmonic or residual identities used to justify the classification. -/
theorem
    uniformPayoff_or_publicResponse_or_processedObstruction_or_rankDecrease
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan)
    (s₀ : G.State) :
    G.IsUniformEquilibriumPayoff
        s₀ (germ.endpointValue s₀) ∨
    (∃ correction : G.State → Payoff ι,
      ∃ who, ∃ response : germ.ContinuationNeutralAction who,
        G.finkBellmanForcingVector
            germ.endpointValue seed.H germ.endpointFinkPoint =
          -G.finkContinuationResidualVector
            correction germ.endpointFinkPoint ∧
        Nonempty
          (G.FinkPublicConstraintResponse
            germ.endpointFinkPoint (seed.H - correction)
            response.source who response.1.2)) ∨
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
  rcases
      seed.poissonCorrection_or_processedObstruction_or_rankDecrease
        span with hPoisson | hProcessed | hNew
  · obtain ⟨correction, hCorrection⟩ := hPoisson
    rcases
        seed.exists_publicConstraintResponse_or_isUniformEquilibriumPayoff
          germ correction s₀ hCorrection with hResponse | hUniform
    · obtain ⟨who, response, hPublic⟩ := hResponse
      exact Or.inr <| Or.inl
        ⟨correction, who, response, hCorrection, hPublic⟩
    · exact Or.inl hUniform
  · exact Or.inr <| Or.inr <| Or.inl hProcessed
  · exact Or.inr <| Or.inr <| Or.inr hNew

end FiniteBiasSeed
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
