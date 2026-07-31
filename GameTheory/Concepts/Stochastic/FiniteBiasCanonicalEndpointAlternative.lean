/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FiniteBiasCanonicalPlayerOwnedAlternative
import GameTheory.Concepts.Stochastic.FiniteBiasEndpointDecomposition

/-!
# Canonical finite-bias endpoint alternative

This file connects the finite-bias endpoint decomposition directly to the
canonical full-owner alternative.  Starting from only a finite-bias seed, a
processed harmonic span, a public entry, and a terminal anchor, it returns
one of six evidence-preserving outcomes:

* a constructed simultaneous unilateral deviation-payoff cap;
* a player-owned positive circulation and its endpoint alternative;
* a visible positive endpoint-drift response;
* an invisible positive endpoint-drift witness;
* a processed nonzero harmonic obstruction; or
* a new harmonic direction with strict rank decrease.

Every outcome retains the Poisson correction and forcing equation, or the
harmonic decomposition, from which it was obtained.  No branch assumes a
punishment or final equilibrium certificate.  In particular, the
deviation-cap branch still needs a separate two-sided on-path realization
of the endpoint target.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace FiniteBiasSeed

open Math Math.Probability

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Exhaustive canonical endpoint classification for a finite-bias seed.

The first four branches retain the exact Poisson correction used by the
player-owned classification.  The last two retain the full processed or
rank-decreasing harmonic decomposition. -/
theorem
    canonicalEndpointAlternative
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan)
    (entry terminalAnchor : G.State) :
    (∃ (correction : G.State → Payoff ι)
        (P :
          AnalyticOwnerScaledChargedOccupationPotential
            (fun who => OwnerOccupationIndex G who)
            (fun who => germ.rawOwnerAnalyticOccupationColumn who)
            (fun who =>
              germ.rawPlayerOwnedOccupationCharge
                (seed.playerOwnedPoissonBias correction) who)),
      G.finkBellmanForcingVector
            germ.endpointValue seed.H germ.endpointFinkPoint =
          -G.finkContinuationResidualVector
            correction germ.endpointFinkPoint ∧
        HasEventualSimultaneousPlayerOwnedDeviationPayoffCap
          seed correction P entry) ∨
      (∃ (correction : G.State → Payoff ι)
          (who : ι)
          (C : AnalyticPositiveChargedCirculation
            (germ.rawOwnerAnalyticOccupationColumn who)
            (germ.rawPlayerOwnedOccupationCharge
              (seed.playerOwnedPoissonBias correction) who)),
        G.finkBellmanForcingVector
              germ.endpointValue seed.H germ.endpointFinkPoint =
            -G.finkContinuationResidualVector
              correction germ.endpointFinkPoint ∧
          Nonempty
            (PlayerOwnedCirculationEndpointAlternative
              germ (seed.playerOwnedPoissonBias correction) who C
                terminalAnchor)) ∨
        (∃ (correction : G.State → Payoff ι),
          G.finkBellmanForcingVector
                germ.endpointValue seed.H germ.endpointFinkPoint =
              -G.finkContinuationResidualVector
                correction germ.endpointFinkPoint ∧
            Nonempty
              (AnalyticPlayerOwnedEndpointDriftTransitionResponse germ)) ∨
          (∃ (correction : G.State → Payoff ι),
            G.finkBellmanForcingVector
                  germ.endpointValue seed.H germ.endpointFinkPoint =
              -G.finkContinuationResidualVector
                correction germ.endpointFinkPoint ∧
              Nonempty
                (AnalyticInvisiblePositivePlayerOwnedEndpointDrift germ)) ∨
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
                          germ.endpointValue seed.H
                            germ.endpointFinkPoint =
                        obstruction -
                          G.finkContinuationResidualVector
                            correction germ.endpointFinkPoint ∧
                      (span.extend obstruction harmonic).rank <
                        span.rank := by
  rcases
      seed.poissonCorrection_or_processedObstruction_or_rankDecrease span
      with hPoisson | hProcessed | hRankDecrease
  · obtain ⟨correction, hCorrection⟩ := hPoisson
    rcases
        seed.hasDeviationPayoffCap_or_circulationEndpoint_or_response_or_invisible
          correction hCorrection entry terminalAnchor
        with hCap | hCirculation | hResponse | hInvisible
    · obtain ⟨P, hCap⟩ := hCap
      exact Or.inl ⟨correction, P, hCorrection, hCap⟩
    · obtain ⟨who, C, hEndpoint⟩ := hCirculation
      exact
        Or.inr <| Or.inl
          ⟨correction, who, C, hCorrection, hEndpoint⟩
    · exact
        Or.inr <| Or.inr <| Or.inl
          ⟨correction, hCorrection, hResponse⟩
    · exact
        Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨correction, hCorrection, hInvisible⟩
  · exact
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hProcessed
  · exact
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr hRankDecrease

end FiniteBiasSeed
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
