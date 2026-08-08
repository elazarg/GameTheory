/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.FiniteBiasCanonicalEndpointAlternative
import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.FiniteBiasPlayerOwnedUniformClosure

/-!
# Semantic finite-bias endpoint alternative

The canonical finite-bias endpoint classification already constructs a
simultaneous unilateral deviation-payoff cap in its successful
common-potential branch.  This file tests the only remaining semantic
condition on that exact calendar: two-sided sublinear prescribed endpoint
transport.

If the prescribed transport condition holds, the same calendar is a uniform
equilibrium realizing the endpoint target.  Otherwise all of the calendar's
Poisson, charge, and deviation-cap evidence is retained together with the
negated transport condition.  The latter is a precise obstruction to this
particular semantic closure, not a counterexample to the uniform-equilibrium
conjecture: another calendar, response, or recursive construction may still
close the game.

All other circulation, endpoint-response, processed-harmonic, and
rank-decrease branches pass through unchanged.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace FiniteBiasSeed

open Filter Math Math.OnlineLearning Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Exhaustive semantic refinement of the canonical finite-bias endpoint
alternative.

The second branch is deliberately the negation of prescribed transport on
the exact calendar that already carries the common-potential charge bound
and all unilateral deviation caps.  It assumes no final certificate. -/
theorem canonicalSemanticAlternative
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan)
    (entry terminalAnchor : G.State) :
    G.IsUniformEquilibriumPayoff
        entry (germ.endpointValue entry) ∨
      (∃ (correction : G.State → Payoff ι)
          (P :
            AnalyticOwnerScaledChargedOccupationPotential
              (fun who => OwnerOccupationIndex G who)
              (fun who => germ.rawOwnerAnalyticOccupationColumn who)
              (fun who =>
                germ.rawPlayerOwnedOccupationCharge
                  (seed.playerOwnedPoissonBias correction) who))
          (startEpoch : ℕ)
          (valid :
            ∀ k : ℕ,
              shiftedUniversalEpochScale startEpoch k ∈
                Ioo (0 : ℝ) germ.radius),
        G.finkBellmanForcingVector
              germ.endpointValue seed.H germ.endpointFinkPoint =
            -G.finkContinuationResidualVector
              correction germ.endpointFinkPoint ∧
          (∀ who k index,
            germ.rawPlayerOwnedOccupationCharge
                  (seed.playerOwnedPoissonBias correction) who
                  (shiftedUniversalEpochScale startEpoch k) index ≤
              transitionPotentialDrift
                (germ.finkOwnerActualOccupationKernelAt (valid k) who)
                (ownerActualOccupationSource who)
                (germ.puncturedPlayerOwnedPotentialAt
                  (seed.playerOwnedPoissonBias correction) who
                  (CommonPlayerOwnedPotentialCalendar.ownerPotential
                    germ (seed.playerOwnedPoissonBias correction)
                    P who)
                  (shiftedUniversalEpochScale startEpoch k))
                index) ∧
            (∀ δ : ℝ, 0 < δ →
              ∀ᶠ T : ℕ in atTop,
                ∀ (who : ι) (dev : G.BehaviorStrategy who),
                  G.finiteAveragePayoff entry T
                      (scheduledPlayerOwnedFinkDeviationProfile
                        germ who startEpoch valid dev)
                      who ≤
                    germ.endpointValue entry who + δ) ∧
              ¬HasSublinearPrescribedCalendarEndpointTargetTransport
                germ entry startEpoch valid) ∨
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
  rcases seed.canonicalEndpointAlternative span entry terminalAnchor with
      hCap | hCirculation | hResponse | hInvisible | hProcessed |
        hRankDecrease
  · obtain ⟨correction, P, hPoisson, hCap⟩ := hCap
    obtain ⟨startEpoch, valid, hcharge, deviationCaps⟩ := hCap
    by_cases hTransport :
        HasSublinearPrescribedCalendarEndpointTargetTransport
          germ entry startEpoch valid
    · exact
        Or.inl
          (seed.isUniformEquilibriumPayoff_of_prescribedTransport_of_deviationCaps
            correction hPoisson entry startEpoch valid hTransport
              deviationCaps)
    · exact
        Or.inr <| Or.inl
          ⟨correction, P, startEpoch, valid, hPoisson, hcharge,
            deviationCaps, hTransport⟩
  · exact Or.inr <| Or.inr <| Or.inl hCirculation
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl hResponse
  · exact
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hInvisible
  · exact
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inl hProcessed
  · exact
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr hRankDecrease

end FiniteBiasSeed
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
