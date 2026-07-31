/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticPrescribedEndpointTailAlternative
import GameTheory.Concepts.Stochastic.FiniteBiasCanonicalSemanticAlternative

/-!
# Canonical transport-circulation alternative for finite bias

The semantic finite-bias endpoint alternative leaves failure of prescribed
endpoint transport as a negated asymptotic condition.  This file replaces
that negation by concrete finite-dimensional evidence.  It selects one
player for whom the exact retained calendar fails, then extracts:

* one fixed orientation of that player's endpoint displacement;
* a positive analytic circulation restricted to the actual tail-reachable
  source subtype;
* a punctured communicating class with positive aggregate oriented charge
  whose representative is support-reachable from a positive-mass tail
  state.

The branch retains the same Poisson correction, common potential, shifted
calendar, charge inequalities, and unilateral deviation-payoff caps.
All other branches pass through unchanged.  No branch is interpreted here
as a punishment, a legal recurrent child, or an equilibrium certificate.
-/

set_option autoImplicit false

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

/-- Concrete evidence retained when the prescribed endpoint target fails
on the canonical common-potential calendar. -/
structure CanonicalPrescribedTransportCirculationBranch
    (germ : G.AnalyticBellmanGerm)
    (seed : germ.FiniteBiasSeed)
    (entry : G.State) where
  correction : G.State → Payoff ι
  commonPotential :
    AnalyticOwnerScaledChargedOccupationPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who =>
        germ.rawPlayerOwnedOccupationCharge
          (seed.playerOwnedPoissonBias correction) who)
  startEpoch : ℕ
  valid :
    ∀ k : ℕ,
      shiftedUniversalEpochScale startEpoch k ∈
        Ioo (0 : ℝ) germ.radius
  poissonEquation :
    G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
      -G.finkContinuationResidualVector
        correction germ.endpointFinkPoint
  chargeBound :
    ∀ who k index,
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
              commonPotential who)
            (shiftedUniversalEpochScale startEpoch k))
          index
  deviationCaps :
    ∀ δ : ℝ, 0 < δ →
      ∀ᶠ T : ℕ in atTop,
        ∀ (who : ι) (dev : G.BehaviorStrategy who),
          G.finiteAveragePayoff entry T
              (scheduledPlayerOwnedFinkDeviationProfile
                germ who startEpoch valid dev)
              who ≤
            germ.endpointValue entry who + δ
  failingPlayer : ι
  transportCirculation :
    TailReachableEndpointTransportCirculationEvidence
      germ failingPlayer entry startEpoch valid

/-- The canonical finite-bias endpoint classification with failed
prescribed transport refined to an oriented analytic circulation and its
punctured positive-charge class.

The successful transport branch remains a uniform-equilibrium conclusion.
Every other outcome is evidence only. -/
theorem canonicalTransportCirculationAlternative
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan)
    (entry terminalAnchor : G.State) :
    G.IsUniformEquilibriumPayoff
        entry (germ.endpointValue entry) ∨
      Nonempty
        (CanonicalPrescribedTransportCirculationBranch
          germ seed entry) ∨
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
  rcases seed.canonicalSemanticAlternative span entry terminalAnchor with
      hEquilibrium | hTransport | hCirculation | hResponse | hInvisible |
        hProcessed | hRankDecrease
  · exact Or.inl hEquilibrium
  · obtain
        ⟨correction, commonPotential, startEpoch, valid, poissonEquation,
          chargeBound, deviationCaps, transportFailure⟩ := hTransport
    rw [HasSublinearPrescribedCalendarEndpointTargetTransport]
      at transportFailure
    obtain ⟨failingPlayer, playerFailure⟩ :=
      not_forall.mp transportFailure
    obtain ⟨transportCirculation⟩ :=
      germ.exists_tailReachableEndpointTransportCirculation_of_not_sublinear
        failingPlayer entry startEpoch valid playerFailure
    exact Or.inr <| Or.inl <| ⟨{
      correction := correction
      commonPotential := commonPotential
      startEpoch := startEpoch
      valid := valid
      poissonEquation := poissonEquation
      chargeBound := chargeBound
      deviationCaps := deviationCaps
      failingPlayer := failingPlayer
      transportCirculation := transportCirculation
    }⟩
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
