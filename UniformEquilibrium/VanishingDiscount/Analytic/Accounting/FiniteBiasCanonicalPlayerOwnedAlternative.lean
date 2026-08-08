/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.PlayerOwned.CirculationEndpointAlternative
import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.FiniteBiasPlayerOwnedEndpointDriftPayoffAlternative

/-!
# Canonical player-owned alternative in the finite-bias branch

Fix a finite-bias seed, a Poisson correction, one public entry, and the
canonical player-owned bias `seed.H - correction`.  Applying the full-owner
charged-flow alternative at exactly this bias gives:

* one player-owned positive analytic circulation, together with its honest
  endpoint alternative; or
* one common scaled potential for every player's operational rows.

In the potential branch, the endpoint-drift payoff theorem either constructs
the eventual simultaneous unilateral deviation-payoff cap, extracts one
fixed visible forward transition response, or retains one fixed positive
endpoint drift whose transition germ is prescribed-indistinguishable.

Every branch below is constructed from existing evidence.  In particular,
the theorem does not package a desired punishment or equilibrium certificate
as an input record.  The deviation-cap branch is only the upper incentive
half of an adaptive equilibrium certificate; two-sided on-path realization
of the endpoint target remains separate.
-/

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

/-- The canonical finite-bias player-owned classification.

The first branch is a semantic payoff statement for arbitrary unilateral
behavior deviations.  The remaining branches preserve the exact analytic
circulation or endpoint-drift evidence from which later public responses,
accounts, or recursive children would have to be constructed. -/
theorem
    hasDeviationPayoffCap_or_circulationEndpoint_or_response_or_invisible
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          correction germ.endpointFinkPoint)
    (entry terminalAnchor : G.State) :
    (∃ P :
        AnalyticOwnerScaledChargedOccupationPotential
          (fun who => OwnerOccupationIndex G who)
          (fun who => germ.rawOwnerAnalyticOccupationColumn who)
          (fun who =>
            germ.rawPlayerOwnedOccupationCharge
              (seed.playerOwnedPoissonBias correction) who),
      HasEventualSimultaneousPlayerOwnedDeviationPayoffCap
        seed correction P entry) ∨
      (∃ (who : ι)
          (C : AnalyticPositiveChargedCirculation
            (germ.rawOwnerAnalyticOccupationColumn who)
            (germ.rawPlayerOwnedOccupationCharge
              (seed.playerOwnedPoissonBias correction) who)),
        Nonempty
          (PlayerOwnedCirculationEndpointAlternative
            germ (seed.playerOwnedPoissonBias correction) who C
              terminalAnchor)) ∨
        Nonempty
          (AnalyticPlayerOwnedEndpointDriftTransitionResponse germ) ∨
          Nonempty
            (AnalyticInvisiblePositivePlayerOwnedEndpointDrift germ) := by
  rcases
      seed.playerOwnedPositiveChargedCirculation_or_commonScaledPotential_of_poisson
        correction with hcirculation | hpotential
  · right
    left
    obtain ⟨who, ⟨C⟩⟩ := hcirculation
    exact
      ⟨who, C,
        germ.exists_playerOwnedCirculationEndpointAlternative
          (seed.playerOwnedPoissonBias correction) who C terminalAnchor⟩
  · obtain ⟨P⟩ := hpotential
    rcases
        seed.hasDeviationPayoffCap_or_endpointDriftResponse_or_invisible
          correction hPoisson P entry with hcap | hresponse | hinvisible
    · exact Or.inl ⟨P, hcap⟩
    · exact Or.inr (Or.inr (Or.inl hresponse))
    · exact Or.inr (Or.inr (Or.inr hinvisible))

end FiniteBiasSeed
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
