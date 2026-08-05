/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticPlayerOwnedEndpointDriftAlternative

/-!
# Finite-bias payoff alternative from endpoint drift

This file is the direct semantic consumer of
`exists_movingSuperharmonicBurnIn_or_endpointDriftResponse_or_invisible`.

In the finite-bias Poisson branch, fix the canonical player-owned bias
`seed.H - correction` and a common scaled potential for every player's
actual operational rows.  The analytic endpoint-drift alternative gives:

* a moving-superharmonic calendar burn-in;
* one fixed owned action with a centered transition monitor; or
* one fixed owned action with positive endpoint drift whose transition germ
  is prescribed-indistinguishable.

In the first branch, the common potential's charge-validity burn-in is
synchronized with the superharmonic burn-in.  The resulting zero
target-transport account is passed to the existing finite-bias payoff
compiler.  The conclusion is the actual eventual simultaneous unilateral
deviation-payoff cap, for every positive accuracy, under one common
prescribed Fink calendar.

This remains only the deviation-cap half of an adaptive equilibrium
certificate.  A two-sided on-path realization of the endpoint target is
still a separate obligation.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace FiniteBiasSeed

open Filter Math Math.OnlineLearning Math.Probability Set Topology

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- The actual simultaneous unilateral deviation-payoff cap supplied by one
common finite-bias player-owned calendar.

The charge inequality is retained in the predicate because it is the exact
local input consumed by the payoff compiler; the cap itself is a semantic
conclusion about arbitrary behavior deviations and is not an assumed record
field. -/
def HasEventualSimultaneousPlayerOwnedDeviationPayoffCap
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (P : AnalyticOwnerScaledChargedOccupationPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who =>
        germ.rawPlayerOwnedOccupationCharge
          (seed.playerOwnedPoissonBias correction) who))
    (entry : G.State) : Prop :=
  ∃ (startEpoch : ℕ)
      (valid :
        ∀ k : ℕ,
          shiftedUniversalEpochScale startEpoch k ∈
            Ioo (0 : ℝ) germ.radius),
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
              germ (seed.playerOwnedPoissonBias correction) P who)
            (shiftedUniversalEpochScale startEpoch k))
          index) ∧
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ T : ℕ in atTop,
          ∀ (who : ι) (dev : G.BehaviorStrategy who),
            G.finiteAveragePayoff entry T
                (scheduledPlayerOwnedFinkDeviationProfile
                  germ who startEpoch valid dev)
                who ≤
              germ.endpointValue entry who + δ

/-- Once a common calendar carries both moving endpoint
superharmonicity and the common potential's charge inequality, the
finite-bias target-transport compiler constructs the simultaneous deviation
cap. -/
theorem hasEventualSimultaneousPlayerOwnedDeviationPayoffCap_of_burnIn
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          correction germ.endpointFinkPoint)
    (P : AnalyticOwnerScaledChargedOccupationPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who =>
        germ.rawPlayerOwnedOccupationCharge
          (seed.playerOwnedPoissonBias correction) who))
    (entry : G.State)
    (burnIn : MovingPlayerOwnedEndpointSuperharmonicBurnIn germ)
    (hcharge :
      ∀ who k index,
        germ.rawPlayerOwnedOccupationCharge
              (seed.playerOwnedPoissonBias correction) who
              (shiftedUniversalEpochScale burnIn.startEpoch k) index ≤
          transitionPotentialDrift
            (germ.finkOwnerActualOccupationKernelAt
              (burnIn.valid k) who)
            (ownerActualOccupationSource who)
            (germ.puncturedPlayerOwnedPotentialAt
              (seed.playerOwnedPoissonBias correction) who
              (CommonPlayerOwnedPotentialCalendar.ownerPotential
                germ (seed.playerOwnedPoissonBias correction) P who)
              (shiftedUniversalEpochScale burnIn.startEpoch k))
            index) :
    HasEventualSimultaneousPlayerOwnedDeviationPayoffCap
      seed correction P entry := by
  refine ⟨burnIn.startEpoch, burnIn.valid, hcharge, ?_⟩
  intro δ hδ
  exact
    seed.eventually_all_deviationPayoff_le_endpointValue_add_of_targetTransport
      correction hPoisson P entry burnIn.startEpoch burnIn.valid hcharge
      (burnIn.targetTransportAccount entry) hδ

/-- A moving-superharmonic burn-in can be shifted far enough that the same
calendar also satisfies the common potential's charge inequality. -/
theorem
    hasEventualSimultaneousPlayerOwnedDeviationPayoffCap_of_superharmonic
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          correction germ.endpointFinkPoint)
    (P : AnalyticOwnerScaledChargedOccupationPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who =>
        germ.rawPlayerOwnedOccupationCharge
          (seed.playerOwnedPoissonBias correction) who))
    (entry : G.State)
    (burnIn : MovingPlayerOwnedEndpointSuperharmonicBurnIn germ) :
    HasEventualSimultaneousPlayerOwnedDeviationPayoffCap
      seed correction P entry := by
  have hscale :
      Tendsto universalEpochScale atTop
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact
      ⟨tendsto_universalEpochScale,
        Filter.Eventually.of_forall universalEpochScale_pos⟩
  have hchargeEventually :
      ∀ᶠ k : ℕ in atTop,
        ∀ hk :
            universalEpochScale k ∈ Ioo (0 : ℝ) germ.radius,
          ∀ who index,
            germ.rawPlayerOwnedOccupationCharge
                  (seed.playerOwnedPoissonBias correction) who
                  (universalEpochScale k) index ≤
              transitionPotentialDrift
                (germ.finkOwnerActualOccupationKernelAt hk who)
                (ownerActualOccupationSource who)
                (germ.puncturedPlayerOwnedPotentialAt
                  (seed.playerOwnedPoissonBias correction) who
                  (CommonPlayerOwnedPotentialCalendar.ownerPotential
                    germ (seed.playerOwnedPoissonBias correction) P who)
                  (universalEpochScale k))
                index :=
    hscale.eventually
      (CommonPlayerOwnedPotentialCalendar.eventually_allPlayerOwnedCharge_le_drift
          germ (seed.playerOwnedPoissonBias correction) P)
  obtain ⟨chargeStart, hchargeStart⟩ :=
    eventually_atTop.1 hchargeEventually
  let shiftedBurnIn :
      MovingPlayerOwnedEndpointSuperharmonicBurnIn germ := {
    startEpoch := burnIn.startEpoch + chargeStart
    valid := fun k => by
      simpa only [shiftedUniversalEpochScale, Nat.add_assoc] using
        burnIn.valid (chargeStart + k)
    superharmonic := by
      intro who k source action
      have hsuper :=
        burnIn.superharmonic who (chargeStart + k) source action
      simpa only [shiftedUniversalEpochScale, Nat.add_assoc] using hsuper }
  have hcharge :
      ∀ who k index,
        germ.rawPlayerOwnedOccupationCharge
              (seed.playerOwnedPoissonBias correction) who
              (shiftedUniversalEpochScale shiftedBurnIn.startEpoch k)
              index ≤
          transitionPotentialDrift
            (germ.finkOwnerActualOccupationKernelAt
              (shiftedBurnIn.valid k) who)
            (ownerActualOccupationSource who)
            (germ.puncturedPlayerOwnedPotentialAt
              (seed.playerOwnedPoissonBias correction) who
              (CommonPlayerOwnedPotentialCalendar.ownerPotential
                germ (seed.playerOwnedPoissonBias correction) P who)
              (shiftedUniversalEpochScale shiftedBurnIn.startEpoch k))
            index := by
    intro who k index
    have h :=
      hchargeStart
        (shiftedBurnIn.startEpoch + k)
        (by
          dsimp only [shiftedBurnIn]
          omega)
        (shiftedBurnIn.valid k) who index
    simpa only [shiftedUniversalEpochScale] using h
  exact
    seed.hasEventualSimultaneousPlayerOwnedDeviationPayoffCap_of_burnIn
      correction hPoisson P entry shiftedBurnIn hcharge

/-- Direct finite-bias endpoint-drift payoff alternative.

The first branch is already the semantic, all-player, arbitrary-behavior
deviation cap at the selected entry target.  The other branches retain one
fixed actual action and either its centered transition monitor or the exact
prescribed-indistinguishability obstruction. -/
theorem
    hasDeviationPayoffCap_or_endpointDriftResponse_or_invisible
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          correction germ.endpointFinkPoint)
    (P : AnalyticOwnerScaledChargedOccupationPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who =>
        germ.rawPlayerOwnedOccupationCharge
          (seed.playerOwnedPoissonBias correction) who))
    (entry : G.State) :
    HasEventualSimultaneousPlayerOwnedDeviationPayoffCap
        seed correction P entry ∨
      Nonempty (AnalyticPlayerOwnedEndpointDriftTransitionResponse germ) ∨
        Nonempty
          (AnalyticInvisiblePositivePlayerOwnedEndpointDrift germ) := by
  rcases
      germ.exists_movingSuperharmonicBurnIn_or_endpointDriftResponse_or_invisible
      with hsuper | hresponse | hinvisible
  · left
    obtain ⟨burnIn⟩ := hsuper
    exact
      seed.hasEventualSimultaneousPlayerOwnedDeviationPayoffCap_of_superharmonic
        correction hPoisson P entry burnIn
  · exact Or.inr (Or.inl hresponse)
  · exact Or.inr (Or.inr hinvisible)

end FiniteBiasSeed
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
