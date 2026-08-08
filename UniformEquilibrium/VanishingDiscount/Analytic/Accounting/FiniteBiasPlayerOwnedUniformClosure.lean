/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.FiniteBiasPlayerOwnedTargetTransportBoundary
import UniformEquilibrium.VanishingDiscount.Analytic.Endpoint.FiniteBiasPrescribedCalendarPayoffBoundary

/-!
# Uniform closure of the finite-bias player-owned calendar

This file joins the two semantic halves of one explicit shifted Fink
calendar:

* two-sided realization of the prescribed endpoint payoff;
* upper payoff caps for every unilateral behavior deviation.

The join is direct: the prescribed profile updated by one player's behavior
strategy is definitionally the scheduled player-owned deviation profile.
The canonical corollary consumes the Poisson residual account, the common
player-owned potential, and moving-row superharmonicity.  Its only separate
on-path input is the named two-sided prescribed endpoint-transport boundary.
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

omit [DecidableEq G.State] in
/-- Updating prescribed calendar play by one behavior strategy is exactly
the player-owned scheduled deviation profile used by the deviation
accounts. -/
theorem update_prescribedPlayerOwnedFinkCalendarProfile
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who) :
    Function.update
        (prescribedPlayerOwnedFinkCalendarProfile
          germ startEpoch valid)
        who dev =
      scheduledPlayerOwnedFinkDeviationProfile
        germ who startEpoch valid dev := by
  rfl

omit [DecidableEq G.State] in
/-- Direct semantic closure for one fixed calendar.

The Poisson equation and two-sided prescribed transport give on-path payoff
realization.  The separate premise is precisely the eventual simultaneous
unilateral payoff cap under the same calendar. -/
theorem isUniformEquilibriumPayoff_of_prescribedTransport_of_deviationCaps
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (correction : G.State → Payoff ι)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          correction germ.endpointFinkPoint)
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (prescribedTransport :
      HasSublinearPrescribedCalendarEndpointTargetTransport
        germ entry startEpoch valid)
    (deviationCaps :
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ T : ℕ in atTop,
          ∀ (who : ι) (dev : G.BehaviorStrategy who),
            G.finiteAveragePayoff entry T
                (scheduledPlayerOwnedFinkDeviationProfile
                  germ who startEpoch valid dev)
                who ≤
              germ.endpointValue entry who + δ) :
    G.IsUniformEquilibriumPayoff
      entry (germ.endpointValue entry) := by
  apply G.isUniformEquilibriumPayoff_of_deviation_caps
  intro δ hδ
  let prescribed :=
    prescribedPlayerOwnedFinkCalendarProfile
      germ startEpoch valid
  have hon :
      ∀ᶠ T : ℕ in atTop,
        ∀ who,
          |G.finiteAveragePayoff entry T prescribed who -
              germ.endpointValue entry who| ≤
            δ := by
    simpa only [prescribed] using
      seed.eventually_all_abs_finiteAveragePayoff_prescribedCalendar_sub_endpointValue_le
        correction hPoisson entry startEpoch valid
        prescribedTransport hδ
  have hdev := deviationCaps δ hδ
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (hon.and hdev)
  refine ⟨prescribed, T₀, fun T hT => ?_⟩
  obtain ⟨honT, hdevT⟩ := hT₀ T hT
  constructor
  · exact honT
  · intro who dev
    rw [update_prescribedPlayerOwnedFinkCalendarProfile
      germ who startEpoch valid dev]
    exact hdevT who dev

/-- Canonical finite-bias/common-potential closure at one shared calendar.

Moving-row superharmonicity supplies the zero upper transport account for
all unilateral deviations.  The common potential pays their Bellman
charges, while the named two-sided prescribed transport boundary realizes
the on-path target. -/
theorem isUniformEquilibriumPayoff_of_playerOwnedCommonPotential
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
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (hsuper :
      IsMovingPlayerOwnedEndpointSuperharmonic
        germ startEpoch valid)
    (hcharge :
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
                P who)
              (shiftedUniversalEpochScale startEpoch k))
            index)
    (prescribedTransport :
      HasSublinearPrescribedCalendarEndpointTargetTransport
        germ entry startEpoch valid) :
    G.IsUniformEquilibriumPayoff
      entry (germ.endpointValue entry) := by
  apply
    seed.isUniformEquilibriumPayoff_of_prescribedTransport_of_deviationCaps
      correction hPoisson entry startEpoch valid prescribedTransport
  intro δ hδ
  exact
    seed.eventually_all_deviationPayoff_le_endpointValue_add_of_targetTransport
      correction hPoisson P entry startEpoch valid hcharge
      (targetTransportAccountOfMovingSuperharmonic hsuper entry)
      hδ

end FiniteBiasSeed
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
