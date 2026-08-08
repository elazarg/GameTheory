/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Adaptive.PotentialSystem

/-!
# Target perturbations for adaptive potential certificates

An adaptive potential system is stable under a uniform perturbation of its
target payoff.  The potentials, profile, and charges are unchanged.  Only
the three initial-value estimates use the target, so the perturbation is
paid once through the triangle inequality.

This turns approximate target transport into an ordinary error-budget term
rather than a separate strategic obstruction.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}
  [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ who, Finite (G.Act who)]

namespace AdaptivePotentialSystemAt

variable {profile : G.BehaviorProfile} {initial : G.State}
  {target perturbedTarget : Payoff ι}
  {error targetError : ℝ}

private theorem initial_close_add
    {value leftTarget rightTarget : ℝ}
    (hvalue : |value - leftTarget| ≤ error)
    (htarget : |leftTarget - rightTarget| ≤ targetError) :
    |value - rightTarget| ≤ error + targetError := by
  have htriangle :=
    abs_sub_le value leftTarget rightTarget
  linarith

/-- Retarget an adaptive system to a uniformly nearby payoff vector.

The strategic profile, potentials, and scalar charges are identical.  The
target perturbation is added only to the advertised error. -/
def retarget
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (targetError_nonneg : 0 ≤ targetError)
    (target_close :
      ∀ who, |target who - perturbedTarget who| ≤ targetError) :
    G.AdaptivePotentialSystemAt profile initial perturbedTarget
      (error + targetError) where
  horizon := system.horizon
  lowerPotential := system.lowerPotential
  upperPotential := system.upperPotential
  deviationPotential := system.deviationPotential
  lowerCharge := system.lowerCharge
  upperCharge := system.upperCharge
  deviationCharge := system.deviationCharge
  horizon_ge_two := system.horizon_ge_two
  lower_initial := fun who =>
    initial_close_add
      (system.lower_initial who) (target_close who)
  upper_initial := fun who =>
    initial_close_add
      (system.upper_initial who) (target_close who)
  deviation_initial := fun who =>
    initial_close_add
      (system.deviation_initial who) (target_close who)
  lower_submartingale := system.lower_submartingale
  lower_stage := system.lower_stage
  upper_supermartingale := system.upper_supermartingale
  upper_stage := system.upper_stage
  deviation_supermartingale := system.deviation_supermartingale
  deviation_stage := system.deviation_stage
  lower_charge_cesaro := by
    intro who total htotal
    exact (system.lower_charge_cesaro who total htotal).trans
      (le_add_of_nonneg_right targetError_nonneg)
  upper_charge_cesaro := by
    intro who total htotal
    exact (system.upper_charge_cesaro who total htotal).trans
      (le_add_of_nonneg_right targetError_nonneg)
  deviation_charge_cesaro := by
    intro who deviation total htotal
    exact
      (system.deviation_charge_cesaro
        who deviation total htotal).trans
        (le_add_of_nonneg_right targetError_nonneg)

end AdaptivePotentialSystemAt

/-- Retarget an existential adaptive certificate to a uniformly nearby
payoff vector. -/
theorem IsAdaptivePotentialCertificateAt.retarget
    {initial : G.State} {target perturbedTarget : Payoff ι}
    {error targetError : ℝ}
    (certificate :
      G.IsAdaptivePotentialCertificateAt initial target error)
    (targetError_nonneg : 0 ≤ targetError)
    (target_close :
      ∀ who, |target who - perturbedTarget who| ≤ targetError) :
    G.IsAdaptivePotentialCertificateAt initial perturbedTarget
      (error + targetError) := by
  rw [G.isAdaptivePotentialCertificateAt_iff_exists_system]
  rw [G.isAdaptivePotentialCertificateAt_iff_exists_system] at certificate
  obtain ⟨profile, ⟨system⟩⟩ := certificate
  exact
    ⟨profile,
      ⟨system.retarget targetError_nonneg target_close⟩⟩

end StochasticGame
end GameTheory
