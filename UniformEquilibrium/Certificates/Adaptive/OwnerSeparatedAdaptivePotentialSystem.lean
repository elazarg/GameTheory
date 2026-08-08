/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Adaptive.SystemEnforcementLedger

/-!
# Owner-separated adaptive potential systems

The adaptive verifier has asymmetric prescribed and deviation obligations.
Lower and upper play use every coordinate of one target vector.  A unilateral
deviation by `who`, however, uses only the `who` coordinate of the deviation
potential, charge, and target.

This file makes that asymmetry explicit.  One on-path adaptive system
supplies the lower and upper halves.  For every possible deviator, a second
adaptive system on the same behavior profile and entry supplies only that
owner's deviation half.  Its other target coordinates are unrestricted.
Only the selected owner's target coordinate must agree approximately with
the on-path target.

The systems combine into an ordinary `AdaptivePotentialSystemAt`, so no
change to the final verifier is required.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type} {G : StochasticGame ι}

/-- One common on-path adaptive system and owner-indexed deviation systems.

All systems have exactly the same behavior profile and entry.  A deviation
system's target may be arbitrary away from its owner's coordinate. -/
structure OwnerSeparatedAdaptivePotentialData
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (profile : G.BehaviorProfile) (initial : G.State)
    (target : Payoff ι) (onPathError : ℝ)
    (deviationTarget : ι → Payoff ι)
    (deviationError mismatchError : ℝ) where
  onPath :
    G.AdaptivePotentialSystemAt
      profile initial target onPathError
  deviation :
    ∀ who,
      G.AdaptivePotentialSystemAt
        profile initial (deviationTarget who) deviationError
  onPathError_nonneg : 0 ≤ onPathError
  deviationError_nonneg : 0 ≤ deviationError
  mismatchError_nonneg : 0 ≤ mismatchError
  owner_target_mismatch : ∀ who,
    |deviationTarget who who - target who| ≤ mismatchError

namespace OwnerSeparatedAdaptivePotentialData

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]
  {profile : G.BehaviorProfile} {initial : G.State}
  {target : Payoff ι} {onPathError : ℝ}
  {deviationTarget : ι → Payoff ι}
  {deviationError mismatchError : ℝ}

/-- The explicit total error used by the combined verifier witness. -/
def combinedError
    (_data :
      G.OwnerSeparatedAdaptivePotentialData
        profile initial target onPathError deviationTarget
        deviationError mismatchError) : ℝ :=
  max onPathError (deviationError + mismatchError)

theorem combinedError_nonneg
    (data :
      G.OwnerSeparatedAdaptivePotentialData
        profile initial target onPathError deviationTarget
        deviationError mismatchError) :
    0 ≤ data.combinedError := by
  unfold combinedError
  exact data.onPathError_nonneg.trans (le_max_left _ _)

/-- Maximum of the finitely many owner-specific deviation horizons. -/
def deviationHorizon
    (data :
      G.OwnerSeparatedAdaptivePotentialData
        profile initial target onPathError deviationTarget
        deviationError mismatchError) : ℕ :=
  Finset.univ.sup fun who => (data.deviation who).horizon

theorem deviation_horizon_le
    (data :
      G.OwnerSeparatedAdaptivePotentialData
        profile initial target onPathError deviationTarget
        deviationError mismatchError)
    (who : ι) :
    (data.deviation who).horizon ≤ data.deviationHorizon :=
  Finset.le_sup
    (s := Finset.univ)
    (f := fun owner => (data.deviation owner).horizon)
    (Finset.mem_univ who)

/-- Combine the on-path lower/upper halves and each owner's separately
certified deviation half into the ordinary verifier interface. -/
def toAdaptivePotentialSystemAt
    (data :
      G.OwnerSeparatedAdaptivePotentialData
        profile initial target onPathError deviationTarget
        deviationError mismatchError) :
    G.AdaptivePotentialSystemAt
      profile initial target data.combinedError := by
  refine {
    horizon := max data.onPath.horizon data.deviationHorizon
    lowerPotential := data.onPath.lowerPotential
    upperPotential := data.onPath.upperPotential
    deviationPotential := fun who =>
      (data.deviation who).deviationPotential who
    lowerCharge := data.onPath.lowerCharge
    upperCharge := data.onPath.upperCharge
    deviationCharge := fun who =>
      (data.deviation who).deviationCharge who
    horizon_ge_two :=
      data.onPath.horizon_ge_two.trans
        (Nat.le_max_left _ _)
    lower_initial := ?_
    upper_initial := ?_
    deviation_initial := ?_
    lower_submartingale := data.onPath.lower_submartingale
    lower_stage := data.onPath.lower_stage
    upper_supermartingale := data.onPath.upper_supermartingale
    upper_stage := data.onPath.upper_stage
    deviation_supermartingale := ?_
    deviation_stage := ?_
    lower_charge_cesaro := ?_
    upper_charge_cesaro := ?_
    deviation_charge_cesaro := ?_
  }
  · intro who
    exact (data.onPath.lower_initial who).trans
      (by
        unfold combinedError
        exact le_max_left _ _)
  · intro who
    exact (data.onPath.upper_initial who).trans
      (by
        unfold combinedError
        exact le_max_left _ _)
  · intro who
    calc
      |(data.deviation who).deviationPotential who 0
            (G.emptyHist initial) -
          target who| =
          |((data.deviation who).deviationPotential who 0
                (G.emptyHist initial) -
              deviationTarget who who) +
            (deviationTarget who who - target who)| := by
            congr 1
            ring
      _ ≤
          |(data.deviation who).deviationPotential who 0
                (G.emptyHist initial) -
              deviationTarget who who| +
            |deviationTarget who who - target who| :=
        abs_add_le _ _
      _ ≤ deviationError + mismatchError :=
        add_le_add
          ((data.deviation who).deviation_initial who)
          (data.owner_target_mismatch who)
      _ ≤ data.combinedError := by
        unfold combinedError
        exact le_max_right _ _
  · intro who deviation time
    exact (data.deviation who).deviation_supermartingale
      who deviation time
  · intro who deviation time
    exact (data.deviation who).deviation_stage
      who deviation time
  · intro who total htotal
    exact (data.onPath.lower_charge_cesaro who total
      ((Nat.le_max_left _ _).trans htotal)).trans
        (by
          unfold combinedError
          exact le_max_left _ _)
  · intro who total htotal
    exact (data.onPath.upper_charge_cesaro who total
      ((Nat.le_max_left _ _).trans htotal)).trans
        (by
          unfold combinedError
          exact le_max_left _ _)
  · intro who deviation total htotal
    exact ((data.deviation who).deviation_charge_cesaro
      who deviation total
      (data.deviation_horizon_le who |>.trans
        ((Nat.le_max_right _ _).trans htotal))).trans
      (by
        unfold combinedError
        exact
          (le_add_of_nonneg_right data.mismatchError_nonneg).trans
            (le_max_right _ _))

/-- Direct acceptance by the existing adaptive verifier. -/
theorem toIsAdaptivePotentialCertificateAt
    (data :
      G.OwnerSeparatedAdaptivePotentialData
        profile initial target onPathError deviationTarget
        deviationError mismatchError) :
    G.IsAdaptivePotentialCertificateAt initial target
      data.combinedError :=
  data.toAdaptivePotentialSystemAt.toIsAdaptivePotentialCertificateAt

end OwnerSeparatedAdaptivePotentialData

/-- Public-ledger presentation of the same owner separation.

The on-path ledger and every owner-specific deviation ledger use one common
public phase profile and entry. -/
structure OwnerSeparatedPublicResponseLedgerData
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)]
    (publicProfile : G.PublicPhaseProfile) (initial : G.State)
    (target : Payoff ι) (onPathError : ℝ)
    (deviationTarget : ι → Payoff ι)
    (deviationError mismatchError : ℝ) where
  onPath :
    G.PublicResponseEnforcementLedgerAt
      publicProfile initial target onPathError
  deviation :
    ∀ who,
      G.PublicResponseEnforcementLedgerAt
        publicProfile initial (deviationTarget who) deviationError
  deviationError_nonneg : 0 ≤ deviationError
  mismatchError_nonneg : 0 ≤ mismatchError
  owner_target_mismatch : ∀ who,
    |deviationTarget who who - target who| ≤ mismatchError

namespace OwnerSeparatedPublicResponseLedgerData

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]
  {publicProfile : G.PublicPhaseProfile} {initial : G.State}
  {target : Payoff ι} {onPathError : ℝ}
  {deviationTarget : ι → Payoff ι}
  {deviationError mismatchError : ℝ}

/-- Compile the public ledgers to the owner-separated adaptive data. -/
def toOwnerSeparatedAdaptivePotentialData
    (data :
      G.OwnerSeparatedPublicResponseLedgerData
        publicProfile initial target onPathError deviationTarget
        deviationError mismatchError) :
    G.OwnerSeparatedAdaptivePotentialData
      publicProfile.behaviorProfile initial target onPathError
      deviationTarget deviationError mismatchError where
  onPath :=
    data.onPath.toPublicPhasePunishmentSystemAt
      |>.toAdaptivePotentialSystemAt G
  deviation := fun who =>
    (data.deviation who).toPublicPhasePunishmentSystemAt
      |>.toAdaptivePotentialSystemAt G
  onPathError_nonneg := data.onPath.error_nonneg
  deviationError_nonneg := data.deviationError_nonneg
  mismatchError_nonneg := data.mismatchError_nonneg
  owner_target_mismatch := data.owner_target_mismatch

/-- Combine owner-separated public ledgers into one adaptive system.

The result uses no parent certificate and imposes no equality on an
owner-specific deviation target outside the owner's own coordinate. -/
def toAdaptivePotentialSystemAt
    (data :
      G.OwnerSeparatedPublicResponseLedgerData
        publicProfile initial target onPathError deviationTarget
        deviationError mismatchError) :
    G.AdaptivePotentialSystemAt
      publicProfile.behaviorProfile initial target
      data.toOwnerSeparatedAdaptivePotentialData.combinedError :=
  data.toOwnerSeparatedAdaptivePotentialData.toAdaptivePotentialSystemAt

/-- Canonical operational ledger extracted from the combined system. -/
def toPublicResponseEnforcementLedgerAt
    (data :
      G.OwnerSeparatedPublicResponseLedgerData
        publicProfile initial target onPathError deviationTarget
        deviationError mismatchError) :
    G.PublicResponseEnforcementLedgerAt
      (G.behaviorPublicPhaseProfile publicProfile.behaviorProfile)
      initial target
      (2 * data.toOwnerSeparatedAdaptivePotentialData.combinedError) :=
  data.toAdaptivePotentialSystemAt
    |>.toExactStageGapPublicResponseEnforcementLedgerAt
      data.toOwnerSeparatedAdaptivePotentialData.combinedError_nonneg

end OwnerSeparatedPublicResponseLedgerData

end StochasticGame
end GameTheory
