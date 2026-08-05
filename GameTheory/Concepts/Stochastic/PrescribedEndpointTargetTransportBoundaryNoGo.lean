/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FiniteBiasPrescribedCalendarPayoffBoundary
import GameTheory.Concepts.Stochastic.PrescribedEndpointTargetTransportNoGo

/-!
# Failure of the prescribed endpoint-transport boundary

The explicit leaking analytic Bellman germ is connected here to the generic
prescribed-calendar boundary.  The generic unshifted calendar is exactly the
explicit prescribed profile, and its cumulative endpoint transport is the
sum of the scalar high-state probabilities.

Those probabilities converge to one.  Their normalized cumulative sum
therefore converges to one rather than zero, so the exact named two-sided
transport boundary fails.  This is a boundary no-go, not a counterexample to
uniform-equilibrium existence.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace PrescribedEndpointTargetTransportBoundaryNoGo

open Filter Math Math.OnlineLearning Math.Probability Set
open AnalyticBellmanGerm
open AnalyticBellmanGerm.FiniteBiasSeed
open PrescribedEndpointTargetTransportNoGo

/-- Every parameter of the unshifted generic calendar lies in the explicit
germ's validity interval. -/
theorem unshiftedValid (epoch : ℕ) :
    shiftedUniversalEpochScale 0 epoch ∈
      Ioo (0 : ℝ)
        PrescribedEndpointTargetTransportNoGo.germ.radius := by
  change shiftedUniversalEpochScale 0 epoch ∈ Ioo (0 : ℝ) 1
  have h :=
    PlayerOwnedEndpointTargetTransportNoGo.calendarValid epoch
  change shiftedUniversalEpochScale 0 epoch ∈ Ioo (0 : ℝ) 1 at h
  exact h

/-- The generic prescribed unshifted calendar is exactly the explicit
leaking profile. -/
theorem prescribedPlayerOwnedFinkCalendarProfile_eq :
    prescribedPlayerOwnedFinkCalendarProfile
        PrescribedEndpointTargetTransportNoGo.germ 0 unshiftedValid =
      PrescribedEndpointTargetTransportNoGo.prescribedProfile := by
  funext player stage history
  unfold prescribedPlayerOwnedFinkCalendarProfile
    PrescribedEndpointTargetTransportNoGo.prescribedProfile
    AnalyticBellmanGerm.LowerValueJet.calendarFinkBehaviorProfile
    StochasticGame.scheduledMarkovBehaviorProfile
  have residualValid :
      AnalyticBellmanGerm.LowerValueJet.residualCalendarScale stage ∈
        Ioo (0 : ℝ)
          PrescribedEndpointTargetTransportNoGo.germ.radius := by
    simpa only [
      AnalyticBellmanGerm.LowerValueJet.residualCalendarScale,
      playerOwnedCalendarScale, calendarScale,
      shiftedUniversalEpochScale, Nat.zero_add] using
        unshiftedValid (anytimeEpochIndex stage)
  change
    (PrescribedEndpointTargetTransportNoGo.game.finkProfile
      (PrescribedEndpointTargetTransportNoGo.germ.finkPointAt
        (unshiftedValid (anytimeEpochIndex stage)))
      history.2) player =
      (AnalyticBellmanGerm.LowerValueJet.calendarFinkMixedProfile
        PrescribedEndpointTargetTransportNoGo.germ
        stage history.2) player
  rw [
    AnalyticBellmanGerm.LowerValueJet.calendarFinkMixedProfile_eq_finkPointAt
      PrescribedEndpointTargetTransportNoGo.germ
      stage residualValid history.2]
  rw [
    PrescribedEndpointTargetTransportNoGo.finkProfile_finkPointAt,
    PrescribedEndpointTargetTransportNoGo.finkProfile_finkPointAt]
  simp only [
    AnalyticBellmanGerm.LowerValueJet.residualCalendarScale,
    shiftedUniversalEpochScale, Nat.zero_add]

/-- The generic prescribed endpoint transport is exactly the cumulative
scalar probability of having reached the high state. -/
theorem expectedPrescribedCalendarEndpointTargetTransport_eq
    (T : ℕ) :
    expectedPrescribedCalendarEndpointTargetTransport
        PrescribedEndpointTargetTransportNoGo.germ
        false false 0 unshiftedValid T =
      ∑ stage ∈ Finset.range T,
        PrescribedEndpointTargetTransportNoGo.scalarEndpointTarget
          stage := by
  unfold expectedPrescribedCalendarEndpointTargetTransport
  rw [prescribedPlayerOwnedFinkCalendarProfile_eq]
  apply Finset.sum_congr rfl
  intro stage _
  unfold expectedHistoryValue
  rw [expect_sub, expect_const]
  change
    PrescribedEndpointTargetTransportNoGo.game.expectedHistoryValue
          PrescribedEndpointTargetTransportNoGo.prescribedProfile false
          (fun _ history =>
            PrescribedEndpointTargetTransportNoGo.germ.endpointValue
              history.2 false)
          stage -
        PrescribedEndpointTargetTransportNoGo.germ.endpointValue
          false false =
      PrescribedEndpointTargetTransportNoGo.scalarEndpointTarget stage
  rw [expected_endpointValue_prescribedProfile,
    endpointTarget_at_entry_eq_zero]
  ring

/-- The normalized absolute generic endpoint transport converges to one. -/
theorem
    tendsto_normalized_abs_expectedPrescribedCalendarEndpointTargetTransport_one :
    Tendsto
      (fun T : ℕ =>
        (T : ℝ)⁻¹ *
          |expectedPrescribedCalendarEndpointTargetTransport
            PrescribedEndpointTargetTransportNoGo.germ
            false false 0 unshiftedValid T|)
      atTop (nhds 1) := by
  have hcesaro :
      Tendsto
        (fun T : ℕ =>
          (T : ℝ)⁻¹ *
            ∑ stage ∈ Finset.range T,
              scalarEndpointTarget stage)
        atTop (nhds 1) :=
    tendsto_scalarEndpointTarget_one.cesaro
  have habs := hcesaro.abs
  have heq :
      (fun T : ℕ =>
        (T : ℝ)⁻¹ *
          |expectedPrescribedCalendarEndpointTargetTransport
            PrescribedEndpointTargetTransportNoGo.germ
            false false 0 unshiftedValid T|) =
        (fun T : ℕ =>
          |(T : ℝ)⁻¹ *
            ∑ stage ∈ Finset.range T,
              scalarEndpointTarget stage|) := by
    funext T
    rw [expectedPrescribedCalendarEndpointTargetTransport_eq,
      abs_mul]
    congr 1
    have hinv : 0 ≤ (T : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg T)
    exact (abs_of_nonneg hinv).symm
  rw [heq]
  simpa only [abs_one] using habs

/-- The explicit germ fails the exact named two-sided prescribed transport
boundary at its low entry state. -/
theorem not_hasSublinearPrescribedCalendarEndpointTargetTransport :
    ¬ HasSublinearPrescribedCalendarEndpointTargetTransport
        PrescribedEndpointTargetTransportNoGo.germ
        false 0 unshiftedValid := by
  intro boundary
  have hzero := isAsymptoticallySublinear_iff_tendsto.mp (boundary false)
  have hone :=
    tendsto_normalized_abs_expectedPrescribedCalendarEndpointTargetTransport_one
  have : (1 : ℝ) = 0 :=
    tendsto_nhds_unique hone hzero
  norm_num at this

end PrescribedEndpointTargetTransportBoundaryNoGo
end StochasticGame
end GameTheory
