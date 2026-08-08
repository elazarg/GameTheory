/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerOwned.OccupationAlternative
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticHarmonicAdjustmentClosure
import Math.Probability.AnalyticChargedCirculationLeadingMass

/-!
# Endpoint neutrality of a player-owned circulation's leading mass

The full player-owned charged-flow alternative may return an analytic
circulation which uses endpoint-strict actions at positive parameters.  Its
first nonzero mass coefficient is nevertheless supported only on prescribed
baseline rows and endpoint continuation-neutral actions.

The reason is order-free.  The leading mass is a nonnegative endpoint
circulation.  Pairing its balance with the owner's excessive endpoint value
gives a sum of nonpositive continuation gains equal to zero.  Every action
with positive leading mass must therefore have zero endpoint gain.

This theorem reconnects the widened full-owner alternative to the existing
player-neutral endpoint hierarchy.  It does not assert that the leading
circulation already has positive charge; that depends on whether its order
equals the analytic circulation's clearing order.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.Probability Set
open Math.Probability.AnalyticPositiveChargedCirculation

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Endpoint drift of the owner's endpoint continuation value along one
full player-owned occupation column. -/
def playerOwnedEndpointValueDrift
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (index : OwnerOccupationIndex G who) : ℝ :=
  ∑ destination,
    germ.endpointValue destination who *
      germ.rawOwnerAnalyticOccupationColumn who 0 index destination

/-- A baseline row has zero endpoint-value drift, while a pure-action row
has exactly its endpoint continuation gain. -/
theorem playerOwnedEndpointValueDrift_eq
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (index : OwnerOccupationIndex G who) :
    germ.playerOwnedEndpointValueDrift who index =
      match index with
      | .inl _ => 0
      | .inr response =>
          G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint response.1 who response.2 := by
  have baseline_drift (source : G.State) :
      (∑ destination,
          germ.endpointValue destination who *
            (germ.rawStateKernelCurve 0 source destination -
              if destination = source then 1 else 0)) = 0 := by
    have harmonic :=
      congrFun
        (congrFun
          germ.finkContinuationResidualVector_endpointValue_eq_zero
          source) who
    simp only [Pi.zero_apply] at harmonic
    have kernel :
        (∑ destination,
            germ.endpointValue destination who *
              germ.rawStateKernelCurve 0 source destination) =
          expect
            (G.finkStateKernel germ.endpointFinkPoint source)
            (fun destination =>
              germ.endpointValue destination who) := by
      rw [expect_eq_sum]
      apply Finset.sum_congr rfl
      intro destination _
      rw [germ.rawStateKernelCurve_zero_eq_finkStateKernel]
      ring
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, kernel]
    have source_term :
        (∑ destination,
            germ.endpointValue destination who *
              (if destination = source then 1 else 0)) =
          germ.endpointValue source who := by
      simp
    rw [source_term, G.expect_finkStateKernel_eq]
    simpa [finkContinuationResidualVector,
      finkContinuationResidual, finkContinuationEU] using harmonic
  cases index with
  | inl source =>
      simpa [playerOwnedEndpointValueDrift,
        rawOwnerAnalyticOccupationColumn,
        ownerOccupationIndexEmbedding,
        rawAnalyticOccupationColumn] using baseline_drift source
  | inr response =>
      have gain :=
        germ.rawPureDeviationContinuationGainCurve_zero_eq_endpointFinkPoint
          germ.endpointValue response.1 who response.2
      change
        germ.playerOwnedEndpointValueDrift who (.inr response) =
          G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint response.1 who response.2
      rw [← gain]
      unfold playerOwnedEndpointValueDrift
        rawOwnerAnalyticOccupationColumn
        ownerOccupationIndexEmbedding rawAnalyticOccupationColumn
        rawPureDeviationContinuationGainCurve
      calc
        (∑ destination,
            germ.endpointValue destination who *
              (germ.rawPureDeviationStateKernelCurve
                  0 response.1 who response.2 destination -
                if destination = response.1 then 1 else 0)) =
            (∑ destination,
              (germ.rawPureDeviationStateKernelCurve
                    0 response.1 who response.2 destination -
                  germ.rawStateKernelCurve
                    0 response.1 destination) *
                germ.endpointValue destination who) +
              (∑ destination,
                germ.endpointValue destination who *
                  (germ.rawStateKernelCurve
                      0 response.1 destination -
                    if destination = response.1 then 1 else 0)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro destination _
          ring
        _ =
            ∑ destination,
              (germ.rawPureDeviationStateKernelCurve
                    0 response.1 who response.2 destination -
                  germ.rawStateKernelCurve
                    0 response.1 destination) *
                germ.endpointValue destination who := by
          rw [baseline_drift response.1, add_zero]

theorem playerOwnedEndpointValueDrift_nonpos
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (index : OwnerOccupationIndex G who) :
    germ.playerOwnedEndpointValueDrift who index ≤ 0 := by
  rw [germ.playerOwnedEndpointValueDrift_eq who index]
  cases index with
  | inl source => exact le_rfl
  | inr response =>
      exact germ.finkContinuationGain_endpointValue_nonpos
        response.1 who response.2

/-- Every pure action carrying positive leading mass is continuation-neutral
at the analytic endpoint. -/
theorem
    AnalyticPositiveChargedCirculation.LeadingMassJet.action_neutral_of_pos
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (jet : C.LeadingMassJet)
    (source : G.State) (action : G.Act who)
    (positive : 0 < jet.factor 0 (.inr (source, action))) :
    G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0 := by
  have weighted_balance :
      ∑ index,
          jet.factor 0 index *
            germ.playerOwnedEndpointValueDrift who index = 0 := by
    calc
      (∑ index,
          jet.factor 0 index *
            germ.playerOwnedEndpointValueDrift who index) =
          ∑ destination,
            germ.endpointValue destination who *
              (∑ index,
                jet.factor 0 index *
                  germ.rawOwnerAnalyticOccupationColumn
                    who 0 index destination) := by
        unfold playerOwnedEndpointValueDrift
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro destination _
        apply Finset.sum_congr rfl
        intro index _
        ring
      _ = 0 := by
        simp only [jet.endpoint_balance, mul_zero,
          Finset.sum_const_zero]
  have term_nonpositive :
      ∀ index,
        jet.factor 0 index *
            germ.playerOwnedEndpointValueDrift who index ≤ 0 := by
    intro index
    exact mul_nonpos_of_nonneg_of_nonpos
      (jet.leading_nonnegative index)
      (germ.playerOwnedEndpointValueDrift_nonpos who index)
  have every_term_zero :=
    (Fintype.sum_eq_zero_iff_of_nonpos term_nonpositive).mp
      weighted_balance
  have selected_zero :=
    congrFun every_term_zero (.inr (source, action))
  rw [germ.playerOwnedEndpointValueDrift_eq
    who (.inr (source, action))] at selected_zero
  exact
    (mul_eq_zero.mp selected_zero).resolve_left
      (ne_of_gt positive)

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
