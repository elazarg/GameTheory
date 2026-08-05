/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticPlayerNeutralOccupationAlternative
import Math.Probability.AnalyticChargedPotentialEndpoint

/-!
# Endpoint jets of analytic player-neutral potentials

The moving player-neutral occupation columns have zero coordinate sum.
Consequently, a scaled analytic charged-occupation potential can be gauge
fixed without changing its column pairings.

Given an endpoint normalized positive circulation and an anchor state, the
generic endpoint extractor supplies a genuine first nonzero gauge-fixed
coefficient. Its order is below the pole-clearing order, its endpoint
pairing is nonnegative on every player-neutral column, and it is
complementary to every positive-mass column of the supplied circulation.

The circulation remains an explicit hypothesis. This file does not infer
one from the scaled-potential branch.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Math.Probability Set
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- Every moving player-neutral actual occupation column has coordinate sum
zero on a sufficiently small positive punctured neighborhood. -/
theorem eventually_sum_rawPlayerNeutralOccupationColumn_eq_zero
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ index,
        ∑ destination,
          germ.rawPlayerNeutralOccupationColumn
            who t index destination = 0 := by
  filter_upwards [
    germ.eventually_sum_rawAnalyticOccupationColumn_eq_zero
  ] with t ht
  intro index
  exact ht (playerNeutralOccupationIndexEmbedding who index)

/-- A scaled player-neutral potential, an endpoint normalized positive
circulation, and an anchor determine a genuine first nonzero gauge-fixed
analytic coefficient. -/
theorem exists_playerNeutralGaugeFixedPotentialJet
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (anchor : G.State) :
    Nonempty (GaugeFixedPotentialJet P anchor) := by
  have endpointCirculation :
      HasNormalizedPositiveChargedCirculation
        (germ.rawPlayerNeutralOccupationColumn who 0)
        (germ.rawPlayerNeutralOccupationCharge B who 0) := by
    simpa only [
      germ.rawPlayerNeutralOccupationColumn_zero who,
      germ.rawPlayerNeutralOccupationCharge_zero B who
    ] using circulation
  exact P.exists_gaugeFixedPotentialJet
    anchor
    (germ.analytic_rawPlayerNeutralOccupationCharge B who)
    (germ.eventually_sum_rawPlayerNeutralOccupationColumn_eq_zero who)
    endpointCirculation

/-- The first nonzero gauge-fixed player-neutral potential coefficient
occurs strictly below the scaled potential's pole-clearing order. -/
theorem playerNeutralGaugeFixedPotentialJet_order_lt_poleOrder
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who)) :
    jet.order < P.poleOrder := by
  have endpointCirculation :
      HasNormalizedPositiveChargedCirculation
        (germ.rawPlayerNeutralOccupationColumn who 0)
        (germ.rawPlayerNeutralOccupationCharge B who 0) := by
    simpa only [
      germ.rawPlayerNeutralOccupationColumn_zero who,
      germ.rawPlayerNeutralOccupationCharge_zero B who
    ] using circulation
  exact jet.order_lt_poleOrder
    (germ.analytic_rawPlayerNeutralOccupationColumn who)
    (germ.analytic_rawPlayerNeutralOccupationCharge B who)
    (germ.eventually_sum_rawPlayerNeutralOccupationColumn_eq_zero who)
    endpointCirculation

/-- The leading gauge-fixed coefficient pairs nonnegatively with every
static endpoint player-neutral actual occupation column. -/
theorem playerNeutralGaugeFixedPotentialJet_pair_nonneg
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (index : germ.PlayerNeutralOccupationIndex who) :
    0 ≤
      ∑ state,
        jet.factor 0 state *
          actualOccupationColumn
            (germ.playerNeutralOccupationKernel who)
            (germ.playerNeutralOccupationSource who)
            index state := by
  have endpointCirculation :
      HasNormalizedPositiveChargedCirculation
        (germ.rawPlayerNeutralOccupationColumn who 0)
        (germ.rawPlayerNeutralOccupationCharge B who 0) := by
    simpa only [
      germ.rawPlayerNeutralOccupationColumn_zero who,
      germ.rawPlayerNeutralOccupationCharge_zero B who
    ] using circulation
  have hPair := jet.leading_pair_nonneg
    (germ.analytic_rawPlayerNeutralOccupationColumn who)
    (germ.analytic_rawPlayerNeutralOccupationCharge B who)
    (germ.eventually_sum_rawPlayerNeutralOccupationColumn_eq_zero who)
    endpointCirculation index
  simpa only [
    germ.rawPlayerNeutralOccupationColumn_zero who
  ] using hPair

/-- The supplied endpoint circulation has a mass representation
complementary to the leading gauge-fixed coefficient on every column with
positive mass. -/
theorem
    exists_playerNeutralGaugeFixedPotentialJet_complementaryMass
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who)) :
    ∃ mass : germ.PlayerNeutralOccupationIndex who → ℝ,
      (∀ index, 0 ≤ mass index) ∧
      (∀ state,
        ∑ index,
          mass index *
            actualOccupationColumn
              (germ.playerNeutralOccupationKernel who)
              (germ.playerNeutralOccupationSource who)
              index state = 0) ∧
      (∑ index,
        mass index *
          germ.playerNeutralOccupationCharge B who index = 1) ∧
      ∀ index, 0 < mass index →
        (∑ state,
          jet.factor 0 state *
            actualOccupationColumn
              (germ.playerNeutralOccupationKernel who)
              (germ.playerNeutralOccupationSource who)
              index state) = 0 := by
  have endpointCirculation :
      HasNormalizedPositiveChargedCirculation
        (germ.rawPlayerNeutralOccupationColumn who 0)
        (germ.rawPlayerNeutralOccupationCharge B who 0) := by
    simpa only [
      germ.rawPlayerNeutralOccupationColumn_zero who,
      germ.rawPlayerNeutralOccupationCharge_zero B who
    ] using circulation
  simpa only [
    germ.rawPlayerNeutralOccupationColumn_zero who,
    germ.rawPlayerNeutralOccupationCharge_zero B who
  ] using
    (jet.exists_leading_complementary_mass
      (germ.analytic_rawPlayerNeutralOccupationColumn who)
      (germ.analytic_rawPlayerNeutralOccupationCharge B who)
      (germ.eventually_sum_rawPlayerNeutralOccupationColumn_eq_zero who)
      endpointCirculation)

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
