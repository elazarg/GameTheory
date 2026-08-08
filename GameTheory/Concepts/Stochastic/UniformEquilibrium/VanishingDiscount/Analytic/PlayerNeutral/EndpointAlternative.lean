/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.LeadingDriftAlternative
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.HarmonicJet

/-!
# Endpoint alternative for analytic player-neutral potential jets

The first nonzero gauge-fixed coefficient of an analytic player-neutral
potential has one of three finite endpoint outcomes:

* a fixed operational column has strictly positive drift, together with
  horizon-uniform adaptive use and mixed-mass budgets;
* the associated endpoint-harmonic payoff vector is already in the
  processed carrier; or
* adjoining that vector strictly lowers the remaining harmonic rank.

This is a typed assembly of the strict-drift and harmonic-jet results. It
does not construct a strategy, punishment, or public response.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

local instance endpointAlternativeIndexDecidableEq
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    DecidableEq (germ.PlayerNeutralOccupationIndex who) :=
  Classical.decEq _

/-- A strict leading-drift certificate equipped with both standard
horizon-uniform occupation budgets. -/
structure PlayerNeutralStrictLeadingDriftWithBudget
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor) where
  drift : germ.PlayerNeutralStrictLeadingDrift B who jet
  use_budget :
    ∀ (initial : G.State)
      (choice :
        ∀ n, (Fin (n + 1) → G.State) →
          germ.PlayerNeutralOccupationIndex who),
      (∀ n history,
        germ.playerNeutralOccupationSource who (choice n history) =
          history (Fin.last n)) →
      ∀ T,
        drift.margin *
            expect
              (adaptiveHistoryLaw
                (adaptiveMarkovStep initial
                  (selectedTransitionComparison
                    (germ.playerNeutralOccupationKernel who) choice))
                (T + 1))
              (selectedTransitionUseCount choice drift.index T) ≤
          1
  mass_budget :
    ∀ (initial : G.State)
      (selection :
        ∀ n, (Fin (n + 1) → G.State) →
          PMF (germ.PlayerNeutralOccupationIndex who)),
      (∀ n history index,
        selection n history index ≠ 0 →
          germ.playerNeutralOccupationSource who index =
            history (Fin.last n)) →
      ∀ T,
        drift.margin *
            expect
              (adaptiveHistoryLaw
                (adaptiveMarkovStep initial
                  (mixedTransitionComparison
                    (germ.playerNeutralOccupationKernel who) selection))
                (T + 1))
              (selectedTransitionMassSum selection drift.index T) ≤
          1

/-- Promote a strict leading-drift certificate to one carrying the two
generic adaptive occupation budgets. -/
def PlayerNeutralStrictLeadingDrift.withBudget
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}
    (drift : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    germ.PlayerNeutralStrictLeadingDriftWithBudget B who jet where
  drift := drift
  use_budget := by
    intro initial choice source_compatible T
    exact drift.selectedUseBudget initial choice source_compatible T
  mass_budget := by
    intro initial selection source_compatible T
    exact drift.selectedMassBudget initial selection source_compatible T

/-- The honest endpoint outcomes of a gauge-fixed analytic
player-neutral potential jet relative to a processed harmonic span. -/
inductive PlayerNeutralPotentialJetEndpointAlternative
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    (jet : GaugeFixedPotentialJet P anchor)
    (span : germ.EndpointHarmonicJetSpan) : Prop
  | strictDrift
      (certificate :
        Nonempty
          (germ.PlayerNeutralStrictLeadingDriftWithBudget B who jet))
  | processedHarmonic
      (membership :
        germ.playerNeutralPotentialJetLeadingPayoff who jet ∈
          span.carrier)
  | rankDecrease
      (harmonic :
        germ.playerNeutralPotentialJetLeadingPayoff who jet ∈
          germ.endpointHarmonicSubmodule)
      (decrease :
        (span.extend
          (germ.playerNeutralPotentialJetLeadingPayoff who jet)
          harmonic).rank < span.rank)

/-- A gauge-fixed analytic player-neutral potential jet yields a strict
drift with both occupation budgets, an already processed harmonic jet, or
a strict harmonic rank decrease. -/
theorem playerNeutralPotentialJet_endpointAlternative
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
    (span : germ.EndpointHarmonicJetSpan) :
    germ.PlayerNeutralPotentialJetEndpointAlternative
      B who jet span := by
  rcases
      germ.playerNeutralLeadingPairings_zero_or_strictDrift
        B who jet circulation with pairing_zero | strict
  · rcases
        germ.playerNeutralPotentialJetLeadingPayoff_processed_or_rankDecrease
          who jet span pairing_zero with processed | rank_decrease
    · exact .processedHarmonic processed
    · rcases rank_decrease with ⟨harmonic, decrease⟩
      exact .rankDecrease harmonic decrease
  · exact .strictDrift (strict.map
      PlayerNeutralStrictLeadingDrift.withBudget)

/-- Starting from the scaled analytic potential itself, extract a genuine
gauge-fixed leading jet and classify it by the endpoint alternative. -/
theorem exists_playerNeutralPotentialJet_endpointAlternative
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
    (anchor : G.State)
    (span : germ.EndpointHarmonicJetSpan) :
    ∃ jet : GaugeFixedPotentialJet P anchor,
      germ.PlayerNeutralPotentialJetEndpointAlternative
        B who jet span := by
  rcases germ.exists_playerNeutralGaugeFixedPotentialJet
      B who P circulation anchor with ⟨jet⟩
  exact ⟨jet,
    germ.playerNeutralPotentialJet_endpointAlternative
      B who jet circulation span⟩

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
