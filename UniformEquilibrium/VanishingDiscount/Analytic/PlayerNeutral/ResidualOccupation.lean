/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.ZeroDriftRestriction
import Math.Probability.AnalyticChargedPotentialEndpoint

/-!
# Analytic iteration on the residual player-neutral occupation family

A strict leading potential deletes every operational column with positive
endpoint drift.  The remaining columns form a strictly smaller finite type.
This file restricts the original analytic column and charge germs to that
type and runs the charged occupation-flow alternative again.

The endpoint circulation survives the restriction by complementarity.
Consequently, the next analytic alternative is either a charged analytic
circulation on the residual family or another genuine gauge-fixed potential
jet on that strictly smaller family.

There is an important boundary to this iteration.  A strict set may contain
a prescribed baseline column.  In that case the residual family no longer
tests the next potential against that row of the prescribed kernel, so the
new jet alone does not imply harmonicity for the original baseline chain.
Such a conclusion requires a separate proof that all relevant baseline
columns survive, or a different invariant accounting for the deleted rows.

This is only a finite analytic descent step.  It does not construct a
strategy, a public response, or a legally reachable recurrent child.
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
namespace PlayerNeutralStrictLeadingDrift

variable
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}

/-- The moving occupation column inherited by a residual zero-drift index. -/
def zeroDriftRawOccupationColumn
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    ℝ → C.ZeroDriftIndex → G.State → ℝ :=
  fun t index destination =>
    germ.rawPlayerNeutralOccupationColumn who t index.1 destination

/-- The moving charge inherited by a residual zero-drift index. -/
def zeroDriftRawOccupationCharge
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    ℝ → C.ZeroDriftIndex → ℝ :=
  fun t index =>
    germ.rawPlayerNeutralOccupationCharge B who t index.1

/-- Every coordinate of the restricted moving column family is analytic at
the endpoint. -/
theorem analytic_zeroDriftRawOccupationColumn
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    ∀ index destination,
      AnalyticAt ℝ
        (fun t =>
          C.zeroDriftRawOccupationColumn t index destination) 0 := by
  intro index destination
  exact germ.analytic_rawPlayerNeutralOccupationColumn
    who index.1 destination

/-- Every coordinate of the restricted moving charge family is analytic at
the endpoint. -/
theorem analytic_zeroDriftRawOccupationCharge
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    ∀ index,
      AnalyticAt ℝ
        (fun t => C.zeroDriftRawOccupationCharge t index) 0 := by
  intro index
  exact germ.analytic_rawPlayerNeutralOccupationCharge
    B who index.1

/-- Restriction preserves the punctured zero-sum identity of every actual
occupation column. -/
theorem eventually_sum_zeroDriftRawOccupationColumn_eq_zero
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ index,
        ∑ destination,
          C.zeroDriftRawOccupationColumn t index destination = 0 := by
  filter_upwards [
    germ.eventually_sum_rawPlayerNeutralOccupationColumn_eq_zero who
  ] with t ht
  intro index
  exact ht index.1

/-- At the endpoint, the restricted moving columns are the static residual
actual-occupation columns. -/
theorem zeroDriftRawOccupationColumn_zero
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    C.zeroDriftRawOccupationColumn 0 =
      actualOccupationColumn C.zeroDriftKernel C.zeroDriftSource := by
  funext index destination
  change
    germ.rawPlayerNeutralOccupationColumn who 0 index.1 destination =
      actualOccupationColumn
        (germ.playerNeutralOccupationKernel who)
        (germ.playerNeutralOccupationSource who)
        index.1 destination
  rw [germ.rawPlayerNeutralOccupationColumn_zero who]

/-- At the endpoint, the restricted moving charges are the static residual
charges. -/
theorem zeroDriftRawOccupationCharge_zero
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet) :
    C.zeroDriftRawOccupationCharge 0 = C.zeroDriftCharge := by
  funext index
  change
    germ.rawPlayerNeutralOccupationCharge B who 0 index.1 =
      germ.playerNeutralOccupationCharge B who index.1
  rw [germ.rawPlayerNeutralOccupationCharge_zero B who]

/-- Complementarity supplies the endpoint circulation required to iterate
the analytic alternative on the residual family. -/
theorem zeroDrift_endpointNormalizedPositiveChargedCirculation
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who)) :
    HasNormalizedPositiveChargedCirculation
      (C.zeroDriftRawOccupationColumn 0)
      (C.zeroDriftRawOccupationCharge 0) := by
  rw [C.zeroDriftRawOccupationColumn_zero,
    C.zeroDriftRawOccupationCharge_zero]
  exact C.exists_zeroDrift_normalizedPositiveChargedCirculation
    circulation

/-- A scaled potential together with its first nonzero gauge-fixed analytic
coefficient on the residual index family. -/
structure ZeroDriftAnalyticPotentialJet
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (nextAnchor : G.State) where
  scaledPotential :
    AnalyticScaledChargedOccupationPotential
      C.zeroDriftRawOccupationColumn
      C.zeroDriftRawOccupationCharge
  gaugeFixedJet :
    GaugeFixedPotentialJet scaledPotential nextAnchor

/-- The next honest analytic iteration on the residual family.

The alternatives remain exclusive because a gauge-fixed jet packages an
underlying scaled charged-occupation potential, which is incompatible with
an analytic positive charged circulation on the same punctured germ. -/
theorem
    zeroDrift_analyticPositiveChargedCirculation_xor_nextPotentialJet
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (nextAnchor : G.State) :
    Xor
      (Nonempty
        (AnalyticPositiveChargedCirculation
          C.zeroDriftRawOccupationColumn
          C.zeroDriftRawOccupationCharge))
      (Nonempty (C.ZeroDriftAnalyticPotentialJet nextAnchor)) := by
  rcases
      analyticPositiveChargedCirculation_xor_scaledPotential
        C.zeroDriftRawOccupationColumn
        C.zeroDriftRawOccupationCharge
        C.analytic_zeroDriftRawOccupationColumn
        C.analytic_zeroDriftRawOccupationCharge with
    analyticCirculation | scaledPotential
  · refine Or.inl ⟨analyticCirculation.1, ?_⟩
    rintro ⟨next⟩
    exact analyticCirculation.2 ⟨next.scaledPotential⟩
  · obtain ⟨nextPotential⟩ := scaledPotential.1
    obtain ⟨nextJet⟩ :=
      nextPotential.exists_gaugeFixedPotentialJet
        nextAnchor
        C.analytic_zeroDriftRawOccupationCharge
        C.eventually_sum_zeroDriftRawOccupationColumn_eq_zero
        (C.zeroDrift_endpointNormalizedPositiveChargedCirculation
          circulation)
    refine Or.inr ⟨⟨{
      scaledPotential := nextPotential
      gaugeFixedJet := nextJet
    }⟩, scaledPotential.2⟩

/-- The residual analytic alternative runs on a strictly smaller finite
operational type. -/
theorem zeroDrift_analyticIteration
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (nextAnchor : G.State) :
    Fintype.card C.ZeroDriftIndex <
        Fintype.card (germ.PlayerNeutralOccupationIndex who) ∧
      Xor
        (Nonempty
          (AnalyticPositiveChargedCirculation
            C.zeroDriftRawOccupationColumn
            C.zeroDriftRawOccupationCharge))
        (Nonempty (C.ZeroDriftAnalyticPotentialJet nextAnchor)) := by
  exact ⟨C.card_zeroDriftIndex_lt,
    C.zeroDrift_analyticPositiveChargedCirculation_xor_nextPotentialJet
      circulation nextAnchor⟩

end PlayerNeutralStrictLeadingDrift
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
