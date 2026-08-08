/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.AnalyticNeutralActionPublicResponse
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.ResidualStrictDeflation
import Math.Probability.PositiveChargedCirculationClass

/-!
# Operational terminal data from player-neutral analytic deflation

The generic well-founded analytic deflation outcome is specialized here to
the raw player-neutral Bellman occupation family of one fixed player.

Both terminal branches yield concrete owner-preserving endpoint data:

* the normalized endpoint circulation on the terminal active subtype;
* a positive-charge communicating class of that active endpoint flow;
* one active continuation-neutral action of the fixed player with positive
  endpoint charge, together with its active-index witness; and
* the corresponding fixed analytic forward public response.

The analytic-circulation branch additionally retains the terminal punctured
analytic circulation.  The zero-pairing branch instead yields an exact active harmonicity
certificate: a nonzero leading state potential has zero endpoint drift on
every remaining active baseline or player-owned action column.  Deleted
columns are exposed as the terminal exceptional set; no false full-kernel
harmonicity is asserted.  An ambient zero-extension of either stored active
circulation is available only as a derived convenience.

These are the strongest unconditional operational consequences currently
available.  The positive class has only its internal representative and
does not provide legal reachability from an arbitrary public history.
Neither branch transports the complete payoff-vector target or constructs a
credible continuation/punishment strategy.  Those entry, target, and
strategic-interface obligations remain explicit blockers.
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

local instance terminalPlayerNeutralIndexDecidableEq
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    DecidableEq (germ.PlayerNeutralOccupationIndex who) :=
  Classical.decEq _

variable
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {initial : FiniteDeflationState
      (germ.PlayerNeutralOccupationIndex who)}
    {terminalAnchor : G.State}

/-- Extend the terminal active-subtype endpoint circulation by zero outside
the active set and identify the raw endpoint family with the static
player-neutral occupation family.  This ambient circulation is a derived
convenience; terminal semantic data retain the active-subtype circulation
itself. -/
theorem ambientPlayerNeutralEndpointCirculation
    (outcome :
      AnalyticOccupationDeflationOutcome initial
        (germ.rawPlayerNeutralOccupationColumn who)
        (germ.rawPlayerNeutralOccupationCharge B who)
        terminalAnchor) :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn
        (germ.playerNeutralOccupationKernel who)
        (germ.playerNeutralOccupationSource who))
      (germ.playerNeutralOccupationCharge B who) := by
  have activeCirculation :
      HasNormalizedPositiveChargedCirculation
        (fun index : outcome.terminal.ActiveIndex =>
          germ.rawPlayerNeutralOccupationColumn
            who 0 index.1)
        (fun index : outcome.terminal.ActiveIndex =>
          germ.rawPlayerNeutralOccupationCharge
            B who 0 index.1) := by
    change
      HasNormalizedPositiveChargedCirculation
        (activeOccupationColumn outcome.terminal
          (germ.rawPlayerNeutralOccupationColumn who) 0)
        (activeOccupationCharge outcome.terminal
          (germ.rawPlayerNeutralOccupationCharge B who) 0)
    exact outcome.endpointCirculation
  have ambientCirculation :=
    activeCirculation.extendActive outcome.terminal
      (germ.rawPlayerNeutralOccupationColumn who 0)
      (germ.rawPlayerNeutralOccupationCharge B who 0)
  simpa only [
    germ.rawPlayerNeutralOccupationColumn_zero who,
    germ.rawPlayerNeutralOccupationCharge_zero B who
  ] using ambientCirculation

/-- Positive charge in a terminal active-subtype circulation is carried by
an actual active continuation-neutral response. -/
theorem exists_active_positive_neutralActionCharge
    (terminal :
      FiniteDeflationState (germ.PlayerNeutralOccupationIndex who))
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (fun index : terminal.ActiveIndex =>
            germ.playerNeutralOccupationKernel who index.1)
          (fun index : terminal.ActiveIndex =>
            germ.playerNeutralOccupationSource who index.1))
        (fun index : terminal.ActiveIndex =>
          germ.playerNeutralOccupationCharge B who index.1)) :
    ∃ (index : terminal.ActiveIndex)
        (response : germ.ContinuationNeutralAction who),
      index.1 = Sum.inr response ∧
        0 < germ.neutralActionCharge B who response := by
  obtain ⟨mass, mass_nonneg, balance, charge_eq_one⟩ :=
    circulation
  have exists_positive_product :
      ∃ index : terminal.ActiveIndex,
        0 <
          mass index *
            germ.playerNeutralOccupationCharge B who index.1 := by
    by_contra hnone
    push Not at hnone
    have hsum_nonpos :
        (∑ index,
          mass index *
            germ.playerNeutralOccupationCharge B who index.1) ≤ 0 := by
      exact Finset.sum_nonpos fun index _ => hnone index
    rw [charge_eq_one] at hsum_nonpos
    norm_num at hsum_nonpos
  obtain ⟨index, hpositive⟩ := exists_positive_product
  rcases hindex : index.1 with source | response
  · simp [hindex, playerNeutralOccupationCharge] at hpositive
  · refine ⟨index, response, hindex, ?_⟩
    apply pos_of_mul_pos_right
    · simpa [hindex, playerNeutralOccupationCharge] using hpositive
    · exact mass_nonneg index

/-- Concrete operational data in the terminal analytic-circulation branch. -/
structure PlayerNeutralAnalyticCirculationTerminalData
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (initial : FiniteDeflationState
      (germ.PlayerNeutralOccupationIndex who))
    (terminalAnchor : G.State) where
  terminal :
    FiniteDeflationState (germ.PlayerNeutralOccupationIndex who)
  trace :
    AnalyticOccupationDeflationTrace
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)
      terminalAnchor initial terminal
  analyticCirculation :
    AnalyticPositiveChargedCirculation
      (activeOccupationColumn terminal
        (germ.rawPlayerNeutralOccupationColumn who))
      (activeOccupationCharge terminal
        (germ.rawPlayerNeutralOccupationCharge B who))
  endpointCirculation :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn
        (fun index : terminal.ActiveIndex =>
          germ.playerNeutralOccupationKernel who index.1)
        (fun index : terminal.ActiveIndex =>
          germ.playerNeutralOccupationSource who index.1))
      (fun index : terminal.ActiveIndex =>
        germ.playerNeutralOccupationCharge B who index.1)
  positiveClass :
    PositiveChargedCirculationClass
      (fun index : terminal.ActiveIndex =>
        germ.playerNeutralOccupationKernel who index.1)
      (fun index : terminal.ActiveIndex =>
        germ.playerNeutralOccupationSource who index.1)
      (fun index : terminal.ActiveIndex =>
        germ.playerNeutralOccupationCharge B who index.1)
  responseIndex : terminal.ActiveIndex
  response : germ.ContinuationNeutralAction who
  responseIndex_eq : responseIndex.1 = Sum.inr response
  responseCharge_pos :
    0 < germ.neutralActionCharge B who response
  analyticPublicResponse :
    AnalyticForwardFinkPublicResponse germ B 0

/-- Concrete active harmonic/complementarity data in the terminal
zero-leading-pairing branch. -/
structure PlayerNeutralZeroPairingTerminalData
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (initial : FiniteDeflationState
      (germ.PlayerNeutralOccupationIndex who))
    (terminalAnchor : G.State) where
  terminal :
    FiniteDeflationState (germ.PlayerNeutralOccupationIndex who)
  trace :
    AnalyticOccupationDeflationTrace
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)
      terminalAnchor initial terminal
  endpointCirculation :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn
        (fun index : terminal.ActiveIndex =>
          germ.playerNeutralOccupationKernel who index.1)
        (fun index : terminal.ActiveIndex =>
          germ.playerNeutralOccupationSource who index.1))
      (fun index : terminal.ActiveIndex =>
        germ.playerNeutralOccupationCharge B who index.1)
  positiveClass :
    PositiveChargedCirculationClass
      (fun index : terminal.ActiveIndex =>
        germ.playerNeutralOccupationKernel who index.1)
      (fun index : terminal.ActiveIndex =>
        germ.playerNeutralOccupationSource who index.1)
      (fun index : terminal.ActiveIndex =>
        germ.playerNeutralOccupationCharge B who index.1)
  responseIndex : terminal.ActiveIndex
  response : germ.ContinuationNeutralAction who
  responseIndex_eq : responseIndex.1 = Sum.inr response
  responseCharge_pos :
    0 < germ.neutralActionCharge B who response
  analyticPublicResponse :
    AnalyticForwardFinkPublicResponse germ B 0
  next :
    ActiveAnalyticPotentialJet terminal
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)
      terminalAnchor
  pairing_zero :
    ∀ index, next.leadingPairing index = 0
  leadingPotential_nonzero :
    next.gaugeFixedJet.factor 0 ≠ 0
  active_harmonic :
    ∀ index : terminal.ActiveIndex,
      expect
          (germ.playerNeutralOccupationKernel who index.1)
          (next.gaugeFixedJet.factor 0) -
        next.gaugeFixedJet.factor 0
          (germ.playerNeutralOccupationSource who index.1) =
        0

namespace PlayerNeutralAnalyticCirculationTerminalData

/-- Zero-extend the provenance-preserving active circulation when an ambient
circulation is convenient for an older occupation theorem. -/
theorem ambientEndpointCirculation
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor) :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn
        (germ.playerNeutralOccupationKernel who)
        (germ.playerNeutralOccupationSource who))
      (germ.playerNeutralOccupationCharge B who) := by
  exact data.endpointCirculation.extendActive data.terminal
    (actualOccupationColumn
      (germ.playerNeutralOccupationKernel who)
      (germ.playerNeutralOccupationSource who))
    (germ.playerNeutralOccupationCharge B who)

end PlayerNeutralAnalyticCirculationTerminalData

namespace PlayerNeutralZeroPairingTerminalData

/-- Zero-extend the provenance-preserving active circulation when an ambient
circulation is convenient for an older occupation theorem. -/
theorem ambientEndpointCirculation
    (data :
      PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor) :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn
        (germ.playerNeutralOccupationKernel who)
        (germ.playerNeutralOccupationSource who))
      (germ.playerNeutralOccupationCharge B who) := by
  exact data.endpointCirculation.extendActive data.terminal
    (actualOccupationColumn
      (germ.playerNeutralOccupationKernel who)
      (germ.playerNeutralOccupationSource who))
    (germ.playerNeutralOccupationCharge B who)

end PlayerNeutralZeroPairingTerminalData

/-- Operational interpretation of the two generic terminal branches. -/
inductive PlayerNeutralAnalyticDeflationTerminalData
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (initial : FiniteDeflationState
      (germ.PlayerNeutralOccupationIndex who))
    (terminalAnchor : G.State) : Type _
  | analyticCirculation
      (data :
        PlayerNeutralAnalyticCirculationTerminalData
          germ B who initial terminalAnchor)
  | zeroPairing
      (data :
        PlayerNeutralZeroPairingTerminalData
          germ B who initial terminalAnchor)

/-- Consume a generic analytic-deflation outcome into the strongest
currently available player-owned operational terminal data. -/
theorem toPlayerNeutralTerminalData
    (outcome :
      AnalyticOccupationDeflationOutcome initial
        (germ.rawPlayerNeutralOccupationColumn who)
        (germ.rawPlayerNeutralOccupationCharge B who)
        terminalAnchor) :
    Nonempty
      (PlayerNeutralAnalyticDeflationTerminalData
        germ B who initial terminalAnchor) := by
  have activeCirculation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (fun index : outcome.terminal.ActiveIndex =>
            germ.playerNeutralOccupationKernel who index.1)
          (fun index : outcome.terminal.ActiveIndex =>
            germ.playerNeutralOccupationSource who index.1))
        (fun index : outcome.terminal.ActiveIndex =>
          germ.playerNeutralOccupationCharge B who index.1) := by
    have rawActive :
        HasNormalizedPositiveChargedCirculation
          (fun index : outcome.terminal.ActiveIndex =>
            germ.rawPlayerNeutralOccupationColumn who 0 index.1)
          (fun index : outcome.terminal.ActiveIndex =>
            germ.rawPlayerNeutralOccupationCharge B who 0 index.1) := by
      change
        HasNormalizedPositiveChargedCirculation
          (activeOccupationColumn outcome.terminal
            (germ.rawPlayerNeutralOccupationColumn who) 0)
          (activeOccupationCharge outcome.terminal
            (germ.rawPlayerNeutralOccupationCharge B who) 0)
      exact outcome.endpointCirculation
    rw [germ.rawPlayerNeutralOccupationColumn_zero who,
      germ.rawPlayerNeutralOccupationCharge_zero B who] at rawActive
    exact rawActive
  obtain ⟨positiveClass⟩ :=
    activeCirculation.exists_positiveChargedClass
      (fun index : outcome.terminal.ActiveIndex =>
        germ.playerNeutralOccupationKernel who index.1)
      (fun index : outcome.terminal.ActiveIndex =>
        germ.playerNeutralOccupationSource who index.1)
      (fun index : outcome.terminal.ActiveIndex =>
        germ.playerNeutralOccupationCharge B who index.1)
  obtain ⟨responseIndex, response, responseIndex_eq,
      responseCharge_pos⟩ :=
    exists_active_positive_neutralActionCharge
      outcome.terminal activeCirculation
  obtain ⟨analyticPublicResponse⟩ :=
    germ.exists_analyticForwardFinkPublicResponse_of_neutralActionCharge_pos
      B who response responseCharge_pos
  cases outcome.certificate with
  | analyticCirculation analyticWitness =>
      exact ⟨.analyticCirculation {
        terminal := outcome.terminal
        trace := outcome.trace
        analyticCirculation := analyticWitness
        endpointCirculation := activeCirculation
        positiveClass := positiveClass
        responseIndex := responseIndex
        response := response
        responseIndex_eq := responseIndex_eq
        responseCharge_pos := responseCharge_pos
        analyticPublicResponse := analyticPublicResponse
      }⟩
  | zeroPairing next pairing_zero =>
      have active_harmonic :
          ∀ index : outcome.terminal.ActiveIndex,
            expect
                (germ.playerNeutralOccupationKernel who index.1)
                (next.gaugeFixedJet.factor 0) -
              next.gaugeFixedJet.factor 0
                (germ.playerNeutralOccupationSource who index.1) =
              0 := by
        intro index
        have pairing := pairing_zero index
        change
          (∑ destination,
            next.gaugeFixedJet.factor 0 destination *
              germ.rawPlayerNeutralOccupationColumn
                who 0 index.1 destination) = 0 at pairing
        rw [germ.rawPlayerNeutralOccupationColumn_zero who] at pairing
        rw [potential_pair_actualOccupationColumn] at pairing
        exact pairing
      exact ⟨.zeroPairing {
        terminal := outcome.terminal
        trace := outcome.trace
        endpointCirculation := activeCirculation
        positiveClass := positiveClass
        responseIndex := responseIndex
        response := response
        responseIndex_eq := responseIndex_eq
        responseCharge_pos := responseCharge_pos
        analyticPublicResponse := analyticPublicResponse
        next := next
        pairing_zero := pairing_zero
        leadingPotential_nonzero :=
          next.gaugeFixedJet.leading_ne_zero
        active_harmonic := active_harmonic
      }⟩

/-- Run the complete finite analytic deflation and immediately expose its
player-owned operational terminal data. -/
theorem exists_playerNeutralAnalyticDeflationTerminalData
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (initial : FiniteDeflationState
      (germ.PlayerNeutralOccupationIndex who))
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (activeOccupationColumn initial
          (germ.rawPlayerNeutralOccupationColumn who) 0)
        (activeOccupationCharge initial
          (germ.rawPlayerNeutralOccupationCharge B who) 0))
    (terminalAnchor : G.State) :
    Nonempty
      (PlayerNeutralAnalyticDeflationTerminalData
        germ B who initial terminalAnchor) := by
  obtain ⟨outcome⟩ :=
    exists_analyticOccupationDeflationOutcome
      initial
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)
      (germ.analytic_rawPlayerNeutralOccupationColumn who)
      (germ.analytic_rawPlayerNeutralOccupationCharge B who)
      (germ.eventually_sum_rawPlayerNeutralOccupationColumn_eq_zero who)
      circulation terminalAnchor
  exact toPlayerNeutralTerminalData outcome

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
