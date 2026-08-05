/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticPlayerOwnedCirculationPublicResponse
import GameTheory.Concepts.Stochastic.PlayerOwnedLeadingNeutralCirculation
import Math.Probability.AnalyticChargedCirculationLowerOrder

/-!
# Endpoint alternative for a player-owned analytic circulation

The leading mass of a full player-owned analytic charged circulation occurs
no later than the pole-clearing order.

* At equal order, the leading mass is a normalized positive circulation on
  the endpoint continuation-neutral operational family.  Existing finite
  analytic deflation then produces its honest terminal data.
* At strictly lower order, division by the leading scalar power leaves an
  honest positive analytic charged circulation with a smaller remaining
  pole degree when the removed order is positive.  Its endpoint mass is
  nonzero, balanced, nonnegative, and zero-charge.  The whole moving
  circulation nevertheless selects one fixed forward public response.
  Further positivity-preserving leading-mass extraction can stagnate, so
  this branch does not enter endpoint deflation.

This is an exhaustive analytic endpoint split.  It does not infer legal
entry, whole-target transport, public-response credibility, or a recursive
child.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.Probability
open Math.Probability.AnalyticPositiveChargedCirculation

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Data retained in the strict lower-order branch.  The residual
circulation is `jet.lowerOrderResidual order_lt`; naming the jet and strict
inequality keeps all of its endpoint and pole-order theorems available. -/
structure PlayerOwnedLowerOrderCirculationData
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)) where
  jet : C.LeadingMassJet
  order_lt : jet.order < C.poleOrder

namespace PlayerOwnedLowerOrderCirculationData

/-- The positivity-preserving residual circulation after removing the first
nonzero scalar mass power. -/
def residual
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (data : PlayerOwnedLowerOrderCirculationData germ B who C) :
    AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who) :=
  data.jet.lowerOrderResidual data.order_lt

/-- The residual still has a positive pole degree. -/
theorem residual_poleOrder_pos
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (data : PlayerOwnedLowerOrderCirculationData germ B who C) :
    0 < data.residual.poleOrder :=
  data.jet.lowerOrderResidual_poleOrder_pos data.order_lt

/-- Its endpoint mass is already nonzero. -/
theorem residual_mass_zero_ne
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (data : PlayerOwnedLowerOrderCirculationData germ B who C) :
    data.residual.mass 0 ≠ 0 :=
  data.jet.lowerOrderResidual_mass_zero_ne data.order_lt

end PlayerOwnedLowerOrderCirculationData

/-- Exhaustive endpoint outcome of one full player-owned analytic charged
circulation. -/
inductive PlayerOwnedCirculationEndpointAlternative
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (terminalAnchor : G.State) : Type _
  | neutralDeflationTerminal
      (jet : C.LeadingMassJet)
      (order_eq : jet.order = C.poleOrder)
      (terminal :
        PlayerNeutralAnalyticDeflationTerminalData
          germ B who
          (PlayerNeutralStrictLeadingDrift.fullDeflationState
            (germ := germ) (who := who))
          terminalAnchor)
  | lowerOrder
      (data : PlayerOwnedLowerOrderCirculationData germ B who C)
      (response :
        CirculationTiedAnalyticForwardFinkPublicResponse
          germ B who C)

/-- Every full player-owned analytic charged circulation reaches the
existing neutral-deflation terminal pipeline at equal order, or returns the
strict lower-order residual data without overstating it. -/
theorem exists_playerOwnedCirculationEndpointAlternative
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (terminalAnchor : G.State) :
    Nonempty
      (PlayerOwnedCirculationEndpointAlternative
        germ B who C terminalAnchor) := by
  obtain ⟨jet⟩ :=
    C.exists_leadingMassJet
      (germ.analytic_rawOwnerAnalyticOccupationColumn who)
      (germ.analytic_rawPlayerOwnedOccupationCharge B who)
  by_cases order_eq : jet.order = C.poleOrder
  · obtain ⟨terminal⟩ :=
      PlayerOwnedLeadingNeutralCirculation.exists_playerNeutralAnalyticDeflationTerminalData
        germ B who jet order_eq terminalAnchor
    exact ⟨.neutralDeflationTerminal jet order_eq terminal⟩
  · have order_lt : jet.order < C.poleOrder :=
      lt_of_le_of_ne jet.order_le_poleOrder order_eq
    obtain ⟨response⟩ :=
      exists_circulationTiedAnalyticForwardFinkPublicResponse
        germ B who C
    exact ⟨.lowerOrder ⟨jet, order_lt⟩ response⟩

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
