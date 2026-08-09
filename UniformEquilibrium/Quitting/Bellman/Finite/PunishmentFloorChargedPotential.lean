/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorChargedRelation

/-!
# Bounded potentials for punishment-floor predecessor reachability

A common absorption-charge bound for every exact Nash--Bellman predecessor
prefix from the punishment floor bounds every path in the reachable class.
`Math.ChargedPathBudget` therefore supplies its canonical budget-to-go
potential.  This file records the potential with its sharp range and edge
decrement inequality, and specializes that inequality to the canonical
forward orbit.

The hypothesis ranges over all legal anchored predecessor selections.  The
bounded branch of `quittingGame_uniformPayoff_or_punishmentFloorForwardChargeBound`
only controls one selected orbit and does not discharge it.  Conversely, the
potential obtained here is an accounting certificate on exact reachable
Bellman states; it does not construct a tail, consume a prefix, or produce a
uniform equilibrium.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

private abbrev ReachableRelation :=
  quittingPunishmentFloorReachableChargedRelation reward

/-- The canonical budget-to-go potential on punishment-floor reachable
Nash--Bellman states. -/
def quittingPunishmentFloorReachablePotential
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (state : QuittingPunishmentFloorReachableState reward) : ℝ :=
  (quittingPunishmentFloorReachableChargedRelation reward).value state

/-- A common anchored-prefix charge bound makes the canonical budget-to-go
function a bounded potential on the reachable relation. -/
theorem quittingPunishmentFloorReachablePotential_isBoundedPotential
    {chargeBound : ℝ}
    (hbound : HasQuittingPunishmentFloorAnchoredChargeBound reward chargeBound) :
    ReachableRelation.IsBoundedPotential
      (quittingPunishmentFloorReachablePotential reward) := by
  exact ReachableRelation.value_isBoundedPotential
    (quittingPunishmentFloorReachable_hasFiniteBudget_of_anchoredChargeBound
      hbound)

/-- In particular, a bounded potential exists on the reachable charged
relation. -/
theorem exists_quittingPunishmentFloorReachable_boundedPotential
    {chargeBound : ℝ}
    (hbound : HasQuittingPunishmentFloorAnchoredChargeBound reward chargeBound) :
    ∃ Φ : QuittingPunishmentFloorReachableState reward → ℝ,
      ReachableRelation.IsBoundedPotential Φ :=
  ⟨quittingPunishmentFloorReachablePotential reward,
    quittingPunishmentFloorReachablePotential_isBoundedPotential hbound⟩

/-- The canonical potential is nonnegative. -/
theorem quittingPunishmentFloorReachablePotential_nonneg
    {chargeBound : ℝ}
    (hbound : HasQuittingPunishmentFloorAnchoredChargeBound reward chargeBound)
    (state : QuittingPunishmentFloorReachableState reward) :
    0 ≤ quittingPunishmentFloorReachablePotential reward state := by
  exact ReachableRelation.value_nonneg
    (quittingPunishmentFloorReachable_hasFiniteBudget_of_anchoredChargeBound
      hbound) state

/-- The common anchored-prefix bound also bounds the canonical potential
pointwise. -/
theorem quittingPunishmentFloorReachablePotential_le_chargeBound
    {chargeBound : ℝ}
    (hbound : HasQuittingPunishmentFloorAnchoredChargeBound reward chargeBound)
    (state : QuittingPunishmentFloorReachableState reward) :
    quittingPunishmentFloorReachablePotential reward state ≤ chargeBound := by
  apply ReachableRelation.value_le hbound.nonneg
  intro target path
  exact reachablePath_chargeSum_le_of_anchoredChargeBound hbound path

/-- Every exact reachable predecessor step spends its actual absorption mass
as a decrement of the canonical potential. -/
theorem quittingPunishmentFloorReachablePotential_predecessor_decrement
    {chargeBound : ℝ}
    (hbound : HasQuittingPunishmentFloorAnchoredChargeBound reward chargeBound)
    (edge : QuittingPunishmentFloorReachableEdge reward) :
    quittingPunishmentFloorReachablePotential reward edge.current +
        edge.toBoxEdge.absorptionCharge ≤
      quittingPunishmentFloorReachablePotential reward edge.tail := by
  exact
    (quittingPunishmentFloorReachablePotential_isBoundedPotential hbound).isPotential
      edge

/-! ## Exact specialization to the selected forward orbit -/

/-- The selected punishment-floor forward point as a reachable state. -/
def quittingPunishmentFloorSelectedReachableState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (time : ℕ) :
    QuittingPunishmentFloorReachableState reward :=
  ⟨quittingPunishmentFloorSelectedBoxState reward time,
    isQuittingPunishmentFloorReachable_selectedBoxState time⟩

/-- One selected forward predecessor update as an edge of the full reachable
relation. -/
def quittingPunishmentFloorSelectedReachableEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (time : ℕ) :
    QuittingPunishmentFloorReachableEdge reward where
  tail := quittingPunishmentFloorSelectedReachableState reward time
  current := quittingPunishmentFloorSelectedReachableState reward (time + 1)
  exactEdge := quittingPunishmentFloorForwardPoint_related reward time

/-- The selected edge's abstract charge is its literal forward-root
absorption mass. -/
@[simp] theorem quittingPunishmentFloorSelectedReachableEdge_charge
    (time : ℕ) :
    (quittingPunishmentFloorReachableChargedRelation reward).charge
        (quittingPunishmentFloorSelectedReachableEdge reward time) =
      quittingRootAbsorptionMass
        (quittingPunishmentFloorForwardRoot reward time) :=
  rfl

/-- Along the selected exact orbit, the same bounded potential decreases by
at least the literal one-stage absorption charge. -/
theorem quittingPunishmentFloorSelected_potential_decrement
    {chargeBound : ℝ}
    (hbound : HasQuittingPunishmentFloorAnchoredChargeBound reward chargeBound)
    (time : ℕ) :
    quittingPunishmentFloorReachablePotential reward
          (quittingPunishmentFloorSelectedReachableState reward (time + 1)) +
        quittingRootAbsorptionMass
          (quittingPunishmentFloorForwardRoot reward time) ≤
      quittingPunishmentFloorReachablePotential reward
        (quittingPunishmentFloorSelectedReachableState reward time) := by
  simpa only [quittingPunishmentFloorSelectedReachableEdge,
    QuittingPunishmentFloorReachableEdge.toBoxEdge,
    QuittingPunishmentFloorBoxEdge.absorptionCharge,
    QuittingPunishmentFloorBoxEdge.root,
    quittingPunishmentFloorSelectedReachableState,
    quittingPunishmentFloorSelectedBoxState,
    quittingPunishmentFloorForwardRoot] using
    quittingPunishmentFloorReachablePotential_predecessor_decrement hbound
      (quittingPunishmentFloorSelectedReachableEdge reward time)

end GameTheory
