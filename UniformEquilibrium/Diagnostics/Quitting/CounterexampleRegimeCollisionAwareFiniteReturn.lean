/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacket
import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import UniformEquilibrium.Quitting.Cycles.ExactCycleStrata
import UniformEquilibrium.Quitting.Debt.Marked.FenceIteration

/-!
# Collision-aware finite returns from product-root delivery

For a fixed product root, its stationary terminal payoff is exactly its
absorption-normalized delivery.  It retains every simultaneous-quitting
coalition in the product law.  One backward Bellman step is therefore the
affine segment

`current = survival * tail + (1 - survival) * delivery`.

This file packages the minimal finite collision-aware return interface.  Its
phase equations are the full-vector affine equations above, and its local
strategic fields are exact product-root Nash.  A supplied finite return is
immediately an existing solved exact cycle once punishment admissibility is
given; no new orbit or behavioral compiler is duplicated.

The interface also records the precise local information supplied by a
physical Nash--Bellman edge: the affine segment identity, pure-Quit pinning
on every positive quit coordinate, and vanishing Boolean--Möbius derivative
on every genuinely mixed coordinate.  The module does not construct the
finite normalized return from tangent compatibility or projective
chronology.  That construction is the remaining global realization seam.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Collision-aware delivery of one fixed product root.  When the root has
positive absorption this is its absorbing contribution divided by absorption
mass; the stationary definition avoids introducing a partial division. -/
def quittingProductRootAbsorbingDelivery
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) : Payoff ι :=
  fun who => quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) who

omit [DecidableEq ι] in
/-- A fixed product root acts affinely between its continuation and its full
collision-aware absorbing delivery. -/
theorem quittingRootSuccessorPayoff_eq_survival_mul_add_absorption_mul_delivery
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward tail root who =
      quittingStationaryContinueMass root * tail who +
        quittingRootAbsorptionMass root *
          quittingProductRootAbsorbingDelivery reward root who := by
  change quittingRootExpectedPayoff reward tail root who = _
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    ← one_sub_continueMass_mul_quittingTerminalPayoff_stationary]
  unfold quittingRootAbsorptionMass quittingProductRootAbsorbingDelivery
  ring

namespace IsQuittingNashBellmanEdge

/-- Every physical exact edge lies on the collision-aware affine segment of
its displayed product root. -/
theorem eq_collisionAwareSegment
    {current tail : QuittingNashBellmanPoint ι}
    (edge : IsQuittingNashBellmanEdge reward current tail) (who : ι) :
    current.1 who =
      quittingStationaryContinueMass (quittingRootOfSimplex current.2) *
          tail.1 who +
        quittingRootAbsorptionMass (quittingRootOfSimplex current.2) *
          quittingProductRootAbsorbingDelivery reward
            (quittingRootOfSimplex current.2) who := by
  calc
    current.1 who = quittingRootSuccessorPayoff reward tail.1
        (quittingRootOfSimplex current.2) who := congrFun edge.1 who
    _ = _ :=
      quittingRootSuccessorPayoff_eq_survival_mul_add_absorption_mul_delivery
        reward tail.1 (quittingRootOfSimplex current.2) who

/-- A positive Quit coordinate of a physical edge is exactly pinned to the
current Bellman value. -/
theorem quitPayoff_eq_current_of_quitProbability_pos
    {current tail : QuittingNashBellmanPoint ι}
    (edge : IsQuittingNashBellmanEdge reward current tail) (who : ι)
    (hquit : 0 <
      ((quittingRootOfSimplex current.2) who true).toReal) :
    quittingRootQuitPayoff reward tail.1
        (quittingRootOfSimplex current.2) who = current.1 who := by
  have hnash : IsεQuittingRootNash reward tail.1 0
      (quittingRootOfSimplex current.2) :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail.1 (quittingRootOfSimplex current.2)).1 edge.2
  calc
    quittingRootQuitPayoff reward tail.1
        (quittingRootOfSimplex current.2) who =
      quittingRootSuccessorPayoff reward tail.1
        (quittingRootOfSimplex current.2) who :=
          quittingRootQuitPayoff_eq_successor_of_quitProbability_pos
            reward tail.1 (quittingRootOfSimplex current.2) who hnash hquit
    _ = current.1 who := (congrFun edge.1 who).symm

/-- On every genuinely mixed coordinate of a physical edge, the exact
Boolean--Möbius active-row derivative vanishes. -/
theorem mobiusCoordinateDerivative_eq_zero_of_interior
    {current tail : QuittingNashBellmanPoint ι}
    (edge : IsQuittingNashBellmanEdge reward current tail) (who : ι)
    (hquit : 0 <
      ((quittingRootOfSimplex current.2) who true).toReal)
    (hcontinue : 0 <
      ((quittingRootOfSimplex current.2) who false).toReal) :
    (quittingStageCenteredCoalGame reward tail.1 who).coordinateDerivative
        (hazardOfRoot (quittingRootOfSimplex current.2)) who = 0 := by
  have hendpoint := edge.2 who
  have hnonpos : quittingRootEndpointDifference reward tail.1
      (quittingRootOfSimplex current.2) who ≤ 0 := by
    exact nonpos_of_mul_nonpos_left
      (by simpa only [mul_comm] using hendpoint.1) hcontinue
  have hnonneg : 0 ≤ quittingRootEndpointDifference reward tail.1
      (quittingRootOfSimplex current.2) who := by
    exact nonneg_of_mul_nonneg_left
      (by simpa only [neg_zero, mul_comm] using hendpoint.2) hquit
  rw [← quittingRootEndpointDifference_eq_mobiusCoordinateDerivative]
  exact le_antisymm hnonpos hnonneg

end IsQuittingNashBellmanEdge

/-- Minimal collision-aware finite return to a prescribed boundary.  The
`closure` field is the finite family of full-vector phase equations; the
phase target is the actual absorbing delivery of that phase's product root.
Exact root Nash supplies all unilateral Boolean--Möbius conditions, while
`punishment` is kept explicit because finite Bellman closure alone does not
control an infinite Continue deviation. -/
structure QuittingCollisionAwareFiniteReturn
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (boundary : Payoff ι) (K : ℕ) [NeZero K] where
  root : Fin K → ι → PMF Bool
  value : Fin K → Payoff ι
  startsAt : value 0 = boundary
  absorption_pos : ∀ phase, 0 < quittingRootAbsorptionMass (root phase)
  closure : ∀ phase who,
    value phase who =
      quittingStationaryContinueMass (root phase) *
          value (finRotate K phase) who +
        quittingRootAbsorptionMass (root phase) *
          quittingProductRootAbsorbingDelivery reward (root phase) who
  nash : ∀ phase, IsεQuittingRootNash reward
    (value (finRotate K phase)) 0 (root phase)
  punishment : IsQuittingCyclePunishmentAdmissible reward root

namespace QuittingCollisionAwareFiniteReturn

/-- Every return phase is genuinely absorbing; in particular the compact
all-Continue self-loop produced by bounded-orbit chronology cannot inhabit
this normalized-return interface. -/
theorem root_ne_allContinueRoot
    {boundary : Payoff ι} {K : ℕ} [NeZero K]
    (returnData : QuittingCollisionAwareFiniteReturn reward boundary K)
    (phase : Fin K) :
    returnData.root phase ≠ quittingAllContinueRoot := by
  intro hroot
  have habsorb := returnData.absorption_pos phase
  rw [hroot, quittingRootAbsorptionMass_allContinueRoot] at habsorb
  exact lt_irrefl 0 habsorb

/-- Equivalently, every normalized return phase has survival strictly below
one. -/
theorem continueMass_lt_one
    {boundary : Payoff ι} {K : ℕ} [NeZero K]
    (returnData : QuittingCollisionAwareFiniteReturn reward boundary K)
    (phase : Fin K) :
    quittingStationaryContinueMass (returnData.root phase) < 1 := by
  rw [← sub_pos]
  exact returnData.absorption_pos phase

/-- The collision-aware full-vector closure equations are exactly the usual
root-successor equations. -/
theorem policy
    {boundary : Payoff ι} {K : ℕ} [NeZero K]
    (returnData : QuittingCollisionAwareFiniteReturn reward boundary K)
    (phase : Fin K) :
    returnData.value phase = quittingRootSuccessorPayoff reward
      (returnData.value (finRotate K phase)) (returnData.root phase) := by
  funext who
  calc
    returnData.value phase who =
        quittingStationaryContinueMass (returnData.root phase) *
            returnData.value (finRotate K phase) who +
          quittingRootAbsorptionMass (returnData.root phase) *
            quittingProductRootAbsorbingDelivery reward
              (returnData.root phase) who := returnData.closure phase who
    _ = quittingRootSuccessorPayoff reward
        (returnData.value (finRotate K phase))
          (returnData.root phase) who :=
      (quittingRootSuccessorPayoff_eq_survival_mul_add_absorption_mul_delivery
        reward (returnData.value (finRotate K phase))
          (returnData.root phase) who).symm

/-- The normalized return is already a solved exact cycle in the repository's
existing strategic interface. -/
theorem isSolvedExactQuittingCycle
    {boundary : Payoff ι} {K : ℕ} [NeZero K]
    (returnData : QuittingCollisionAwareFiniteReturn reward boundary K) :
    IsSolvedExactQuittingCycle reward returnData.root returnData.value := by
  refine ⟨⟨returnData.policy, returnData.nash⟩, ?_, returnData.punishment⟩
  exact prod_quittingStationaryContinueMass_univ_lt_one_of_absorbing
    returnData.root 0 (returnData.absorption_pos 0)

/-- A finite collision-aware normalized return compiles to a uniform-
equilibrium payoff at its prescribed boundary. -/
theorem boundary_isUniformEquilibriumPayoff
    {boundary : Payoff ι} {K : ℕ} [NeZero K]
    (returnData : QuittingCollisionAwareFiniteReturn reward boundary K) :
    (quittingGame reward).IsUniformEquilibriumPayoff none boundary := by
  rw [← returnData.startsAt]
  exact isUniformEquilibriumPayoff_of_isSolvedExactQuittingCycle reward
    returnData.root returnData.value 0 returnData.isSolvedExactQuittingCycle

end QuittingCollisionAwareFiniteReturn

namespace QuittingChargeTangentPacket

/-- Packet-anchored name for the exact global realization object still
needed after local tangent compatibility has produced physical edges. -/
abbrev CollisionAwareFiniteReturn
    (packet : QuittingChargeTangentPacket reward)
    (K : ℕ) [NeZero K] :=
  QuittingCollisionAwareFiniteReturn reward packet.boundary K

/-- Any packet-anchored collision-aware finite return is already enough for
the uniform-payoff conclusion.  Compatibility is an upstream root-production
condition, not an additional compiler hypothesis. -/
theorem boundary_isUniformEquilibriumPayoff_of_collisionAwareFiniteReturn
    (packet : QuittingChargeTangentPacket reward)
    {K : ℕ} [NeZero K]
    (returnData : packet.CollisionAwareFiniteReturn K) :
    (quittingGame reward).IsUniformEquilibriumPayoff none packet.boundary :=
  returnData.boundary_isUniformEquilibriumPayoff

end QuittingChargeTangentPacket

namespace QuittingCounterexampleRegime

/-- A counterexample regime forbids every finite packet-anchored normalized
return.  Hence local compatible arcs must fail either finite full-vector
closure, absorption, or punishment-admissible recurrence. -/
theorem not_nonempty_collisionAwareFiniteReturn
    (regime : QuittingCounterexampleRegime reward)
    (packet : QuittingChargeTangentPacket reward)
    (K : ℕ) [NeZero K] :
    ¬ Nonempty (packet.CollisionAwareFiniteReturn K) := by
  rintro ⟨returnData⟩
  exact regime.not_exists_uniformEquilibriumPayoff
    ⟨packet.boundary,
      packet.boundary_isUniformEquilibriumPayoff_of_collisionAwareFiniteReturn
        returnData⟩

end QuittingCounterexampleRegime

end GameTheory
