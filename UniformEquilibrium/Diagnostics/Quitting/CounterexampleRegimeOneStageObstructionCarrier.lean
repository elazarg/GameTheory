/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeBallisticity
import UniformEquilibrium.Quitting.AbsorptionPath.FlowCostateObstructionAdapter
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtAugmentedEdge

/-!
# Compact one-stage raw-obstruction carrier for a counterexample tail

The non-plateau tangent extraction uses literal one-stage windows.  This file
keeps those windows at raw scale: no absorption normalization and no union over
word lengths occurs.

The source carrier is the compact graph of boxed exact dynamic-debt
Nash--Bellman edges, intersected with the closed condition that both endpoint
values dominate the behavioral punishment floor.  An edge determines one
literal one-stage root window with its current and successor value annotations.
Its image under `toObstructionRawGradedFlow` is therefore a compact
finite-dimensional set of two-grade raw obstructions.  Every one-stage window
of the canonical counterexample tail belongs to this image, and every finite
co-state pairing attains a support value once that tail supplies nonemptiness.

Compactness here does not select a co-state, compare a killed boundary,
normalize by absorption, expose a recurrent face, or realize a strategic
word.  Membership retains the exact source edge only existentially through
the image witness.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming.FlowCostateDuality
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

/-! ## Closed exact floor-admissible edge source -/

/-- Boxed exact dynamic-debt edges whose two value annotations both dominate
the behavioral punishment floor. -/
def quittingFloorDynamicDebtEdgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingDebtPoint ι × QuittingDebtPoint ι) :=
  {edge | edge ∈ quittingDynamicDebtEdgeGraph reward ∧
    ∀ who,
      quittingPunishmentValue reward who ≤ edge.1.1.1 who ∧
      quittingPunishmentValue reward who ≤ edge.2.1.1 who}

/-- The floor-admissible exact dynamic-debt edge graph is closed. -/
theorem isClosed_quittingFloorDynamicDebtEdgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsClosed (quittingFloorDynamicDebtEdgeGraph reward) := by
  let floorSet : Set (QuittingDebtPoint ι × QuittingDebtPoint ι) :=
    {edge | ∀ who,
      quittingPunishmentValue reward who ≤ edge.1.1.1 who ∧
      quittingPunishmentValue reward who ≤ edge.2.1.1 who}
  have hfloor : IsClosed floorSet := by
    have heq : floorSet = ⋂ who,
        {edge | quittingPunishmentValue reward who ≤ edge.1.1.1 who} ∩
        {edge | quittingPunishmentValue reward who ≤ edge.2.1.1 who} := by
      ext edge
      simp [floorSet]
    rw [heq]
    apply isClosed_iInter
    intro who
    exact (isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_le continuous_const (by fun_prop))
  have heq : quittingFloorDynamicDebtEdgeGraph reward =
      quittingDynamicDebtEdgeGraph reward ∩ floorSet := by
    ext edge
    simp [quittingFloorDynamicDebtEdgeGraph, floorSet]
  rw [heq]
  exact (isClosed_quittingDynamicDebtEdgeGraph reward).inter hfloor

/-- The exact floor-admissible one-stage source is compact. -/
theorem quittingFloorDynamicDebtEdgeGraph_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (quittingFloorDynamicDebtEdgeGraph reward) := by
  apply (quittingDynamicDebtEdgeGraph_isCompact reward).of_isClosed_subset
    (isClosed_quittingFloorDynamicDebtEdgeGraph reward)
  intro edge hedge
  exact hedge.1

/-! ## One edge as one literal annotated window -/

/-- Constant operational root sequence used to present one source edge as a
one-stage window.  Only time zero is read by that window. -/
def quittingDebtEdgeRootSequence
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι) :
    ℕ → ι → PMF Bool :=
  fun _ ↦ quittingRootOfSimplex edge.1.1.2

/-- Current value at time zero and successor value at every positive time.
The associated window reads exactly times zero and one. -/
def quittingDebtEdgeAnnotation
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι) :
    ℕ → Payoff ι
  | 0 => edge.1.1.1
  | _ + 1 => edge.2.1.1

/-- The literal one-stage window sourced by an augmented edge. -/
def quittingDebtEdgeOneStageWindow
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι) :
    QuittingFiniteRootWindow (quittingDebtEdgeRootSequence edge) where
  start := 0
  fuel := 1

/-- The unnormalized two-grade obstruction of one exact source edge. -/
def quittingDebtEdgeObstructionFlow
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι) :
    RawGradedFlow QuittingObstructionGrade
      (QuittingObstructionCoordinate ι) :=
  (quittingDebtEdgeOneStageWindow edge).toObstructionRawGradedFlow
    (quittingDebtEdgeAnnotation edge)

@[simp]
theorem quittingDebtEdgeObstructionFlow_singleton
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι) (owner : ι) :
    quittingDebtEdgeObstructionFlow edge .charge
        (Sum.inl (.singleton owner)) =
      quittingRootCoalitionMass (quittingRootOfSimplex edge.1.1.2) {owner} := by
  simp [quittingDebtEdgeObstructionFlow, quittingDebtEdgeOneStageWindow,
    QuittingFiniteRootWindow.toObstructionRawGradedFlow_charge,
    QuittingFiniteRootWindow.rawCharge_singleton_value,
    QuittingFiniteRootWindow.singletonMass,
    QuittingFiniteRootWindow.survivalWeight,
    QuittingFiniteRootWindow.rootAt, quittingDebtEdgeRootSequence]

@[simp]
theorem quittingDebtEdgeObstructionFlow_collision
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι) :
    quittingDebtEdgeObstructionFlow edge .charge (Sum.inl .collision) =
      quittingRootCollisionMass (quittingRootOfSimplex edge.1.1.2) := by
  simp [quittingDebtEdgeObstructionFlow, quittingDebtEdgeOneStageWindow,
    QuittingFiniteRootWindow.toObstructionRawGradedFlow_charge,
    QuittingFiniteRootWindow.rawCharge_collision_value,
    QuittingFiniteRootWindow.collisionMass,
    QuittingFiniteRootWindow.survivalWeight,
    QuittingFiniteRootWindow.rootAt, quittingDebtEdgeRootSequence]

@[simp]
theorem quittingDebtEdgeObstructionFlow_endpoint
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι) (who : ι) :
    quittingDebtEdgeObstructionFlow edge .coboundary (Sum.inr who) =
      edge.1.1.1 who - edge.2.1.1 who := by
  rfl

@[simp]
theorem quittingDebtEdgeObstructionFlow_charge_player
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι) (who : ι) :
    quittingDebtEdgeObstructionFlow edge .charge (Sum.inr who) = 0 := rfl

@[simp]
theorem quittingDebtEdgeObstructionFlow_coboundary_charge
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι)
    (channel : QuittingWindowChargeChannel ι) :
    quittingDebtEdgeObstructionFlow edge .coboundary
        (Sum.inl channel) = 0 := rfl

private theorem continuous_quittingDebtEdgeCoalitionMass
    (coalition : Finset ι) :
    Continuous (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
      quittingRootCoalitionMass
        (quittingRootOfSimplex edge.1.1.2) coalition) := by
  unfold quittingRootCoalitionMass quittingRootQuitRates
    Math.PMFProduct.coalitionMass
  simp_rw [quittingRootOfSimplex_apply_toReal]
  have hcoordinate : ∀ who : ι, Continuous
      (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
        edge.1.1.2 who true) := by
    intro who
    exact (continuous_apply true).comp
      (continuous_subtype_val.comp
        ((continuous_apply who).comp (by fun_prop)))
  apply Continuous.mul
  · apply continuous_finsetProd
    intro who _
    exact hcoordinate who
  · apply continuous_finsetProd
    intro who _
    exact continuous_const.sub (hcoordinate who)

private theorem continuous_quittingDebtEdgeCollisionMass :
    Continuous (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
      quittingRootCollisionMass
        (quittingRootOfSimplex edge.1.1.2)) := by
  simp_rw [quittingRootCollisionMass_eq_sum_coalitionMass]
  exact continuous_finsetSum _ fun coalition _ ↦
    continuous_quittingDebtEdgeCoalitionMass coalition

/-- The raw one-edge obstruction depends continuously on its boxed exact
source edge. -/
theorem continuous_quittingDebtEdgeObstructionFlow :
    Continuous (quittingDebtEdgeObstructionFlow (ι := ι)) := by
  apply continuous_pi
  intro grade
  apply continuous_pi
  intro coordinate
  cases grade with
  | charge =>
      cases coordinate with
      | inl channel =>
          cases channel with
          | singleton owner =>
              simpa only [quittingDebtEdgeObstructionFlow_singleton] using
                continuous_quittingDebtEdgeCoalitionMass {owner}
          | collision =>
              simpa only [quittingDebtEdgeObstructionFlow_collision] using
                (continuous_quittingDebtEdgeCollisionMass (ι := ι))
      | inr who =>
          simpa only [quittingDebtEdgeObstructionFlow_charge_player] using
            (continuous_const : Continuous
              (fun _ : QuittingDebtPoint ι × QuittingDebtPoint ι ↦ (0 : ℝ)))
  | coboundary =>
      cases coordinate with
      | inl channel =>
          simpa only [quittingDebtEdgeObstructionFlow_coboundary_charge] using
            (continuous_const : Continuous
              (fun _ : QuittingDebtPoint ι × QuittingDebtPoint ι ↦ (0 : ℝ)))
      | inr who =>
          simp only [quittingDebtEdgeObstructionFlow_endpoint]
          fun_prop

/-! ## Compact image and canonical-tail membership -/

/-- Finite-dimensional raw obstruction flows sourced by boxed exact
floor-admissible one-stage edges. -/
def quittingOneStageObstructionCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (RawGradedFlow QuittingObstructionGrade
      (QuittingObstructionCoordinate ι)) :=
  quittingDebtEdgeObstructionFlow ''
    quittingFloorDynamicDebtEdgeGraph reward

/-- The exact one-stage raw-obstruction carrier is compact. -/
theorem quittingOneStageObstructionCarrier_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (quittingOneStageObstructionCarrier reward) :=
  (quittingFloorDynamicDebtEdgeGraph_isCompact reward).image
    continuous_quittingDebtEdgeObstructionFlow

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

/-- Every adjacent pair of canonical tail states is an exact boxed
floor-admissible source edge. -/
theorem tailEdge_mem_quittingFloorDynamicDebtEdgeGraph (time : ℕ) :
    (seam.tail time, seam.tail (time + 1)) ∈
      quittingFloorDynamicDebtEdgeGraph reward := by
  refine ⟨⟨seam.tail_mem time, seam.tail_mem (time + 1),
    seam.tail_edge time⟩, ?_⟩
  intro who
  exact ⟨seam.punishmentValue_le_tailValue time who,
    seam.punishmentValue_le_tailValue (time + 1) who⟩

/-- The edge presentation and the literal canonical one-stage tail window
produce the same unnormalized two-grade flow. -/
theorem quittingDebtEdgeObstructionFlow_tailEdge_eq (time : ℕ) :
    quittingDebtEdgeObstructionFlow
        (seam.tail time, seam.tail (time + 1)) =
      (seam.finiteRootWindow time 1).toObstructionRawGradedFlow
        (fun date ↦ (seam.tail date).1.1) := by
  funext grade coordinate
  cases grade with
  | charge =>
      cases coordinate with
      | inl channel =>
          cases channel with
          | singleton owner =>
              simp [QuittingFiniteRootWindow.toObstructionRawGradedFlow_charge,
                QuittingFiniteRootWindow.rawCharge_singleton_value,
                QuittingFiniteRootWindow.singletonMass,
                QuittingFiniteRootWindow.survivalWeight,
                QuittingFiniteRootWindow.rootAt,
                quittingDynamicDebtTailRoots]
          | collision =>
              simp [QuittingFiniteRootWindow.toObstructionRawGradedFlow_charge,
                QuittingFiniteRootWindow.rawCharge_collision_value,
                QuittingFiniteRootWindow.collisionMass,
                QuittingFiniteRootWindow.survivalWeight,
                QuittingFiniteRootWindow.rootAt,
                quittingDynamicDebtTailRoots]
      | inr who => simp
  | coboundary =>
      cases coordinate with
      | inl channel => simp
      | inr who => rfl

/-- Every literal one-stage window of the canonical non-plateau extraction
belongs to the exact compact raw-obstruction carrier. -/
theorem oneStageTailFlow_mem_quittingOneStageObstructionCarrier (time : ℕ) :
    (seam.finiteRootWindow time 1).toObstructionRawGradedFlow
        (fun date ↦ (seam.tail date).1.1) ∈
      quittingOneStageObstructionCarrier reward := by
  refine ⟨(seam.tail time, seam.tail (time + 1)),
    seam.tailEdge_mem_quittingFloorDynamicDebtEdgeGraph time, ?_⟩
  exact (seam.quittingDebtEdgeObstructionFlow_tailEdge_eq time).symm

/-- The canonical tail makes the exact one-stage carrier nonempty. -/
theorem quittingOneStageObstructionCarrier_nonempty
    (seam : QuittingCounterexampleSeamWitness regime) :
    (quittingOneStageObstructionCarrier reward).Nonempty :=
  ⟨(seam.finiteRootWindow 0 1).toObstructionRawGradedFlow
      (fun date ↦ (seam.tail date).1.1),
    seam.oneStageTailFlow_mem_quittingOneStageObstructionCarrier 0⟩

end QuittingCounterexampleSeamWitness

/-! ## Attained finite co-state support -/

omit [DecidableEq ι] in
/-- Pairing with a fixed finite co-state is continuous in the raw flow. -/
theorem continuous_pair_quittingObstructionCostate
    (costate : Costate QuittingObstructionGrade
      (QuittingObstructionCoordinate ι)) :
    Continuous (pair costate) := by
  unfold pair
  fun_prop

/-- Every co-state support is attained on a nonempty exact one-stage carrier. -/
theorem exists_hasSupportValue_quittingOneStageObstructionCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hne : (quittingOneStageObstructionCarrier reward).Nonempty)
    (costate : Costate QuittingObstructionGrade
      (QuittingObstructionCoordinate ι)) :
    ∃ value,
      HasSupportValue costate
        (quittingOneStageObstructionCarrier reward) value := by
  obtain ⟨chosen, hchosen, hmax⟩ :=
    (quittingOneStageObstructionCarrier_isCompact reward).exists_isMaxOn
      hne (continuous_pair_quittingObstructionCostate costate).continuousOn
  refine ⟨pair costate chosen, ?_⟩
  constructor
  · intro candidate hcandidate
    rw [isMaxOn_iff] at hmax
    exact hmax candidate hcandidate
  · exact ⟨chosen, hchosen, rfl⟩

namespace QuittingCounterexampleSeamWitness

/-- In a counterexample regime, the canonical tail supplies nonemptiness, so
every finite co-state has an attained support value on the exact carrier. -/
theorem exists_hasSupportValue_oneStageObstructionCarrier
    (seam : QuittingCounterexampleSeamWitness regime)
    (costate : Costate QuittingObstructionGrade
      (QuittingObstructionCoordinate ι)) :
    ∃ value,
      HasSupportValue costate
        (quittingOneStageObstructionCarrier reward) value :=
  exists_hasSupportValue_quittingOneStageObstructionCarrier reward
    (quittingOneStageObstructionCarrier_nonempty seam) costate

end QuittingCounterexampleSeamWitness

end GameTheory
