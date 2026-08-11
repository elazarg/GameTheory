/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOneStageObstructionCarrier
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtConservation

/-!
# The dynamic-debt source channel of a one-stage obstruction

The raw singleton/collision and endpoint-coboundary flow does not remember
the playerwise diagonal term in exact dynamic-debt conservation.  This file
adds precisely that missing datum.  A new grade-one coordinate records

`p_i * d_i`,

the current prescribed Quit probability of player `i` times its current
dynamic debt.  The source is still the exact boxed, punishment-floor
admissible one-edge graph; no strategic constraints are relaxed.

The enriched image is compact and contains every canonical one-stage tail
edge.  Across consecutive exact edges, identity chronological transport
weights the later debt source by the earlier joint survival, and exact
dynamic-debt conservation identifies the folded coordinate with the debt
consumed across the two edges.

The positive coordinate co-state pairs exactly with the diagonal seam.  Its
negative exposes the zero-seam face, because the canonical all-Continue
limit self-loop supplies an attainable zero while every source seam is
nonnegative.  Playerwise zero-face membership is exactly the corresponding
coordinate of augmented-cap transport; membership in every player's face is
the vector cap-lift criterion of `DynamicDebtCapBridge`.

This is raw finite-dimensional accounting.  In particular, the nonlinear
killed-capacity account is deliberately not made a flow coordinate, and no
strategic realization, boundary exhaustion, or return is asserted.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming.FlowCostateDuality
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

/-! ## The enriched one-edge flow -/

/-- Existing obstruction coordinates, together with one playerwise dynamic
debt-source coordinate. -/
abbrev QuittingDebtSourceObstructionCoordinate (ι : Type*) :=
  Sum (QuittingObstructionCoordinate ι) ι

/-- The exact one-edge raw obstruction enriched by the playerwise diagonal
dynamic-debt source in survival grade one. -/
def quittingDebtSourceObstructionFlow
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι) :
    RawGradedFlow QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι) :=
  fun grade coordinate ↦
    match coordinate with
    | Sum.inl base => quittingDebtEdgeObstructionFlow edge grade base
    | Sum.inr who =>
        match grade with
        | .charge => quittingDynamicDebtSeam edge.1 who
        | .coboundary => 0

@[simp]
theorem quittingDebtSourceObstructionFlow_base
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι)
    (grade : QuittingObstructionGrade)
    (coordinate : QuittingObstructionCoordinate ι) :
    quittingDebtSourceObstructionFlow edge grade (Sum.inl coordinate) =
      quittingDebtEdgeObstructionFlow edge grade coordinate := rfl

@[simp]
theorem quittingDebtSourceObstructionFlow_source
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι) (who : ι) :
    quittingDebtSourceObstructionFlow edge .charge (Sum.inr who) =
      quittingDynamicDebtSeam edge.1 who := rfl

@[simp]
theorem quittingDebtSourceObstructionFlow_source_offGrade
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι) (who : ι) :
    quittingDebtSourceObstructionFlow edge .coboundary (Sum.inr who) = 0 := rfl

omit [DecidableEq ι] in
private theorem continuous_quittingDebtEdgeDynamicDebtSeam (who : ι) :
    Continuous (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
      quittingDynamicDebtSeam edge.1 who) := by
  unfold quittingDynamicDebtSeam
  simp_rw [quittingRootOfSimplex_apply_toReal]
  have hprob : Continuous
      (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
        edge.1.1.2 who true) :=
    (continuous_apply true).comp
      (continuous_subtype_val.comp
        ((continuous_apply who).comp (by fun_prop)))
  have hdebt : Continuous
      (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
        edge.1.2 who) := by
    fun_prop
  exact hprob.mul hdebt

/-- The enriched raw flow depends continuously on its exact source edge. -/
theorem continuous_quittingDebtSourceObstructionFlow :
    Continuous (quittingDebtSourceObstructionFlow (ι := ι)) := by
  apply continuous_pi
  intro grade
  apply continuous_pi
  intro coordinate
  cases coordinate with
  | inl base =>
      exact (continuous_apply base).comp
        ((continuous_apply grade).comp
          (continuous_quittingDebtEdgeObstructionFlow (ι := ι)))
  | inr who =>
      cases grade with
      | charge =>
          simpa only [quittingDebtSourceObstructionFlow_source] using
            continuous_quittingDebtEdgeDynamicDebtSeam (ι := ι) who
      | coboundary =>
          simpa only [quittingDebtSourceObstructionFlow_source_offGrade] using
            (continuous_const : Continuous
              (fun _ : QuittingDebtPoint ι × QuittingDebtPoint ι ↦ (0 : ℝ)))

/-! ## Compact exact image and canonical sources -/

/-- Enriched one-stage raw flows sourced by the same boxed exact,
punishment-floor admissible edge graph as the base obstruction carrier. -/
def quittingDebtSourceOneStageObstructionCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (RawGradedFlow QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι)) :=
  quittingDebtSourceObstructionFlow ''
    quittingFloorDynamicDebtEdgeGraph reward

/-- The exact enriched one-stage carrier is compact. -/
theorem quittingDebtSourceOneStageObstructionCarrier_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (quittingDebtSourceOneStageObstructionCarrier reward) :=
  (quittingFloorDynamicDebtEdgeGraph_isCompact reward).image
    continuous_quittingDebtSourceObstructionFlow

/-- Every debt-source coordinate in the exact enriched carrier is
nonnegative. -/
theorem quittingDebtSourceObstructionCoordinate_nonneg
    {flow : RawGradedFlow QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι)}
    (hflow : flow ∈ quittingDebtSourceOneStageObstructionCarrier reward)
    (who : ι) :
    0 ≤ flow .charge (Sum.inr who) := by
  obtain ⟨edge, hedge, rfl⟩ := hflow
  exact quittingDynamicDebtSeam_nonneg edge.1 hedge.1.1 who

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

/-- Every canonical one-stage tail edge belongs to the exact enriched
carrier, now retaining its actual diagonal dynamic-debt source. -/
theorem debtSourceTailEdgeFlow_mem (time : ℕ) :
    quittingDebtSourceObstructionFlow
        (seam.tail time, seam.tail (time + 1)) ∈
      quittingDebtSourceOneStageObstructionCarrier reward := by
  exact ⟨(seam.tail time, seam.tail (time + 1)),
    seam.tailEdge_mem_quittingFloorDynamicDebtEdgeGraph time, rfl⟩

/-- The limiting all-Continue dynamic-debt point, written in the ambient
source type of the enriched carrier. -/
def limitDebtPoint : QuittingDebtPoint ι :=
  ((seam.limit.value, quittingAllContinueSimplexRoot), seam.limit.debt)

/-- The limiting all-Continue self-loop is an exact floor-admissible source
edge. -/
theorem limitDebtPoint_selfLoop_mem :
    (seam.limitDebtPoint, seam.limitDebtPoint) ∈
      quittingFloorDynamicDebtEdgeGraph reward := by
  refine ⟨⟨seam.limit.state_mem, seam.limit.state_mem,
    seam.limit.exactSelfLoop⟩, ?_⟩
  intro who
  exact ⟨seam.punishmentValue_le_limitValue who,
    seam.punishmentValue_le_limitValue who⟩

@[simp]
theorem limitDebtPoint_source_eq_zero (who : ι) :
    quittingDebtSourceObstructionFlow
        (seam.limitDebtPoint, seam.limitDebtPoint)
        .charge (Sum.inr who) = 0 := by
  simp [limitDebtPoint, quittingDynamicDebtSeam,
    quittingRootOfSimplex_allContinueSimplexRoot,
    quittingAllContinueRoot, PMF.pure_apply]

end QuittingCounterexampleSeamWitness

/-! ## Exact chronological folding -/

/-- Identity transport on the enriched coordinate carrier. -/
def quittingDebtSourceObstructionIdentityOperator :
    GradedOperator QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι)
      (QuittingDebtSourceObstructionCoordinate ι) :=
  fun _ output input ↦ if output = input then 1 else 0

@[simp]
theorem push_quittingDebtSourceObstructionIdentityOperator
    (flow : RawGradedFlow QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι)) :
    push (quittingDebtSourceObstructionIdentityOperator (ι := ι)) flow =
      flow := by
  funext grade output
  simp [push, quittingDebtSourceObstructionIdentityOperator]

@[simp]
theorem adjoint_quittingDebtSourceObstructionIdentityOperator
    (costate : Costate QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι)) :
    adjoint (quittingDebtSourceObstructionIdentityOperator (ι := ι)) costate =
      costate := by
  funext grade input
  simp [adjoint, quittingDebtSourceObstructionIdentityOperator]

/-- Identity chronological transport is pointwise addition, with grade-one
later coordinates weighted by the supplied survival. -/
theorem quittingDebtSource_survivalTransport_identity_apply
    (survival : ℝ)
    (earlier later : RawGradedFlow QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι))
    (grade : QuittingObstructionGrade)
    (coordinate : QuittingDebtSourceObstructionCoordinate ι) :
    survivalTransport quittingObstructionSurvivalDegree survival
        (quittingDebtSourceObstructionIdentityOperator (ι := ι))
        earlier later grade coordinate =
      earlier grade coordinate +
        survival ^ quittingObstructionSurvivalDegree grade *
          later grade coordinate := by
  simp only [survivalTransport, chronologicalTransport, flowAdd, reweight,
    push_quittingDebtSourceObstructionIdentityOperator]
  rfl

/-- Chronological fold of two one-edge enriched flows.  For consecutive
exact edges, the next theorem identifies its new coordinate by debt
conservation. -/
def quittingDebtSourceObstructionFold
    (earlier later : QuittingDebtPoint ι × QuittingDebtPoint ι) :
    RawGradedFlow QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι) :=
  survivalTransport quittingObstructionSurvivalDegree
    (quittingStationaryContinueMass
      (quittingRootOfSimplex earlier.1.1.2))
    (quittingDebtSourceObstructionIdentityOperator (ι := ι))
    (quittingDebtSourceObstructionFlow earlier)
    (quittingDebtSourceObstructionFlow later)

/-- Forgetting the new coordinate commutes exactly with chronological
folding of the base raw obstruction channels. -/
theorem quittingDebtSourceObstructionFold_base
    (earlier later : QuittingDebtPoint ι × QuittingDebtPoint ι)
    (grade : QuittingObstructionGrade)
    (coordinate : QuittingObstructionCoordinate ι) :
    quittingDebtSourceObstructionFold earlier later grade
        (Sum.inl coordinate) =
      survivalTransport quittingObstructionSurvivalDegree
        (quittingStationaryContinueMass
          (quittingRootOfSimplex earlier.1.1.2))
        (quittingObstructionIdentityOperator (ι := ι))
        (quittingDebtEdgeObstructionFlow earlier)
        (quittingDebtEdgeObstructionFlow later) grade coordinate := by
  rw [quittingDebtSourceObstructionFold,
    quittingDebtSource_survivalTransport_identity_apply,
    QuittingFiniteRootWindow.survivalTransport_identity_apply]
  simp only [quittingDebtSourceObstructionFlow_base]

/-- The folded player coordinate is the earlier diagonal seam plus the
survival-weighted later seam. -/
@[simp]
theorem quittingDebtSourceObstructionFold_source
    (earlier later : QuittingDebtPoint ι × QuittingDebtPoint ι)
    (who : ι) :
    quittingDebtSourceObstructionFold earlier later .charge
        (Sum.inr who) =
      quittingDynamicDebtSeam earlier.1 who +
        quittingStationaryContinueMass
            (quittingRootOfSimplex earlier.1.1.2) *
          quittingDynamicDebtSeam later.1 who := by
  rw [quittingDebtSourceObstructionFold,
    quittingDebtSource_survivalTransport_identity_apply]
  simp only [quittingDebtSourceObstructionFlow_source,
    quittingObstructionSurvivalDegree_charge, pow_one]

/-- **Two-edge exact debt fold.**  On supplied consecutive exact boxed
edges, the folded source coordinate is exactly current debt minus the debt
surviving both stages. -/
theorem quittingDebtSourceObstructionFold_eq_debt_sub_surviving
    (earlier later : QuittingDebtPoint ι × QuittingDebtPoint ι)
    (hearlier : earlier ∈ quittingFloorDynamicDebtEdgeGraph reward)
    (hlater : later ∈ quittingFloorDynamicDebtEdgeGraph reward)
    (hconsecutive : earlier.2 = later.1)
    (who : ι) :
    quittingDebtSourceObstructionFold earlier later .charge
        (Sum.inr who) =
      earlier.1.2 who -
        (quittingStationaryContinueMass
            (quittingRootOfSimplex earlier.1.1.2) *
          quittingStationaryContinueMass
            (quittingRootOfSimplex later.1.1.2)) * later.2.2 who := by
  have hfirst := quittingDynamicDebt_eq_continueMass_mul_add_seam
    (reward := reward) earlier.1 earlier.2 hearlier.1.2.2
      hearlier.1.2.1.2.1 who
  have hsecond := quittingDynamicDebt_eq_continueMass_mul_add_seam
    (reward := reward) later.1 later.2 hlater.1.2.2
      hlater.1.2.1.2.1 who
  rw [quittingDebtSourceObstructionFold_source]
  rw [hconsecutive] at hfirst
  have hseamEarlier :
      quittingDynamicDebtSeam earlier.1 who =
        earlier.1.2 who -
          quittingStationaryContinueMass
              (quittingRootOfSimplex earlier.1.1.2) * later.1.2 who := by
    linarith
  have hseamLater :
      quittingDynamicDebtSeam later.1 who =
        later.1.2 who -
          quittingStationaryContinueMass
              (quittingRootOfSimplex later.1.1.2) * later.2.2 who := by
    linarith
  rw [hseamEarlier, hseamLater]
  ring

/-! ## The coordinate co-state and its zero face -/

/-- The positive co-state selecting one player's grade-one debt-source
coordinate. -/
def quittingDebtSourceCostate (selected : ι) :
    Costate QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι) :=
  fun grade coordinate ↦
    match grade, coordinate with
    | .charge, Sum.inr who => if who = selected then 1 else 0
    | _, _ => 0

/-- The negative selector, whose maximizers are precisely the attainable
zero-source flows once a zero source is available. -/
def quittingDebtSourceZeroFaceCostate (selected : ι) :
    Costate QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι) :=
  fun grade coordinate ↦ -quittingDebtSourceCostate selected grade coordinate

@[simp]
theorem pair_quittingDebtSourceCostate
    (selected : ι)
    (flow : RawGradedFlow QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι)) :
    pair (quittingDebtSourceCostate selected) flow =
      flow .charge (Sum.inr selected) := by
  classical
  unfold pair
  have huniv : (Finset.univ : Finset QuittingObstructionGrade) =
      {.charge, .coboundary} := by decide
  rw [huniv]
  simp only [Finset.sum_insert, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, Finset.sum_singleton]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [quittingDebtSourceCostate]

@[simp]
theorem pair_quittingDebtSourceZeroFaceCostate
    (selected : ι)
    (flow : RawGradedFlow QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι)) :
    pair (quittingDebtSourceZeroFaceCostate selected) flow =
      -flow .charge (Sum.inr selected) := by
  classical
  unfold pair
  have huniv : (Finset.univ : Finset QuittingObstructionGrade) =
      {.charge, .coboundary} := by decide
  rw [huniv]
  simp only [Finset.sum_insert, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, Finset.sum_singleton]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [quittingDebtSourceZeroFaceCostate,
    quittingDebtSourceCostate]

/-- On a source edge, the positive coordinate co-state prices exactly the
diagonal dynamic-debt seam. -/
@[simp]
theorem pair_quittingDebtSourceCostate_edge
    (selected : ι)
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι) :
    pair (quittingDebtSourceCostate selected)
        (quittingDebtSourceObstructionFlow edge) =
      quittingDynamicDebtSeam edge.1 selected := by
  rw [pair_quittingDebtSourceCostate,
    quittingDebtSourceObstructionFlow_source]

/-- Identity survival adjoint transport merely multiplies the grade-one
debt-source selector by the survival factor. -/
theorem survivalAdjointUpdate_quittingDebtSourceCostate
    (survival : ℝ) (selected : ι) :
    survivalAdjointUpdate quittingObstructionSurvivalDegree survival
        (quittingDebtSourceObstructionIdentityOperator (ι := ι))
        (quittingDebtSourceCostate selected) =
      fun grade coordinate ↦
        survival ^ quittingObstructionSurvivalDegree grade *
          quittingDebtSourceCostate selected grade coordinate := by
  unfold survivalAdjointUpdate adjointUpdate
  rw [adjoint_quittingDebtSourceObstructionIdentityOperator]
  rfl

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

include seam in
/-- The negative selected-source co-state exposes exactly the flows whose
selected dynamic-debt source vanishes.  Nonnegativity comes from the exact
boxed source; attainment of zero comes from the all-Continue limit
self-loop. -/
theorem mem_exposedFace_quittingDebtSourceZeroFaceCostate_iff
    (selected : ι)
    (flow : RawGradedFlow QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι)) :
    flow ∈ exposedFace (quittingDebtSourceZeroFaceCostate selected)
        (quittingDebtSourceOneStageObstructionCarrier reward) ↔
      flow ∈ quittingDebtSourceOneStageObstructionCarrier reward ∧
        flow .charge (Sum.inr selected) = 0 := by
  constructor
  · intro hface
    refine ⟨hface.1, ?_⟩
    have hlimitMem :
        quittingDebtSourceObstructionFlow
            (limitDebtPoint seam, limitDebtPoint seam) ∈
          quittingDebtSourceOneStageObstructionCarrier reward :=
      ⟨(limitDebtPoint seam, limitDebtPoint seam),
        limitDebtPoint_selfLoop_mem seam, rfl⟩
    have hmax := hface.2 _ hlimitMem
    rw [pair_quittingDebtSourceZeroFaceCostate,
      pair_quittingDebtSourceZeroFaceCostate,
      limitDebtPoint_source_eq_zero seam, neg_zero] at hmax
    have hnonneg :=
      quittingDebtSourceObstructionCoordinate_nonneg hface.1 selected
    linarith
  · rintro ⟨hflow, hzero⟩
    refine ⟨hflow, ?_⟩
    intro candidate hcandidate
    rw [pair_quittingDebtSourceZeroFaceCostate,
      pair_quittingDebtSourceZeroFaceCostate, hzero, neg_zero]
    exact neg_nonpos.mpr
      (quittingDebtSourceObstructionCoordinate_nonneg hcandidate selected)

include seam in
/-- For an exact source edge, selected zero-face membership is precisely the
playerwise augmented-cap transport equation at that edge. -/
theorem debtSourceFlow_mem_zeroFace_iff_cap_transport_apply
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι)
    (hedge : edge ∈ quittingFloorDynamicDebtEdgeGraph reward)
    (selected : ι) :
    quittingDebtSourceObstructionFlow edge ∈
        exposedFace (quittingDebtSourceZeroFaceCostate selected)
          (quittingDebtSourceOneStageObstructionCarrier reward) ↔
      quittingDynamicDebtCap edge.1 selected =
        quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap edge.2)
          (quittingRootOfSimplex edge.1.1.2) selected := by
  rw [mem_exposedFace_quittingDebtSourceZeroFaceCostate_iff seam selected]
  have hmem : quittingDebtSourceObstructionFlow edge ∈
      quittingDebtSourceOneStageObstructionCarrier reward :=
    ⟨edge, hedge, rfl⟩
  have hseam := quittingDynamicDebtCap_sub_rootSuccessorPayoff_eq
    reward edge.1 edge.2 hedge.1.2.2 hedge.1.2.1.2.1 selected
  constructor
  · rintro ⟨_, hzero⟩
    rw [quittingDebtSourceObstructionFlow_source] at hzero
    unfold quittingDynamicDebtSeam at hzero
    linarith
  · intro htransport
    refine ⟨hmem, ?_⟩
    rw [quittingDebtSourceObstructionFlow_source]
    unfold quittingDynamicDebtSeam
    linarith

include seam in
/-- Membership in every playerwise zero-source face is exactly the vector
augmented-cap transport condition of `DynamicDebtCapBridge`. -/
theorem debtSourceFlow_mem_all_zeroFaces_iff_cap_transport
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι)
    (hedge : edge ∈ quittingFloorDynamicDebtEdgeGraph reward) :
    (∀ selected,
      quittingDebtSourceObstructionFlow edge ∈
        exposedFace (quittingDebtSourceZeroFaceCostate selected)
          (quittingDebtSourceOneStageObstructionCarrier reward)) ↔
      quittingDynamicDebtCap edge.1 =
        quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap edge.2)
          (quittingRootOfSimplex edge.1.1.2) := by
  constructor
  · intro hfaces
    funext selected
    exact (debtSourceFlow_mem_zeroFace_iff_cap_transport_apply seam
      edge hedge selected).1 (hfaces selected)
  · intro htransport selected
    apply (debtSourceFlow_mem_zeroFace_iff_cap_transport_apply seam
      edge hedge selected).2
    exact congrFun htransport selected

end QuittingCounterexampleSeamWitness

end GameTheory
