/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentSupportTransversality

/-!
# A projective gauge for the compatible tangent blow-up system

The exceptional-divisor packet bases form a scale line.  The literal support
blow-up residual therefore has a nonzero radial-zero kernel direction, and
its ungauged regular-level hypotheses cannot produce a physical branch.

This file removes exactly that direction with the affine normalization

`∑ owner, leading owner = 1`.

The normalized packet mass already lies in this slice.  The slice is
parameterized by zero-sum leading variations, so it is a genuine finite
normed vector chart rather than an affine subtype.  Its range is proved to be
exactly the displayed hyperplane.

After gauge fixing, the full residual is square.  Surjectivity of its full
derivative would isolate the base; it is not an arc criterion.  The honest
regular interface therefore takes a finite-dimensional reduced residual and
an explicit local exact-recovery hypothesis saying that no full equation was
lost on the slice.  Surjectivity of the reduced derivative together with an
outward kernel direction then gives an analytic arc of *full* residual zeros.
Every positive physical point on that arc is consumed by the existing exact
Nash--Bellman decoder.

The local recovery premise is deliberately visible.  This module does not
derive it from compatibility, does not assert a global return, and does not
turn a merely projected zero into a strategic root.
-/

noncomputable section

open Filter Finset Set Topology

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## The affine sum-one slice -/

/-- Total leading hazard coefficient, as a continuous linear functional. -/
def quittingBlowupLeadingTotal : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ owner, ContinuousLinearMap.proj owner

omit [DecidableEq ι] in
@[simp]
theorem quittingBlowupLeadingTotal_apply (leading : ι → ℝ) :
    quittingBlowupLeadingTotal leading = ∑ owner, leading owner := by
  simp [quittingBlowupLeadingTotal]

/-- Linear tangent space of the affine normalization `∑ leading = 1`. -/
abbrev QuittingLeadingGaugeVariation (ι : Type) [Fintype ι] :=
  (quittingBlowupLeadingTotal (ι := ι)).ker

/-- Radial coordinate, zero-sum leading variation, and unrestricted
continuation-drift variation. -/
abbrev QuittingProjectiveGaugePoint (ι : Type) [Fintype ι] :=
  ℝ × (QuittingLeadingGaugeVariation ι × (ι → ℝ))

/-- Distinguished radial coordinate on the gauged chart. -/
def quittingProjectiveGaugeRadialCoordinate :
    QuittingProjectiveGaugePoint ι →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ
    (QuittingLeadingGaugeVariation ι × (ι → ℝ))

/-- Affine sum-one chart centered at the unit-scale packet base. -/
def QuittingChargeTangentPacket.projectiveGaugeChart
    (packet : QuittingChargeTangentPacket reward)
    (point : QuittingProjectiveGaugePoint ι) : QuittingBlowupPoint ι :=
  (point.1,
    packet.mass + point.2.1.1,
    packet.blowupContinuationDrift 1 + point.2.2)

namespace QuittingChargeTangentPacket

@[simp]
theorem projectiveGaugeChart_zero
    (packet : QuittingChargeTangentPacket reward) :
    packet.projectiveGaugeChart 0 = packet.blowupBasePoint 1 := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext owner
    simp [projectiveGaugeChart, blowupBasePoint, blowupLeading]
  · funext who
    simp [projectiveGaugeChart, blowupBasePoint,
      blowupContinuationDrift]

@[simp]
theorem projectiveGaugeChart_radial
    (packet : QuittingChargeTangentPacket reward)
    (point : QuittingProjectiveGaugePoint ι) :
    quittingBlowupRadialCoordinate (packet.projectiveGaugeChart point) =
      quittingProjectiveGaugeRadialCoordinate point :=
  rfl

/-- Every chart point has total leading coefficient exactly one. -/
theorem projectiveGaugeChart_leadingTotal
    (packet : QuittingChargeTangentPacket reward)
    (point : QuittingProjectiveGaugePoint ι) :
    quittingBlowupLeadingTotal (packet.projectiveGaugeChart point).2.1 = 1 := by
  change quittingBlowupLeadingTotal (packet.mass + point.2.1.1) = 1
  rw [map_add, quittingBlowupLeadingTotal_apply, packet.mass_sum]
  have hzero : quittingBlowupLeadingTotal point.2.1.1 = 0 :=
    point.2.1.property
  rw [hzero, add_zero]

/-- The affine chart is injective: precisely the projective scale direction
has been removed. -/
theorem projectiveGaugeChart_injective
    (packet : QuittingChargeTangentPacket reward) :
    Function.Injective packet.projectiveGaugeChart := by
  intro first second heq
  have hradial : first.1 = second.1 :=
    congrArg (fun point : QuittingBlowupPoint ι => point.1) heq
  have hleading : first.2.1.1 = second.2.1.1 := by
    have h := congrArg (fun point : QuittingBlowupPoint ι => point.2.1) heq
    change packet.mass + first.2.1.1 = packet.mass + second.2.1.1 at h
    exact add_left_cancel h
  have hdrift : first.2.2 = second.2.2 := by
    have h := congrArg (fun point : QuittingBlowupPoint ι => point.2.2) heq
    change packet.blowupContinuationDrift 1 + first.2.2 =
      packet.blowupContinuationDrift 1 + second.2.2 at h
    exact add_left_cancel h
  apply Prod.ext hradial
  apply Prod.ext
  · exact Subtype.ext hleading
  · exact hdrift

/-- Exact global range of the affine chart.  Thus there is neither a hidden
positivity restriction nor a second gauge direction. -/
theorem mem_range_projectiveGaugeChart_iff
    (packet : QuittingChargeTangentPacket reward)
    (point : QuittingBlowupPoint ι) :
    point ∈ Set.range packet.projectiveGaugeChart ↔
      quittingBlowupLeadingTotal point.2.1 = 1 := by
  constructor
  · rintro ⟨coordinate, rfl⟩
    exact packet.projectiveGaugeChart_leadingTotal coordinate
  · intro htotal
    let variation : QuittingLeadingGaugeVariation ι :=
      ⟨point.2.1 - packet.mass, by
        change quittingBlowupLeadingTotal (point.2.1 - packet.mass) = 0
        rw [map_sub, htotal, quittingBlowupLeadingTotal_apply,
          packet.mass_sum, sub_self]⟩
    let coordinate : QuittingProjectiveGaugePoint ι :=
      (point.1,
        variation,
        point.2.2 - packet.blowupContinuationDrift 1)
    refine ⟨coordinate, ?_⟩
    ext owner <;>
      simp [coordinate, variation, projectiveGaugeChart]

/-- The affine chart is analytic at every coordinate. -/
theorem analyticAt_projectiveGaugeChart
    (packet : QuittingChargeTangentPacket reward)
    (point : QuittingProjectiveGaugePoint ι) :
    AnalyticAt ℝ packet.projectiveGaugeChart point := by
  let tail : QuittingProjectiveGaugePoint ι →L[ℝ]
      (QuittingLeadingGaugeVariation ι × (ι → ℝ)) :=
    ContinuousLinearMap.snd ℝ ℝ
      (QuittingLeadingGaugeVariation ι × (ι → ℝ))
  let leadingVariation : QuittingProjectiveGaugePoint ι →L[ℝ] (ι → ℝ) :=
    (Submodule.subtypeL (quittingBlowupLeadingTotal (ι := ι)).ker).comp
      ((ContinuousLinearMap.fst ℝ
        (QuittingLeadingGaugeVariation ι) (ι → ℝ)).comp tail)
  let driftVariation : QuittingProjectiveGaugePoint ι →L[ℝ] (ι → ℝ) :=
    (ContinuousLinearMap.snd ℝ
      (QuittingLeadingGaugeVariation ι) (ι → ℝ)).comp tail
  have hradial : AnalyticAt ℝ
      (fun coordinate : QuittingProjectiveGaugePoint ι => coordinate.1)
      point :=
    (quittingProjectiveGaugeRadialCoordinate (ι := ι)).analyticAt point
  have hleading : AnalyticAt ℝ
      (fun coordinate : QuittingProjectiveGaugePoint ι =>
        packet.mass + coordinate.2.1.1) point := by
    exact analyticAt_const.add (leadingVariation.analyticAt point)
  have hdrift : AnalyticAt ℝ
      (fun coordinate : QuittingProjectiveGaugePoint ι =>
        packet.blowupContinuationDrift 1 + coordinate.2.2) point := by
    exact analyticAt_const.add (driftVariation.analyticAt point)
  exact hradial.prod (hleading.prod hdrift)

/-! ## Exact residual and physical decoding on the slice -/

/-- Full support residual pulled back to the projective gauge slice. -/
def projectiveGaugeResidual
    (packet : QuittingChargeTangentPacket reward) (support : Finset ι)
    (point : QuittingProjectiveGaugePoint ι) :
    QuittingBlowupEqRow ι support → ℝ :=
  quittingSupportBlowupResidual reward packet.boundary support
    (packet.projectiveGaugeChart point)

/-- Exact set-level equivalence between gauged full zeros and ungauged full
zeros in the affine sum-one slice. -/
theorem mem_image_projectiveGauge_zeroSet_iff
    (packet : QuittingChargeTangentPacket reward) (support : Finset ι)
    (point : QuittingBlowupPoint ι) :
    point ∈ packet.projectiveGaugeChart ''
        {coordinate | packet.projectiveGaugeResidual support coordinate = 0} ↔
      quittingSupportBlowupResidual reward packet.boundary support point = 0 ∧
        quittingBlowupLeadingTotal point.2.1 = 1 := by
  constructor
  · rintro ⟨coordinate, hzero, rfl⟩
    exact ⟨hzero, packet.projectiveGaugeChart_leadingTotal coordinate⟩
  · rintro ⟨hzero, htotal⟩
    obtain ⟨coordinate, hcoordinate⟩ :=
      (packet.mem_range_projectiveGaugeChart_iff point).mpr htotal
    refine ⟨coordinate, ?_, hcoordinate⟩
    simpa [projectiveGaugeResidual, hcoordinate] using hzero

@[simp]
theorem projectiveGaugeResidual_zero
    (packet : QuittingChargeTangentPacket reward) (support : Finset ι)
    (hsupport : ∀ who, who ∈ support ↔ 0 < packet.mass who)
    (hcompat : ∀ who ∈ support,
      quittingActivePairCompatibilityResidual packet who = 0) :
    packet.projectiveGaugeResidual support 0 = 0 := by
  rw [projectiveGaugeResidual, packet.projectiveGaugeChart_zero]
  exact packet.supportBlowupResidual_basePoint_eq_zero 1 support
    hsupport hcompat

/-- The pulled-back full residual remains analytic. -/
theorem analyticAt_projectiveGaugeResidual
    (packet : QuittingChargeTangentPacket reward) (support : Finset ι)
    (point : QuittingProjectiveGaugePoint ι) :
    AnalyticAt ℝ (packet.projectiveGaugeResidual support) point := by
  exact (analyticAt_quittingSupportBlowupResidual
    packet.boundary support (packet.projectiveGaugeChart point)).comp
      (packet.analyticAt_projectiveGaugeChart point)

/-- A full zero on the gauge slice is consumed by the existing exact physical
root decoder.  All strategic inequalities remain explicit inputs. -/
theorem isNashBellmanRoot_of_projectiveGaugeResidual_eq_zero
    (packet : QuittingChargeTangentPacket reward) (support : Finset ι)
    (point : QuittingProjectiveGaugePoint ι)
    (hresidual : packet.projectiveGaugeResidual support point = 0)
    (hpacketActive : ∀ who ∈ support, 0 < packet.mass who)
    (hhazard_nonneg : ∀ who,
      0 ≤ quittingBlowupHazard point.1
        (packet.projectiveGaugeChart point).2.1 who)
    (hhazard_lt_one : ∀ who,
      quittingBlowupHazard point.1
        (packet.projectiveGaugeChart point).2.1 who < 1)
    (houtside : ∀ who ∉ support,
      gainValue (weightOfReward reward)
        (quittingBlowupHazard point.1
          (packet.projectiveGaugeChart point).2.1) who
        (packet.boundary who +
          point.1 * (packet.projectiveGaugeChart point).2.2 who) < 0) :
    let chartPoint := packet.projectiveGaugeChart point
    let hazard := quittingBlowupHazard chartPoint.1 chartPoint.2.1
    let continuation : Payoff ι :=
      fun who ↦ packet.boundary who + chartPoint.1 * chartPoint.2.2 who
    let root := rootOfHazard hazard hhazard_nonneg
      (fun who ↦ (hhazard_lt_one who).le)
    packet.boundary = quittingRootSuccessorPayoff reward continuation root ∧
      IsεQuittingRootEndpointNash reward continuation 0 root := by
  exact isNashBellmanRoot_of_supportBlowupResidual_eq_zero
    packet support (packet.projectiveGaugeChart point) hresidual
      hpacketActive hhazard_nonneg hhazard_lt_one houtside

/-! ## Honest reduced regularity interface -/

/-- **Projectively gauged regular arc criterion.**  `projection` chooses a
finite reduced equality system.  The hypothesis `hrecover` is the exact local
equivalence seam: on the supplied chart neighborhood, projected zeros are
full support-residual zeros.  Under that seam, ordinary regular-level
surjectivity and a positive radial kernel vector yield an analytic arc of
literal full zeros in the affine sum-one slice.

This is nonvacuous after gauge fixing when the reduced target has one fewer
dimension than the chart.  No such reduction or recovery is inferred merely
from packet compatibility. -/
theorem hasPositiveRadialAnalyticArcAt_of_regular_projectiveGauge
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (packet : QuittingChargeTangentPacket reward) (support : Finset ι)
    (hsupport : ∀ who, who ∈ support ↔ 0 < packet.mass who)
    (hcompat : ∀ who ∈ support,
      quittingActivePairCompatibilityResidual packet who = 0)
    (projection :
      (QuittingBlowupEqRow ι support → ℝ) →L[ℝ] F)
    (W : Set (QuittingProjectiveGaugePoint ι)) (hW : W ∈ 𝓝 0)
    (hrecover : ∀ point ∈ W,
      projection (packet.projectiveGaugeResidual support point) = 0 ↔
        packet.projectiveGaugeResidual support point = 0)
    (U : Set (QuittingBlowupPoint ι))
    (hU : U ∈ 𝓝 (packet.blowupBasePoint 1))
    (hsurj :
      (fderiv ℝ
        (fun point =>
          projection (packet.projectiveGaugeResidual support point)) 0).range =
        ⊤)
    (direction :
      (fderiv ℝ
        (fun point =>
          projection (packet.projectiveGaugeResidual support point)) 0).ker)
    (hdirection :
      0 < quittingProjectiveGaugeRadialCoordinate direction.1) :
    Math.HasPositiveCoordinateAnalyticArcAt
      ({point |
          quittingSupportBlowupResidual reward packet.boundary support point =
            0 ∧
          quittingBlowupLeadingTotal point.2.1 = 1} ∩ U)
      quittingBlowupRadialCoordinate (packet.blowupBasePoint 1) := by
  let reduced : QuittingProjectiveGaugePoint ι → F :=
    fun point => projection (packet.projectiveGaugeResidual support point)
  have hreducedAnalytic : AnalyticAt ℝ reduced 0 := by
    exact projection.analyticAt
      (packet.projectiveGaugeResidual support 0) |>.comp
        (packet.analyticAt_projectiveGaugeResidual support 0)
  have hbaseFull : packet.projectiveGaugeResidual support 0 = 0 :=
    packet.projectiveGaugeResidual_zero support hsupport hcompat
  have hbaseReduced : reduced 0 = 0 := by
    simp [reduced, hbaseFull]
  have hchartContinuous : ContinuousAt packet.projectiveGaugeChart 0 :=
    (packet.analyticAt_projectiveGaugeChart 0).continuousAt
  have hpreimageU : packet.projectiveGaugeChart ⁻¹' U ∈ 𝓝 0 := by
    apply hchartContinuous.preimage_mem_nhds
    simpa using hU
  have hneighborhood : W ∩ packet.projectiveGaugeChart ⁻¹' U ∈ 𝓝 0 :=
    inter_mem hW hpreimageU
  have hstrict : HasStrictFDerivAt reduced (fderiv ℝ reduced 0) 0 :=
    hreducedAnalytic.hasStrictFDerivAt
  have harc := Math.hasPositiveCoordinateAnalyticArcAt_regularLevel_of_analytic
    hstrict hreducedAnalytic hsurj direction hdirection rfl hneighborhood
  obtain ⟨arc, eta, heta, harcAnalytic, harcZero, _, harcMem⟩ := harc
  refine ⟨packet.projectiveGaugeChart ∘ arc, eta, heta, ?_, ?_, rfl, ?_⟩
  · exact (packet.analyticAt_projectiveGaugeChart (arc 0)).comp harcAnalytic
  · simp [harcZero]
  · intro t ht
    have hmem := harcMem t ht
    have hWpoint : arc t ∈ W := hmem.1.2.1
    have hUpoint : packet.projectiveGaugeChart (arc t) ∈ U := hmem.1.2.2
    have hreducedZero : reduced (arc t) = 0 := by
      rw [hmem.1.1, hbaseReduced]
    have hfullZero : packet.projectiveGaugeResidual support (arc t) = 0 :=
      (hrecover (arc t) hWpoint).mp hreducedZero
    refine ⟨⟨⟨hfullZero,
      packet.projectiveGaugeChart_leadingTotal (arc t)⟩, hUpoint⟩, ?_⟩
    simpa [Function.comp_def] using hmem.2

end QuittingChargeTangentPacket

end GameTheory
