/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Repeated.MonitoringIncentives
import GameTheory.Concepts.Repeated.MonitoringPureDeviations

/-!
# Hyperplane Enforcement under Public Monitoring

This file connects the FLM rank linear algebra to APS enforceability.  A
profile is enforceable on a normal hyperplane when all public continuation
payoffs lie in that hyperplane and deter every unilateral stage deviation.
-/

noncomputable section

namespace GameTheory
namespace KernelGame
namespace PublicMonitoring

open Math.Probability

variable {iota : Type} {G : KernelGame iota}

/-- A stage profile is enforceable on the linear hyperplane tangent to
`normal` when one enforcing continuation assignment lies pointwise in that
hyperplane. -/
def IsEnforceableOnNormalHyperplane
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) (delta : ℝ) (a : Profile G)
    (normal : Payoff iota) : Prop :=
  ∃ w : M.ContinuationAssignment,
    (∀ y, w y ∈ Math.LinearAlgebra.normalHyperplane normal) ∧
      M.IsEnforceable delta a w

/-- Enforceability with all public continuation payoffs in an affine level
set of a normal functional. -/
def IsEnforceableOnAffineNormalHyperplane
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) (delta : ℝ) (a : Profile G)
    (normal : Payoff iota) (level : ℝ) : Prop :=
  ∃ w : M.ContinuationAssignment,
    (∀ y, w y ∈ Math.LinearAlgebra.normalAffineHyperplane normal level) ∧
      M.IsEnforceable delta a w

/-- For a nonzero normal, enforceability on its linear hyperplane is
equivalent to enforceability on every affine translate. -/
theorem isEnforceableOnAffineNormalHyperplane_iff
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) [Finite M.Signal]
    (delta : ℝ) (a : Profile G) (normal : Payoff iota)
    (hnormal : normal ≠ 0) (level : ℝ) :
    M.IsEnforceableOnAffineNormalHyperplane delta a normal level ↔
      M.IsEnforceableOnNormalHyperplane delta a normal := by
  obtain ⟨center, hcenter⟩ :=
    Math.LinearAlgebra.normalLinearMap_surjective_of_ne_zero hnormal level
  constructor
  · rintro ⟨w, haffine, henforce⟩
    refine ⟨M.translateContinuation w (-center), ?_,
      (M.isEnforceable_translateContinuation_iff delta a w (-center)).2
        henforce⟩
    intro y
    change Math.LinearAlgebra.normalLinearMap normal
      (w y + (-center)) = 0
    rw [map_add, map_neg, hcenter]
    have hy := haffine y
    change Math.LinearAlgebra.normalLinearMap normal (w y) = level at hy
    rw [hy]
    ring
  · rintro ⟨w, hlinear, henforce⟩
    refine ⟨M.translateContinuation w center, ?_,
      (M.isEnforceable_translateContinuation_iff delta a w center).2
        henforce⟩
    intro y
    change Math.LinearAlgebra.normalLinearMap normal (w y + center) = level
    rw [map_add, hcenter]
    have hy := hlinear y
    change Math.LinearAlgebra.normalLinearMap normal (w y) = 0 at hy
    rw [hy, zero_add]

/-- Under bounded utilities and finite public signals, hyperplane
enforceability of a pure profile is equivalent before and after behavioral
lifting. -/
theorem isEnforceableOnNormalHyperplane_mixedExtension_iff_of_bounded
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) [Finite M.Signal]
    (delta : ℝ) (a : Profile G) (normal : Payoff iota)
    (hu : ∀ who, ∃ C, ∀ omega, |G.utility omega who| ≤ C) :
    M.mixedExtension.IsEnforceableOnNormalHyperplane delta
        (G.pureMixedProfile a) normal ↔
      M.IsEnforceableOnNormalHyperplane delta a normal := by
  constructor
  · rintro ⟨w, htangent, henforce⟩
    refine ⟨w, htangent, ?_⟩
    exact (M.isEnforceable_mixedExtension_pureMixedProfile_iff_of_bounded
      delta a w hu (M.isBoundedContinuationAssignment_of_finite w)).1 henforce
  · rintro ⟨w, htangent, henforce⟩
    refine ⟨w, htangent, ?_⟩
    exact (M.isEnforceable_mixedExtension_pureMixedProfile_iff_of_bounded
      delta a w hu (M.isBoundedContinuationAssignment_of_finite w)).2 henforce

/-- Finite outcomes discharge utility boundedness in the behavioral-lifting
equivalence for hyperplane enforceability. -/
theorem isEnforceableOnNormalHyperplane_mixedExtension_iff
    [Fintype iota] [DecidableEq iota] [Finite G.Outcome]
    (M : G.PublicMonitoring) [Finite M.Signal]
    (delta : ℝ) (a : Profile G) (normal : Payoff iota) :
    M.mixedExtension.IsEnforceableOnNormalHyperplane delta
        (G.pureMixedProfile a) normal ↔
      M.IsEnforceableOnNormalHyperplane delta a normal := by
  apply M.isEnforceableOnNormalHyperplane_mixedExtension_iff_of_bounded
  intro who
  exact Math.Probability.exists_abs_bound_of_finite
    (fun omega => G.utility omega who)

/-- For finite public signals, the pure-deviation incentive-effect map is the
difference between expected continuation transfers after deviating and after
following the prescribed pure action. -/
theorem pureIndividualIncentiveEffectMap_mixedExtension_eq_expect_sub
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) [Fintype M.Signal]
    (a : Profile G) (who : iota) (z : M.Signal → ℝ)
    (dev : NontrivialDeviation a who) :
    M.mixedExtension.pureIndividualIncentiveEffectMap a who z dev =
      expect (M.signalKernel (Function.update a who dev.1)) z -
        expect (M.signalKernel a) z := by
  rw [M.mixedExtension.pureIndividualIncentiveEffectMap_apply,
    expect_eq_sum, expect_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  simp only [pureDeviationSignalMatrix, deviationSignalVector]
  rw [← G.pureMixedProfile_update]
  simp only [Math.PMFProduct.pmfPi_pure, PMF.pure_bind]
  ring

/-- Current one-period payoff gains from nontrivial pure deviations. -/
def pureDeviationGainVector
    [DecidableEq iota]
    (G : KernelGame iota) (a : Profile G) :
    (who : iota) → NontrivialDeviation a who → ℝ :=
  fun who dev =>
    G.eu (Function.update a who dev.1) who - G.eu a who

/-- The exact continuation-effect target that offsets the current gain from
a nontrivial pure deviation at discount factor `delta`. -/
def pureDeviationEnforcementTarget
    [DecidableEq iota]
    (G : KernelGame iota) (delta : ℝ) (a : Profile G) (who : iota)
    (dev : NontrivialDeviation a who) : ℝ :=
  -((1 - delta) / delta) *
    (G.eu (Function.update a who dev.1) who - G.eu a who)

/-- Any tangent continuation assignment whose pure-deviation effects equal
the exact enforcement targets enforces the pure stage profile.  This algebraic
bridge does not require finite action carriers. -/
theorem isEnforceable_of_pureIncentiveEffects
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) [Fintype M.Signal]
    {delta : ℝ} (hdelta : 0 < delta) (a : Profile G)
    (w : M.ContinuationAssignment)
    (heffect : ∀ who,
      M.mixedExtension.pureIndividualIncentiveEffectMap a who
          (fun y => w y who) =
        fun dev => pureDeviationEnforcementTarget G delta a who dev) :
    M.IsEnforceable delta a w := by
  intro who dev
  by_cases hdev : dev = a who
  · subst dev
    simp [decomposedDeviationPayoff, decomposedPayoff]
  · let d : NontrivialDeviation a who := ⟨dev, hdev⟩
    have hcontinuation :
        expect (M.signalKernel (Function.update a who dev))
              (fun y => w y who) -
            expect (M.signalKernel a) (fun y => w y who) =
          pureDeviationEnforcementTarget G delta a who d := by
      rw [← M.pureIndividualIncentiveEffectMap_mixedExtension_eq_expect_sub
        a who (fun y => w y who) d]
      exact congrFun (heffect who) d
    have hdeltaNe : delta ≠ 0 := ne_of_gt hdelta
    have hcancel :
        (1 - delta) *
              (G.eu (Function.update a who dev) who - G.eu a who) +
            delta *
              (expect (M.signalKernel (Function.update a who dev))
                  (fun y => w y who) -
                expect (M.signalKernel a) (fun y => w y who)) = 0 := by
      rw [hcontinuation]
      simp only [pureDeviationEnforcementTarget, d]
      field_simp [hdeltaNe]
      ring
    simp only [decomposedDeviationPayoff, decomposedPayoff]
    linarith

/-- Pairwise full rank at a pure profile enforces that profile on every
non-coordinate normal hyperplane.  Only the relevant nontrivial-deviation
types and public signal type must be finite; no outcome-space finiteness is
used. -/
theorem PurePairwiseFullRankAtProfile.isEnforceableOnNormalHyperplane
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) [Finite M.Signal]
    {delta : ℝ} (hdelta : 0 < delta) (a : Profile G)
    [∀ who, Finite (NontrivialDeviation a who)]
    (h : M.mixedExtension.PurePairwiseFullRankAtProfile a)
    (normal : Payoff iota)
    (hnormal : Math.LinearAlgebra.HasTwoNonzeroCoordinates normal) :
    M.IsEnforceableOnNormalHyperplane delta a normal := by
  letI := Fintype.ofFinite M.Signal
  obtain ⟨w, htangent, heffect⟩ :=
    h.exists_tangentIncentiveTransfer hnormal
      (fun who => pureDeviationEnforcementTarget G delta a who)
  exact ⟨w, htangent,
    M.isEnforceable_of_pureIncentiveEffects hdelta a w heffect⟩

/-- At a fixed non-coordinate normal, pairwise full rank gives affine
hyperplane enforcement with continuation displacement bounded uniformly by a
constant times `(1 - delta) / delta`.  The constant is independent of the
discount factor and of the affine center. -/
theorem PurePairwiseFullRankAtProfile.exists_smallVariation_affine_enforcement
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) [Finite M.Signal]
    (a : Profile G)
    [∀ who, Finite (NontrivialDeviation a who)]
    (h : M.mixedExtension.PurePairwiseFullRankAtProfile a)
    (normal : Payoff iota)
    (hnormal : Math.LinearAlgebra.HasTwoNonzeroCoordinates normal) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (delta : ℝ), 0 < delta → ∀ center : Payoff iota,
        ∃ w : M.ContinuationAssignment,
          (∀ y, w y ∈ Math.LinearAlgebra.normalAffineHyperplane normal
            (Math.LinearAlgebra.normalLinearMap normal center)) ∧
          M.IsEnforceable delta a w ∧
          ∀ y, ‖w y - center‖ ≤ C * |(1 - delta) / delta| := by
  letI := Fintype.ofFinite M.Signal
  letI (who : iota) : Fintype (NontrivialDeviation a who) :=
    Fintype.ofFinite (NontrivialDeviation a who)
  obtain ⟨R, CR, hCR, hR, hRbound⟩ :=
    h.exists_bounded_tangentIncentiveEffect_rightInverse hnormal
  let gain := pureDeviationGainVector G a
  refine ⟨CR * ‖gain‖, mul_nonneg hCR (norm_nonneg gain), ?_⟩
  intro delta hdelta center
  let target : (who : iota) → NontrivialDeviation a who → ℝ :=
    fun who => pureDeviationEnforcementTarget G delta a who
  let zSub := R target
  let z : M.Signal → Payoff iota := zSub.1
  let w : M.ContinuationAssignment := M.translateContinuation z center
  have hzTangent : ∀ y,
      z y ∈ Math.LinearAlgebra.normalHyperplane normal := by
    intro y
    have hzKer := zSub.2
    change M.mixedExtension.normalIncentiveTransferLinearMap normal z = 0 at hzKer
    have hy := congrFun hzKer y
    exact hy
  have htargetRealized :
      M.mixedExtension.pureTangentIncentiveEffectMapAtProfile a normal
          zSub = target := by
    calc
      M.mixedExtension.pureTangentIncentiveEffectMapAtProfile a normal zSub =
          ((M.mixedExtension.pureTangentIncentiveEffectMapAtProfile
            a normal).comp R) target := rfl
      _ = LinearMap.id target := congrArg (fun L => L target) hR
      _ = target := rfl
  have hzEffect : ∀ who,
      M.mixedExtension.pureIndividualIncentiveEffectMap a who
          (fun y => z y who) = target who := by
    intro who
    exact congrFun htargetRealized who
  have hzEnforce : M.IsEnforceable delta a z :=
    M.isEnforceable_of_pureIncentiveEffects hdelta a z hzEffect
  refine ⟨w, ?_,
    (M.isEnforceable_translateContinuation_iff delta a z center).2
      hzEnforce, ?_⟩
  · intro y
    change Math.LinearAlgebra.normalLinearMap normal (z y + center) =
      Math.LinearAlgebra.normalLinearMap normal center
    rw [map_add]
    have hy := hzTangent y
    change Math.LinearAlgebra.normalLinearMap normal (z y) = 0 at hy
    rw [hy, zero_add]
  · intro y
    have hdisplacement : (fun y => w y - center) = z := by
      funext y who
      simp [w, translateContinuation]
    refine (norm_le_pi_norm (fun y => w y - center) y).trans ?_
    rw [hdisplacement]
    have htarget : target = (-((1 - delta) / delta)) • gain := by
      funext who dev
      simp [target, gain, pureDeviationEnforcementTarget,
        pureDeviationGainVector, smul_eq_mul]
    calc
      ‖z‖ = ‖zSub‖ := rfl
      _ ≤ CR * ‖target‖ := hRbound target
      _ = CR * (‖-((1 - delta) / delta)‖ * ‖gain‖) := by
        rw [htarget, norm_smul]
      _ = (CR * ‖gain‖) * |(1 - delta) / delta| := by
        rw [Real.norm_eq_abs, abs_neg]
        ring

/-- Pairwise full rank supplies one affine-enforcement bound uniformly over
all unit-bounded non-coordinate normals whose two witnessing coordinates are
separated from zero by a common positive margin.  The witnessing pair may
vary with the normal. -/
theorem PurePairwiseFullRankAtProfile.exists_uniformlyBounded_smallVariation_affine_enforcement
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) [Finite M.Signal]
    (a : Profile G)
    [∀ who, Finite (NontrivialDeviation a who)]
    (h : M.mixedExtension.PurePairwiseFullRankAtProfile a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (normal : Payoff iota) (margin : ℝ), 0 < margin → ‖normal‖ ≤ 1 →
        Math.LinearAlgebra.HasTwoCoordinatesWithAbsAtLeast margin normal →
        ∀ (delta : ℝ), 0 < delta → ∀ center : Payoff iota,
          ∃ w : M.ContinuationAssignment,
            (∀ y, w y ∈ Math.LinearAlgebra.normalAffineHyperplane normal
              (Math.LinearAlgebra.normalLinearMap normal center)) ∧
            M.IsEnforceable delta a w ∧
            ∀ y, ‖w y - center‖ ≤
              C * margin⁻¹ * |(1 - delta) / delta| := by
  letI := Fintype.ofFinite M.Signal
  letI (who : iota) : Fintype (NontrivialDeviation a who) :=
    Fintype.ofFinite (NontrivialDeviation a who)
  obtain ⟨CR, hCR, hsolver⟩ :=
    h.exists_uniformlyBounded_tangentIncentiveTransfer
  let gain := pureDeviationGainVector G a
  refine ⟨CR * ‖gain‖, mul_nonneg hCR (norm_nonneg gain), ?_⟩
  intro normal margin hmargin hnormal hseparated delta hdelta center
  let target : (who : iota) → NontrivialDeviation a who → ℝ :=
    fun who => pureDeviationEnforcementTarget G delta a who
  let B := |(1 - delta) / delta| * ‖gain‖
  have hB : 0 ≤ B := mul_nonneg (abs_nonneg _) (norm_nonneg gain)
  have htarget : ∀ who dev, ‖target who dev‖ ≤ B := by
    intro who dev
    have hgain : ‖gain who dev‖ ≤ ‖gain‖ :=
      (norm_le_pi_norm (gain who) dev).trans (norm_le_pi_norm gain who)
    calc
      ‖target who dev‖ =
          ‖-((1 - delta) / delta)‖ * ‖gain who dev‖ := by
        change ‖-((1 - delta) / delta) * gain who dev‖ = _
        rw [norm_mul]
      _ = |(1 - delta) / delta| * ‖gain who dev‖ := by
        rw [norm_neg, Real.norm_eq_abs]
      _ ≤ |(1 - delta) / delta| * ‖gain‖ :=
        mul_le_mul_of_nonneg_left hgain (abs_nonneg _)
      _ = B := rfl
  obtain ⟨z, hzTangent, hzEffect, hzBound⟩ :=
    hsolver normal margin hmargin hnormal hseparated target B hB htarget
  let w : M.ContinuationAssignment := M.translateContinuation z center
  have hzEnforce : M.IsEnforceable delta a z :=
    M.isEnforceable_of_pureIncentiveEffects hdelta a z hzEffect
  refine ⟨w, ?_,
    (M.isEnforceable_translateContinuation_iff delta a z center).2
      hzEnforce, ?_⟩
  · intro y
    change Math.LinearAlgebra.normalLinearMap normal (z y + center) =
      Math.LinearAlgebra.normalLinearMap normal center
    rw [map_add]
    have hy := hzTangent y
    change Math.LinearAlgebra.normalLinearMap normal (z y) = 0 at hy
    rw [hy, zero_add]
  · intro y
    have hdisplacement : w y - center = z y := by
      funext who
      simp [w, translateContinuation]
    rw [hdisplacement]
    calc
      ‖z y‖ ≤ CR * margin⁻¹ * B := hzBound y
      _ = (CR * ‖gain‖) * margin⁻¹ * |(1 - delta) / delta| := by
        simp only [B]
        ring

/-- If the normal vanishes outside one player, individual full rank supplies
tangent incentives for every other player.  The distinguished player must
already be playing a stage best response because tangency fixes that player's
continuation coordinate. -/
theorem PureIndividualFullRankAtProfile.isEnforceableOnNormalHyperplane_of_bestResponse
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) [Finite M.Signal]
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (a : Profile G)
    [∀ who, Finite (NontrivialDeviation a who)]
    (h : M.mixedExtension.PureIndividualFullRankAtProfile a)
    (normal : Payoff iota) (anchor : iota)
    (hzero : ∀ who, who ≠ anchor → normal who = 0)
    (hbest : G.IsBestResponse anchor a (a anchor)) :
    M.IsEnforceableOnNormalHyperplane delta a normal := by
  letI := Fintype.ofFinite M.Signal
  obtain ⟨w, htangent, hanchorZero, heffect⟩ :=
    h.exists_coordinateTangentIncentiveTransfer normal anchor hzero
      (fun who => pureDeviationEnforcementTarget G delta a who)
  refine ⟨w, htangent, ?_⟩
  intro who dev
  by_cases hwho : who = anchor
  · subst who
    have hstage := hbest dev
    rw [Function.update_eq_self] at hstage
    have hwzero : (fun y => w y anchor) = 0 := by
      funext y
      exact hanchorZero y
    have hcontinuationDev :
        expect (M.signalKernel (Function.update a anchor dev))
          (fun y => w y anchor) = 0 := by
      rw [hwzero]
      exact expect_const _ 0
    have hcontinuationBase :
        expect (M.signalKernel a) (fun y => w y anchor) = 0 := by
      rw [hwzero]
      exact expect_const _ 0
    simp only [decomposedDeviationPayoff, decomposedPayoff]
    rw [hcontinuationDev, hcontinuationBase]
    simp only [mul_zero, add_zero]
    exact mul_le_mul_of_nonneg_left hstage (sub_nonneg.mpr hdeltaOne)
  · by_cases hdev : dev = a who
    · subst dev
      simp [decomposedDeviationPayoff, decomposedPayoff]
    · let d : NontrivialDeviation a who := ⟨dev, hdev⟩
      have hcontinuation :
          expect (M.signalKernel (Function.update a who dev))
                (fun y => w y who) -
              expect (M.signalKernel a) (fun y => w y who) =
            pureDeviationEnforcementTarget G delta a who d := by
        rw [← M.pureIndividualIncentiveEffectMap_mixedExtension_eq_expect_sub
          a who (fun y => w y who) d]
        exact congrFun (heffect who hwho) d
      have hdeltaNe : delta ≠ 0 := ne_of_gt hdelta
      have hcancel :
          (1 - delta) *
                (G.eu (Function.update a who dev) who - G.eu a who) +
              delta *
                (expect (M.signalKernel (Function.update a who dev))
                    (fun y => w y who) -
                  expect (M.signalKernel a) (fun y => w y who)) = 0 := by
        rw [hcontinuation]
        simp only [pureDeviationEnforcementTarget, d]
        field_simp [hdeltaNe]
        ring
      simp only [decomposedDeviationPayoff, decomposedPayoff]
      linarith

/-- The coordinate-normal formulation packages the distinguished coordinate
existentially and requests a stage best response wherever the normal is
nonzero. -/
theorem PureIndividualFullRankAtProfile.isEnforceableOnCoordinateNormalHyperplane
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) [Finite M.Signal]
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (a : Profile G)
    [∀ who, Finite (NontrivialDeviation a who)]
    (h : M.mixedExtension.PureIndividualFullRankAtProfile a)
    (normal : Payoff iota)
    (hcoordinate : Math.LinearAlgebra.IsCoordinateDirection normal)
    (hbest : ∀ who, normal who ≠ 0 →
      G.IsBestResponse who a (a who)) :
    M.IsEnforceableOnNormalHyperplane delta a normal := by
  obtain ⟨anchor, hanchor, hzero⟩ := hcoordinate
  exact h.isEnforceableOnNormalHyperplane_of_bestResponse M hdelta hdeltaOne
    a normal anchor hzero (hbest anchor hanchor)

/-- With finite outcomes, coordinate-normal enforcement also deters every
behavioral mixed deviation from the embedded pure profile. -/
theorem PureIndividualFullRankAtProfile.isEnforceableOnCoordinateNormalHyperplane_mixedExtension
    [Fintype iota] [DecidableEq iota] [Finite G.Outcome]
    (M : G.PublicMonitoring) [Finite M.Signal]
    [∀ who, Finite (G.Strategy who)]
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (a : Profile G)
    (h : M.mixedExtension.PureIndividualFullRankAtProfile a)
    (normal : Payoff iota)
    (hcoordinate : Math.LinearAlgebra.IsCoordinateDirection normal)
    (hbest : ∀ who, normal who ≠ 0 →
      G.IsBestResponse who a (a who)) :
    M.mixedExtension.IsEnforceableOnNormalHyperplane delta
      (G.pureMixedProfile a) normal := by
  rw [M.isEnforceableOnNormalHyperplane_mixedExtension_iff]
  exact h.isEnforceableOnCoordinateNormalHyperplane M hdelta hdeltaOne
    a normal hcoordinate hbest

/-- Under explicit utility boundedness, the same tangent continuation
assignment enforces the embedded pure profile against every behavioral mixed
deviation. -/
theorem PurePairwiseFullRankAtProfile.isEnforceableOnNormalHyperplane_mixedExtension_of_bounded
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) [Finite M.Signal]
    [∀ who, Finite (G.Strategy who)]
    {delta : ℝ} (hdelta : 0 < delta) (a : Profile G)
    (h : M.mixedExtension.PurePairwiseFullRankAtProfile a)
    (normal : Payoff iota)
    (hnormal : Math.LinearAlgebra.HasTwoNonzeroCoordinates normal)
    (hu : ∀ who, ∃ C, ∀ omega, |G.utility omega who| ≤ C) :
    M.mixedExtension.IsEnforceableOnNormalHyperplane delta
      (G.pureMixedProfile a) normal := by
  letI := Fintype.ofFinite M.Signal
  obtain ⟨w, htangent, henforce⟩ :=
    h.isEnforceableOnNormalHyperplane M hdelta a normal hnormal
  refine ⟨w, htangent, ?_⟩
  exact (M.isEnforceable_mixedExtension_pureMixedProfile_iff_of_bounded
    delta a w hu (M.isBoundedContinuationAssignment_of_finite w)).2 henforce

/-- Finite outcomes discharge the utility-boundedness hypothesis in the
behavioral mixed-deviation theorem. -/
theorem PurePairwiseFullRankAtProfile.isEnforceableOnNormalHyperplane_mixedExtension
    [Fintype iota] [DecidableEq iota]
    [Finite G.Outcome]
    (M : G.PublicMonitoring) [Finite M.Signal]
    [∀ who, Finite (G.Strategy who)]
    {delta : ℝ} (hdelta : 0 < delta) (a : Profile G)
    (h : M.mixedExtension.PurePairwiseFullRankAtProfile a)
    (normal : Payoff iota)
    (hnormal : Math.LinearAlgebra.HasTwoNonzeroCoordinates normal) :
    M.mixedExtension.IsEnforceableOnNormalHyperplane delta
      (G.pureMixedProfile a) normal := by
  letI := Fintype.ofFinite M.Signal
  apply h.isEnforceableOnNormalHyperplane_mixedExtension_of_bounded
    M hdelta a normal hnormal
  intro who
  exact Math.Probability.exists_abs_bound_of_finite
    (fun omega => G.utility omega who)

end PublicMonitoring
end KernelGame
end GameTheory
