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

/-- The exact continuation-effect target that offsets the current gain from
a nontrivial pure deviation at discount factor `delta`. -/
def pureDeviationEnforcementTarget
    [DecidableEq iota]
    (G : KernelGame iota) (delta : ℝ) (a : Profile G) (who : iota)
    (dev : NontrivialDeviation a who) : ℝ :=
  -((1 - delta) / delta) *
    (G.eu (Function.update a who dev.1) who - G.eu a who)

/-- Pairwise full rank at a pure profile enforces that profile on every
non-coordinate normal hyperplane.  Only the action carriers and public signal
type need finite enumerations; no outcome-space finiteness is used. -/
theorem PurePairwiseFullRankAtProfile.isEnforceableOnNormalHyperplane
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) [Finite M.Signal]
    [∀ who, Finite (G.Strategy who)]
    {delta : ℝ} (hdelta : 0 < delta) (a : Profile G)
    (h : M.mixedExtension.PurePairwiseFullRankAtProfile a)
    (normal : Payoff iota)
    (hnormal : Math.LinearAlgebra.HasTwoNonzeroCoordinates normal) :
    M.IsEnforceableOnNormalHyperplane delta a normal := by
  letI := Fintype.ofFinite M.Signal
  obtain ⟨w, htangent, heffect⟩ :=
    h.exists_tangentIncentiveTransfer hnormal
      (fun who => pureDeviationEnforcementTarget G delta a who)
  refine ⟨w, htangent, ?_⟩
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
