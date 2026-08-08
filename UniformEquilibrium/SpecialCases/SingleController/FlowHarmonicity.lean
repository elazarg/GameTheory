/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.SpecialCases.SingleController.FlowCompletion
import Math.Probability.StationaryNonnegativeDrift

/-!
# Gain harmonicity of the hybrid Vrieze flow completion

This file uses the ordinary zero-gap primal--dual pair tied to the original
encoded Vrieze primal point.  On zero-occupation states the hybrid policy is
normalized `yGain`; positive `yGain` rows are tight by complementary
slackness.  On positive-occupation states, primal gain feasibility gives a
nonnegative kernel drift and the stationary positive `z` state mass forces
that drift to vanish pointwise.

Thus the same hybrid policy already used for closed-core reachability makes
the original gain `g` harmonic, and hence makes the controller gain `-g`
harmonic as well.  Reward/projection compatibility is intentionally left to
a separate layer.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {G : StochasticGame Bool} [Finite G.State]
  [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]

/-- For an ordinary zero-gap Vrieze primal--dual pair, any hybrid flow
completion makes the original encoded gain harmonic. -/
theorem vriezeGain_harmonic_of_flowCompletion
    {controller : Bool}
    {x : G.State → PMF (G.Act (!controller))}
    {g v : G.State → ℝ}
    {w : VriezeRow G controller → ℝ}
    {tau : G.State → PMF (G.Act controller)}
    (hprimal : Math.LinearProgramming.MinPrimalFeasible
      (G.vriezeA controller) (G.vriezeB controller)
        (G.vriezeEncode controller x g v))
    (hdual : Math.LinearProgramming.MaxDualFeasible
      (G.vriezeA controller) (G.vriezeC controller) w)
    (hgap :
      Math.LinearProgramming.minPrimalValue (G.vriezeC controller)
          (G.vriezeEncode controller x g v) =
        Math.LinearProgramming.maxDualValue
          (G.vriezeB controller) w)
    (completion : G.IsVriezeFlowCompletion controller
      (G.vriezeDualZ controller w)
      (G.vriezeDualYGain controller w) tau) :
    ∀ state,
      expect (G.controllerKernel controller tau state) g = g state := by
  classical
  let z : G.State → G.Act controller → ℝ :=
    G.vriezeDualZ controller w
  let yGain : G.State → G.Act controller → ℝ :=
    G.vriezeDualYGain controller w
  let kernel : G.State → PMF G.State :=
    G.controllerKernel controller tau
  have hnamedDual : G.IsVriezeDualFeasible controller z yGain
      (G.vriezeDualLam controller w) :=
    G.isVriezeDualFeasible_vriezeDualZ_vriezeDualYGain hdual
  have hgainSlack_nonneg : ∀ state
      (action : G.Act controller),
      0 ≤ (∑ destination,
          G.transProb controller state action destination *
            g destination) - g state := by
    intro state action
    have hrow := hprimal.2 (Sum.inl (state, action))
    rw [G.rowEval_vriezeA_vriezeEncode_gain] at hrow
    simpa only [vriezeB] using hrow
  have hgainSlack_zero_of_yGain_pos : ∀ state
      (action : G.Act controller),
      0 < yGain state action →
      (∑ destination,
          G.transProb controller state action destination *
            g destination) - g state = 0 := by
    intro state action hyPositive
    have hrowPositive :
        0 < w (Sum.inl (state, action)) := by
      simpa only [yGain, vriezeDualYGain] using hyPositive
    have hslack :=
      Math.LinearProgramming.minPrimalSlack_eq_zero_of_dual_pos
        hprimal hdual hgap hrowPositive
    rw [Math.LinearProgramming.minPrimalSlack,
      G.rowEval_vriezeA_vriezeEncode_gain] at hslack
    simpa only [vriezeB, sub_zero] using hslack
  have hkernelDrift_expand : ∀ state,
      kernelDrift kernel g state =
        ∑ action,
          ((tau state) action).toReal *
            ((∑ destination,
                G.transProb controller state action destination *
                  g destination) - g state) := by
    intro state
    have htauMass :
        (∑ action, ((tau state) action).toReal) = 1 :=
      pmf_toReal_sum_one (tau state)
    dsimp only [kernelDrift, kernel]
    rw [expect_eq_sum]
    simp_rw [G.controllerKernel_apply_toReal_eq_sum]
    have hexpect :
        (∑ destination,
            (∑ action,
              ((tau state) action).toReal *
                G.transProb controller state action destination) *
              g destination) =
          ∑ action,
            ((tau state) action).toReal *
              (∑ destination,
                G.transProb controller state action destination *
                  g destination) := by
      calc
        ∑ destination,
            (∑ action,
              ((tau state) action).toReal *
                G.transProb controller state action destination) *
              g destination =
            ∑ destination, ∑ action,
              ((tau state) action).toReal *
                G.transProb controller state action destination *
                  g destination := by
          apply Finset.sum_congr rfl
          intro destination _
          rw [Finset.sum_mul]
        _ = ∑ action, ∑ destination,
            ((tau state) action).toReal *
              G.transProb controller state action destination *
                g destination := Finset.sum_comm
        _ = ∑ action,
            ((tau state) action).toReal *
              (∑ destination,
                G.transProb controller state action destination *
                  g destination) := by
          apply Finset.sum_congr rfl
          intro action _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro destination _
          ring
    rw [hexpect]
    calc
      (∑ action,
          ((tau state) action).toReal *
            (∑ destination,
              G.transProb controller state action destination *
                g destination)) - g state =
          (∑ action,
            ((tau state) action).toReal *
              (∑ destination,
                G.transProb controller state action destination *
                  g destination)) -
            ∑ action, ((tau state) action).toReal * g state := by
        rw [← Finset.sum_mul, htauMass, one_mul]
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro action _
        ring
  have hdrift_nonneg : ∀ state,
      0 ≤ kernelDrift kernel g state := by
    intro state
    rw [hkernelDrift_expand state]
    exact Finset.sum_nonneg fun action _ =>
      mul_nonneg ENNReal.toReal_nonneg
        (hgainSlack_nonneg state action)
  have hstationary : ∀ destination,
      (∑ source,
        (∑ action, z source action) *
          (kernel source destination).toReal) =
        ∑ action, z destination action := by
    exact G.vriezeStateMass_stationary_of_normalized_z
      hnamedDual tau completion.normalized_z_on_support
  intro state
  by_cases hstate : G.vriezeOccupationSupport controller z state
  · have hzero := kernelDrift_eq_zero_of_stationary_weight_pos
      kernel (fun source => ∑ action, z source action) g
      (fun source => Finset.sum_nonneg fun action _ =>
        hnamedDual.z_nonneg source action)
      hstationary hdrift_nonneg state hstate
    exact sub_eq_zero.mp hzero
  · have hterms_zero : ∀ action : G.Act controller,
        ((tau state) action).toReal *
          ((∑ destination,
              G.transProb controller state action destination *
                g destination) - g state) = 0 := by
      intro action
      by_cases hyZero : yGain state action = 0
      · have hyZero' :
            G.vriezeDualYGain controller w state action = 0 := by
          simpa only [yGain] using hyZero
        rw [completion.normalized_yGain_off_support state hstate action,
          hyZero', zero_div, zero_mul]
      · have hyPositive : 0 < yGain state action :=
          lt_of_le_of_ne
            (hnamedDual.yGain_nonneg state action)
            (Ne.symm hyZero)
        rw [hgainSlack_zero_of_yGain_pos state action hyPositive,
          mul_zero]
    have hzero : kernelDrift kernel g state = 0 := by
      rw [hkernelDrift_expand state]
      exact Finset.sum_eq_zero fun action _ => hterms_zero action
    exact sub_eq_zero.mp hzero

/-- Negating the harmonic Vrieze gain gives the controller's harmonic gain. -/
theorem neg_vriezeGain_harmonic_of_flowCompletion
    {controller : Bool}
    {x : G.State → PMF (G.Act (!controller))}
    {g v : G.State → ℝ}
    {w : VriezeRow G controller → ℝ}
    {tau : G.State → PMF (G.Act controller)}
    (hprimal : Math.LinearProgramming.MinPrimalFeasible
      (G.vriezeA controller) (G.vriezeB controller)
        (G.vriezeEncode controller x g v))
    (hdual : Math.LinearProgramming.MaxDualFeasible
      (G.vriezeA controller) (G.vriezeC controller) w)
    (hgap :
      Math.LinearProgramming.minPrimalValue (G.vriezeC controller)
          (G.vriezeEncode controller x g v) =
        Math.LinearProgramming.maxDualValue
          (G.vriezeB controller) w)
    (completion : G.IsVriezeFlowCompletion controller
      (G.vriezeDualZ controller w)
      (G.vriezeDualYGain controller w) tau) :
    ∀ state,
      expect (G.controllerKernel controller tau state)
          (fun next => -(g next)) = -(g state) := by
  intro state
  have hneg :
      expect (G.controllerKernel controller tau state)
          (fun next => -(g next)) =
        -(expect (G.controllerKernel controller tau state) g) := by
    simpa using
      expect_const_mul
        (G.controllerKernel controller tau state) (-1 : ℝ) g
  rw [hneg, G.vriezeGain_harmonic_of_flowCompletion
    hprimal hdual hgap completion state]

/-- Primal optimality supplies an ordinary dual and one hybrid completion
under which the original gain is harmonic. -/
theorem exists_vriezeFlowCompletion_harmonic_of_primalOptimal
    {controller : Bool} (hSC : G.IsSingleController controller)
    {x : G.State → PMF (G.Act (!controller))}
    {g v : G.State → ℝ}
    (hopt : G.IsVriezePrimalOptimal controller x g v) :
    ∃ (w : VriezeRow G controller → ℝ)
        (tau : G.State → PMF (G.Act controller)),
      Math.LinearProgramming.MaxDualFeasible
          (G.vriezeA controller) (G.vriezeC controller) w ∧
        G.IsVriezeFlowCompletion controller
          (G.vriezeDualZ controller w)
          (G.vriezeDualYGain controller w) tau ∧
        ∀ state,
          expect (G.controllerKernel controller tau state) g = g state := by
  have hprimal :=
    G.minPrimalFeasible_vriezeEncode_of_isVriezePrimalFeasible
      hSC hopt.feasible
  obtain ⟨w, hdual, hdualValue⟩ :=
    G.exists_vriezeMaxDualFeasible_of_vriezePrimalOptimal hSC hopt
  have hgap :
      Math.LinearProgramming.minPrimalValue (G.vriezeC controller)
          (G.vriezeEncode controller x g v) =
        Math.LinearProgramming.maxDualValue
          (G.vriezeB controller) w := by
    calc
      _ = -(∑ state, g state) := by
        rw [G.minPrimalValue_vriezeC_eq,
          G.vriezeDecodeG_vriezeEncode]
      _ = _ := hdualValue.symm
  let namedDual :=
    G.isVriezeDualFeasible_vriezeDualZ_vriezeDualYGain hdual
  obtain ⟨tau, completion⟩ :=
    G.exists_vriezeFlowCompletion_of_dualFeasible namedDual
  exact ⟨w, tau, hdual, completion,
    G.vriezeGain_harmonic_of_flowCompletion
      hprimal hdual hgap completion⟩

end StochasticGame
end GameTheory
