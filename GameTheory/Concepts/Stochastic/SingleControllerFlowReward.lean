/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.SingleControllerFlowHarmonicity

/-!
# Reward compatibility of the hybrid Vrieze flow completion

On the positive occupation support, ordinary complementary slackness makes
the Vrieze bias rows tight and makes reward domination tight on every action
in the primal mixed-action support.  After normalizing the occupation flow,
zero-sumness identifies the controller's worst reward with the dual simplex
multiplier divided by state mass, and the tight bias rows identify that ratio
with the gain--bias expression `-g + P v - v`.

The closed-core Poisson correction extending this identity through transient
states is proved in the second half of this file.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {G : StochasticGame Bool} [Finite G.State]
  [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- In a zero-sum Bool game, the controller payoff at a canonical joint
action is the negative of `rewardVal`, which records the noncontroller
payoff. -/
theorem IsZeroSumBoolGame.stagePayoff_jointOf_controller_eq_neg_rewardVal
    (hzs : G.IsZeroSumBoolGame) (controller : Bool) (state : G.State)
    (controllerAction : G.Act controller)
    (opponentAction : G.Act (!controller)) :
    G.stagePayoff state
        (G.jointOf controller controllerAction opponentAction) controller =
      -G.rewardVal controller state opponentAction controllerAction := by
  unfold rewardVal
  cases controller with
  | false =>
      have hzeroSum := hzs state
        (G.jointOf false controllerAction opponentAction)
      simp only [Bool.not_false] at hzeroSum ⊢
      linarith
  | true =>
      simpa only [Bool.not_true] using
        hzs state (G.jointOf true controllerAction opponentAction)

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- Updating the controller coordinate of an arbitrary Bool joint action
produces the corresponding canonical `jointOf` action. -/
theorem update_controller_eq_jointOf
    (controller : Bool) (action : G.Act controller) (joint : G.JointAct) :
    Function.update joint controller action =
      G.jointOf controller action (joint (!controller)) := by
  apply G.jointAct_ext_of_agree_controller_not controller
  · rw [Function.update_self, G.jointOf_apply_controller]
  · rw [Function.update_of_ne (Ne.symm (controller_ne_not controller)),
      G.jointOf_apply_not]

/-- Ordinary zero-gap complementary slackness is enough to average the
original encoded primal bias rows against normalized positive dual
occupation mass.  No strict-complementarity assumption is needed. -/
theorem normalized_vriezeDualZ_bias_eq_of_gap_zero
    {controller : Bool}
    {x : G.State → PMF (G.Act (!controller))}
    {g v : G.State → ℝ}
    {w : VriezeRow G controller → ℝ}
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
    (state : G.State)
    (hstate : G.vriezeOccupationSupport controller
      (G.vriezeDualZ controller w) state) :
    (∑ action,
        (G.vriezeDualZ controller w state action /
          ∑ candidate, G.vriezeDualZ controller w state candidate) *
          ((∑ opponentAction,
              ((x state) opponentAction).toReal *
                G.rewardVal controller state opponentAction action) +
            ∑ destination,
              G.transProb controller state action destination *
                v destination)) =
      g state + v state := by
  classical
  have hzNonneg : ∀ action,
      0 ≤ G.vriezeDualZ controller w state action :=
    fun action => hdual.1 (Sum.inr (Sum.inl (state, action)))
  have hbiasTight : ∀ action,
      0 < G.vriezeDualZ controller w state action →
      (∑ opponentAction,
          ((x state) opponentAction).toReal *
            G.rewardVal controller state opponentAction action) +
        (∑ destination,
          G.transProb controller state action destination *
            v destination) =
        g state + v state := by
    intro action hzPositive
    have hrowPositive :
        0 < w (Sum.inr (Sum.inl (state, action))) := by
      simpa only [vriezeDualZ] using hzPositive
    have hslack :=
      Math.LinearProgramming.minPrimalSlack_eq_zero_of_dual_pos
        hprimal hdual hgap hrowPositive
    rw [Math.LinearProgramming.minPrimalSlack,
      G.rowEval_vriezeA_vriezeEncode_bias] at hslack
    simp only [vriezeB, sub_zero] at hslack
    linarith
  calc
    _ = ∑ action,
        (G.vriezeDualZ controller w state action /
          ∑ candidate, G.vriezeDualZ controller w state candidate) *
          (g state + v state) := by
      apply Finset.sum_congr rfl
      intro action _
      by_cases hzZero : G.vriezeDualZ controller w state action = 0
      · simp [hzZero]
      · rw [hbiasTight action
          (lt_of_le_of_ne (hzNonneg action) (Ne.symm hzZero))]
    _ = (∑ action,
          G.vriezeDualZ controller w state action /
            ∑ candidate, G.vriezeDualZ controller w state candidate) *
          (g state + v state) := by
      rw [Finset.sum_mul]
    _ = g state + v state := by
      rw [← Finset.sum_div, div_self hstate.ne', one_mul]

/-- On occupied states, the controller's worst reward is exactly the dual
simplex multiplier divided by the positive occupation mass. -/
theorem worstReward_eq_vriezeDualLam_div_on_occupationSupport
    {controller : Bool}
    {x : G.State → PMF (G.Act (!controller))}
    {g v : G.State → ℝ}
    {w : VriezeRow G controller → ℝ}
    {tau : G.State → PMF (G.Act controller)}
    (hzs : G.IsZeroSumBoolGame)
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
      (G.vriezeDualYGain controller w) tau)
    (state : G.State)
    (hstate : G.vriezeOccupationSupport controller
      (G.vriezeDualZ controller w) state) :
    G.worstReward controller tau state =
      G.vriezeDualLam controller w state /
        ∑ action, G.vriezeDualZ controller w state action := by
  classical
  let z := G.vriezeDualZ controller w
  let lam := G.vriezeDualLam controller w
  let mass : ℝ := ∑ action, z state action
  have hnamedDual :=
    G.isVriezeDualFeasible_vriezeDualZ_vriezeDualYGain hdual
  have hcontrollerExpected : ∀ opponentAction : G.Act (!controller),
      expect (tau state) (fun action =>
        G.stagePayoff state
          (G.jointOf controller action opponentAction) controller) =
        -(∑ action, z state action *
            G.rewardVal controller state opponentAction action) / mass := by
    intro opponentAction
    rw [expect_eq_sum]
    simp_rw [hzs.stagePayoff_jointOf_controller_eq_neg_rewardVal]
    rw [show
        (∑ action,
          ((tau state) action).toReal *
            -G.rewardVal controller state opponentAction action) =
          ∑ action,
            (z state action / mass) *
              -G.rewardVal controller state opponentAction action by
      apply Finset.sum_congr rfl
      intro action _
      rw [completion.normalized_z_on_support state hstate action]]
    calc
      ∑ action,
          (z state action / mass) *
            -G.rewardVal controller state opponentAction action =
          ∑ action,
            (-(z state action *
              G.rewardVal controller state opponentAction action)) /
                mass := by
        apply Finset.sum_congr rfl
        intro action _
        ring
      _ = (∑ action,
          -(z state action *
            G.rewardVal controller state opponentAction action)) /
              mass := by
        rw [Finset.sum_div]
      _ = -(∑ action, z state action *
          G.rewardVal controller state opponentAction action) / mass := by
        rw [Finset.sum_neg_distrib]
  apply le_antisymm
  · obtain ⟨opponentAction, hopponentSupport⟩ :=
      (x state).support_nonempty
    have hxPositive : 0 < ((x state) opponentAction).toReal :=
      ENNReal.toReal_pos
        ((PMF.mem_support_iff _ _).mp hopponentSupport)
        (PMF.apply_ne_top _ _)
    let controllerAction : G.Act controller := Classical.choice inferInstance
    let joint := G.jointOf controller controllerAction opponentAction
    have hworst := G.worstReward_le tau state joint
    have hjoint : (fun action =>
        G.stagePayoff state
          (Function.update joint controller action) controller) =
        fun action => G.stagePayoff state
          (G.jointOf controller action opponentAction) controller := by
      funext action
      rw [G.update_controller_eq_jointOf]
      simp only [joint, G.jointOf_apply_not]
    rw [hjoint, hcontrollerExpected opponentAction] at hworst
    have hrewardTight :=
      G.reward_domination_eq_of_vriezePrimalDual_gap_zero
        x g v w hprimal hdual hgap state opponentAction hxPositive
    dsimp only [z, lam, mass] at hworst ⊢
    rw [show
        -(∑ action,
            G.vriezeDualZ controller w state action *
              G.rewardVal controller state opponentAction action) =
          G.vriezeDualLam controller w state by
      linarith] at hworst
    exact hworst
  · apply G.le_worstReward tau state
    intro joint
    have hjoint : (fun action =>
        G.stagePayoff state
          (Function.update joint controller action) controller) =
        fun action => G.stagePayoff state
          (G.jointOf controller action (joint (!controller))) controller := by
      funext action
      rw [G.update_controller_eq_jointOf]
    rw [hjoint, hcontrollerExpected (joint (!controller))]
    have hdomination :=
      hnamedDual.reward_domination state (joint (!controller))
    dsimp only [z, lam, mass] at hdomination ⊢
    exact (div_le_div_iff_of_pos_right hstate).2 (by linarith)

/-- On occupied states, the normalized dual simplex multiplier is the
controller gain plus the one-step drift of the original primal bias. -/
theorem vriezeDualLam_div_eq_neg_gain_add_kernelBias_on_occupationSupport
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
      (G.vriezeDualYGain controller w) tau)
    (state : G.State)
    (hstate : G.vriezeOccupationSupport controller
      (G.vriezeDualZ controller w) state) :
    G.vriezeDualLam controller w state /
        (∑ action, G.vriezeDualZ controller w state action) =
      -g state +
        expect (G.controllerKernel controller tau state) v - v state := by
  classical
  let z := G.vriezeDualZ controller w
  let lam := G.vriezeDualLam controller w
  let mass : ℝ := ∑ action, z state action
  have hnormalizedBias :=
    G.normalized_vriezeDualZ_bias_eq_of_gap_zero
      hprimal hdual hgap state hstate
  have havgReward :
      (∑ action,
        (z state action / mass) *
          (∑ opponentAction,
            ((x state) opponentAction).toReal *
              G.rewardVal controller state opponentAction action)) =
        -(lam state) / mass := by
    calc
      _ = ∑ action, ∑ opponentAction,
          ((x state) opponentAction).toReal *
            ((z state action *
              G.rewardVal controller state opponentAction action) /
                mass) := by
        apply Finset.sum_congr rfl
        intro action _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro opponentAction _
        ring
      _ = ∑ opponentAction, ∑ action,
          ((x state) opponentAction).toReal *
            ((z state action *
              G.rewardVal controller state opponentAction action) /
                mass) := Finset.sum_comm
      _ = ∑ opponentAction,
          ((x state) opponentAction).toReal *
            ((∑ action, z state action *
              G.rewardVal controller state opponentAction action) /
                mass) := by
        apply Finset.sum_congr rfl
        intro opponentAction _
        rw [← Finset.mul_sum, Finset.sum_div]
      _ = ∑ opponentAction,
          ((x state) opponentAction).toReal *
            (-(lam state) / mass) := by
        apply Finset.sum_congr rfl
        intro opponentAction _
        by_cases hxZero : ((x state) opponentAction).toReal = 0
        · simp [hxZero]
        · have hxPositive :
              0 < ((x state) opponentAction).toReal :=
            lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hxZero)
          have hrewardTight :=
            G.reward_domination_eq_of_vriezePrimalDual_gap_zero
              x g v w hprimal hdual hgap state opponentAction hxPositive
          rw [show
              (∑ action,
                G.vriezeDualZ controller w state action *
                  G.rewardVal controller state opponentAction action) =
                -G.vriezeDualLam controller w state by
            linarith]
      _ = -(lam state) / mass := by
        rw [← Finset.sum_mul, pmf_toReal_sum_one]
        ring
  have hkernelBias :
      (∑ action,
        (z state action / mass) *
          (∑ destination,
            G.transProb controller state action destination *
              v destination)) =
        expect (G.controllerKernel controller tau state) v := by
    rw [show
        expect (G.controllerKernel controller tau state) v =
          ∑ action,
            ((tau state) action).toReal *
              (∑ destination,
                G.transProb controller state action destination *
                  v destination) by
      unfold controllerKernel
      rw [expect_bind, expect_eq_sum]
      apply Finset.sum_congr rfl
      intro action _
      rw [expect_eq_sum]
      rfl]
    apply Finset.sum_congr rfl
    intro action _
    rw [completion.normalized_z_on_support state hstate action]
  have hsplit :
      (∑ action,
        (z state action / mass) *
          ((∑ opponentAction,
              ((x state) opponentAction).toReal *
                G.rewardVal controller state opponentAction action) +
            ∑ destination,
              G.transProb controller state action destination *
                v destination)) =
        (∑ action,
          (z state action / mass) *
            (∑ opponentAction,
              ((x state) opponentAction).toReal *
                G.rewardVal controller state opponentAction action)) +
          ∑ action,
            (z state action / mass) *
              (∑ destination,
                G.transProb controller state action destination *
                  v destination) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro action _
    ring
  dsimp only [z, lam, mass] at hnormalizedBias hsplit havgReward hkernelBias ⊢
  rw [hsplit, havgReward, hkernelBias] at hnormalizedBias
  rw [neg_div] at hnormalizedBias
  linarith

/-- Combining the two occupied-state identities gives exact reward--bias
compatibility on the closed occupation core. -/
theorem worstReward_eq_neg_gain_add_kernelBias_on_occupationSupport
    {controller : Bool}
    {x : G.State → PMF (G.Act (!controller))}
    {g v : G.State → ℝ}
    {w : VriezeRow G controller → ℝ}
    {tau : G.State → PMF (G.Act controller)}
    (hzs : G.IsZeroSumBoolGame)
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
      (G.vriezeDualYGain controller w) tau)
    (state : G.State)
    (hstate : G.vriezeOccupationSupport controller
      (G.vriezeDualZ controller w) state) :
    G.worstReward controller tau state =
      -g state +
        expect (G.controllerKernel controller tau state) v - v state := by
  rw [G.worstReward_eq_vriezeDualLam_div_on_occupationSupport
      hzs hprimal hdual hgap completion state hstate,
    G.vriezeDualLam_div_eq_neg_gain_add_kernelBias_on_occupationSupport
      hprimal hdual hgap completion state hstate]

/-- Closed-core reachability extends occupied-core reward compatibility
through every transient state.  Consequently the mean-ergodic projection
of the hybrid policy's worst reward is exactly the controller gain `-g`. -/
theorem ergodicProjection_worstReward_eq_neg_gain_of_flowCompletion
    [Nonempty G.State]
    {controller : Bool}
    {x : G.State → PMF (G.Act (!controller))}
    {g v : G.State → ℝ}
    {w : VriezeRow G controller → ℝ}
    {tau : G.State → PMF (G.Act controller)}
    (hzs : G.IsZeroSumBoolGame)
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
    ergodicProjection (G.controllerKernel controller tau)
        (G.worstReward controller tau) =
      fun state => -(g state) := by
  classical
  let kernel : G.State → PMF G.State :=
    G.controllerKernel controller tau
  let core : Set G.State :=
    {state | G.vriezeOccupationSupport controller
      (G.vriezeDualZ controller w) state}
  let rho : G.State → ℝ := fun state => -(g state)
  let reward : G.State → ℝ := G.worstReward controller tau
  let residual : G.State → ℝ := fun state =>
    reward state -
      (rho state + (expect (kernel state) v - v state))
  have hresidualCore : residual ∈ coreVanishingSubmodule core := by
    intro state hstate
    dsimp only [residual, reward, rho, kernel, core]
    rw [G.worstReward_eq_neg_gain_add_kernelBias_on_occupationSupport
      hzs hprimal hdual hgap completion state hstate]
    ring
  let charge : coreVanishingSubmodule core :=
    ⟨residual, hresidualCore⟩
  let certificate : ClosedCoreTransienceCertificate kernel core :=
    Classical.choice completion.exists_closedCoreTransienceCertificate
  obtain ⟨correction, hcorrection⟩ :=
    exists_coreVanishing_poissonPotential_for
      completion.occupationSupport_closed
      certificate.minorization_pos
      certificate.minorization_le_one
      certificate.uniform_reach charge
  have hcorrectionPoisson : ∀ state,
      (correction : G.State → ℝ) state -
          expect (kernel state) correction = residual state := by
    intro state
    have hpoint := congrFun (congrArg Subtype.val hcorrection) state
    change
      (correction : G.State → ℝ) state -
          (killedMarkovOperator kernel core
            completion.occupationSupport_closed correction :
              G.State → ℝ) state =
        residual state at hpoint
    simpa only [killedMarkovOperator_apply, charge] using hpoint
  let adjustedBias : G.State → ℝ := fun state =>
    v state - (correction : G.State → ℝ) state
  have hrhoHarmonic : ∀ state,
      expect (kernel state) rho = rho state := by
    intro state
    simpa only [kernel, rho] using
      G.neg_vriezeGain_harmonic_of_flowCompletion
        hprimal hdual hgap completion state
  have hrewardDecomposition : ∀ state,
      reward state = rho state +
        (expect (kernel state) adjustedBias - adjustedBias state) := by
    intro state
    have hexpectSub :
        expect (kernel state) adjustedBias =
          expect (kernel state) v - expect (kernel state) correction := by
      simpa only [adjustedBias] using
        expect_sub (kernel state) v (correction : G.State → ℝ)
    rw [hexpectSub]
    dsimp only [residual] at hcorrectionPoisson
    dsimp only [adjustedBias]
    linarith [hcorrectionPoisson state]
  have hunique :=
    Math.MeanErgodic.harmonic_eq_of_add_poisson_eq
      kernel reward rho adjustedBias
      (ergodicProjection kernel reward)
      (ergodicPoissonPotential kernel reward)
      hrhoHarmonic hrewardDecomposition
      (ergodicProjection_harmonic kernel reward)
      (eq_ergodicProjection_add_poisson kernel reward)
  simpa only [kernel, reward, rho] using hunique.symm

end StochasticGame
end GameTheory
