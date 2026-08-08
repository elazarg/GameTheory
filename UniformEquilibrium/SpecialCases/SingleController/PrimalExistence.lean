/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.SpecialCases.SingleController.FlowReward

/-!
# Existence of an optimal Vrieze primal point

This file removes the final supplied-object hypothesis from the finite
zero-sum single-controller route.  A constant low gain gives a feasible
Vrieze primal point.  Every feasible gain is bounded above by a finite stage
payoff bound: its stationary average certificate gives a one-sided guarantee,
which cannot exceed that payoff bound.  The resulting lower bound on the
standard-form minimization objective feeds finite LP attainment.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {G : StochasticGame Bool} [Finite G.State]
  [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]

/-- A concrete finite bound for the absolute stage payoff of the
noncontroller. -/
def vriezeNoncontrollerPayoffBound (G : StochasticGame Bool)
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (controller : Bool) : ℝ :=
  ∑ state, ∑ joint : G.JointAct,
    |G.stagePayoff state joint (!controller)|

theorem vriezeNoncontrollerPayoffBound_nonneg
    (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] (controller : Bool) :
    0 ≤ G.vriezeNoncontrollerPayoffBound controller :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Every noncontroller stage payoff is bounded by the concrete finite sum. -/
theorem abs_stagePayoff_noncontroller_le_vriezeBound
    (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] (controller : Bool)
    (state : G.State) (joint : G.JointAct) :
    |G.stagePayoff state joint (!controller)| ≤
      G.vriezeNoncontrollerPayoffBound controller := by
  letI : Fintype G.State := Fintype.ofFinite G.State
  letI : Fintype G.JointAct := Fintype.ofFinite G.JointAct
  calc
    |G.stagePayoff state joint (!controller)| ≤
        ∑ candidate : G.JointAct,
          |G.stagePayoff state candidate (!controller)| :=
      Finset.single_le_sum
        (fun candidate _ => abs_nonneg
          (G.stagePayoff state candidate (!controller)))
        (Finset.mem_univ joint)
    _ ≤ ∑ source, ∑ candidate : G.JointAct,
          |G.stagePayoff source candidate (!controller)| :=
      Finset.single_le_sum
        (fun source _ => Finset.sum_nonneg fun candidate _ =>
          abs_nonneg (G.stagePayoff source candidate (!controller)))
        (Finset.mem_univ state)

/-- The Vrieze primal is always feasible: use an arbitrary pure
noncontroller action, zero bias, and constant gain equal to the negative
absolute payoff bound. -/
theorem exists_isVriezePrimalFeasible (G : StochasticGame Bool)
    [Finite G.State] [∀ i, Finite (G.Act i)]
    [∀ i, Nonempty (G.Act i)] (controller : Bool) :
    ∃ (x : G.State → PMF (G.Act (!controller)))
        (g v : G.State → ℝ),
      G.IsVriezePrimalFeasible controller x g v := by
  classical
  let action : G.Act (!controller) := Classical.choice inferInstance
  let x : G.State → PMF (G.Act (!controller)) := fun _ => PMF.pure action
  let g : G.State → ℝ := fun _ =>
    -(G.vriezeNoncontrollerPayoffBound controller)
  let v : G.State → ℝ := fun _ => 0
  refine ⟨x, g, v, ?_, ?_⟩
  · intro state joint
    dsimp only [g, x]
    rw [expect_pure, expect_const]
  · intro state joint
    dsimp only [g, v, x]
    rw [expect_pure, expect_const, add_zero, add_zero]
    exact neg_le_of_abs_le
      (G.abs_stagePayoff_noncontroller_le_vriezeBound controller
        state (Function.update joint (!controller) action))

/-- Any Vrieze-feasible gain is pointwise at most one plus the finite stage
payoff bound.  The harmless `+1` comes from instantiating the semantic
one-sided guarantee at accuracy `1`. -/
theorem IsVriezePrimalFeasible.gain_le_payoffBound_add_one
    {controller : Bool}
    {x : G.State → PMF (G.Act (!controller))}
    {g v : G.State → ℝ}
    (hfeasible : G.IsVriezePrimalFeasible controller x g v)
    (state : G.State) :
    g state ≤ G.vriezeNoncontrollerPayoffBound controller + 1 := by
  classical
  have hstationary :
      G.IsStationaryAverageGuaranteeCertificate
        state (!controller) (g state) :=
    G.isLowerAverageCertificate_of_vriezePrimalFeasible
      controller state x g v hfeasible
  have hguarantee :
      G.IsOneSidedGuaranteeCertificate state (!controller) (g state) :=
    G.isOneSidedGuaranteeCertificate_of_isStationaryAverageGuaranteeCertificate
      state (!controller) (g state) hstationary
  obtain ⟨strategy, horizon, -, hsecurity⟩ :=
    hguarantee 1 zero_lt_one
  let opponent : G.BehaviorProfile := fun who _ _ =>
    PMF.pure (Classical.choice (inferInstance : Nonempty (G.Act who)))
  have hlower := hsecurity opponent horizon le_rfl
  have habs := G.abs_finiteAveragePayoff_le
    (G.vriezeNoncontrollerPayoffBound_nonneg controller)
    (fun source joint =>
      G.abs_stagePayoff_noncontroller_le_vriezeBound
        controller source joint)
    state horizon (Function.update opponent (!controller) strategy)
  have hupper := (abs_le.mp habs).2
  linarith

/-- Every finite single-controller game admits a primal-optimal Vrieze
point.  Feasibility and the semantic payoff bound make the encoded finite LP
nonempty and bounded; finite LP attainment then supplies an optimizer. -/
theorem exists_isVriezePrimalOptimal
    (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (controller : Bool) (hSC : G.IsSingleController controller) :
    ∃ (x : G.State → PMF (G.Act (!controller)))
        (g v : G.State → ℝ),
      G.IsVriezePrimalOptimal controller x g v := by
  classical
  have hstandardFeasible : ∃ q,
      Math.LinearProgramming.MinPrimalFeasible
        (G.vriezeA controller) (G.vriezeB controller) q := by
    obtain ⟨x, g, v, hfeasible⟩ :=
      G.exists_isVriezePrimalFeasible controller
    exact ⟨G.vriezeEncode controller x g v,
      G.minPrimalFeasible_vriezeEncode_of_isVriezePrimalFeasible
        hSC hfeasible⟩
  have hstandardBounded : ∃ lower : ℝ, ∀ q,
      Math.LinearProgramming.MinPrimalFeasible
          (G.vriezeA controller) (G.vriezeB controller) q →
        lower ≤ Math.LinearProgramming.minPrimalValue
          (G.vriezeC controller) q := by
    let bound : ℝ :=
      G.vriezeNoncontrollerPayoffBound controller + 1
    let lower : ℝ :=
      -((Fintype.card G.State : ℝ) * bound)
    refine ⟨lower, ?_⟩
    intro q hq
    have hsemantic :=
      G.isVriezePrimalFeasible_of_minPrimalFeasible hSC hq
    have hsum :
        (∑ state, G.vriezeDecodeG controller q state) ≤
          (Fintype.card G.State : ℝ) * bound := by
      calc
        (∑ state, G.vriezeDecodeG controller q state) ≤
            ∑ _state : G.State, bound := by
          apply Finset.sum_le_sum
          intro state _
          exact hsemantic.gain_le_payoffBound_add_one state
        _ = (Fintype.card G.State : ℝ) * bound := by
          simp [nsmul_eq_mul]
    rw [G.minPrimalValue_vriezeC_eq]
    dsimp only [lower]
    linarith
  obtain ⟨q, hq, hqOptimal⟩ :=
    Math.LinearProgramming.exists_minPrimalOptimal_of_feasible_of_bounded
      hstandardFeasible hstandardBounded
  have hsemantic :=
    G.isVriezePrimalFeasible_of_minPrimalFeasible hSC hq
  refine ⟨G.vriezeDecodeX controller q,
    G.vriezeDecodeG controller q,
    G.vriezeDecodeV controller q, hsemantic, ?_⟩
  intro x' g' v' hfeasible'
  have hencoded :=
    G.minPrimalFeasible_vriezeEncode_of_isVriezePrimalFeasible
      hSC hfeasible'
  have hvalue :=
    hqOptimal (G.vriezeEncode controller x' g' v') hencoded
  rw [G.minPrimalValue_vriezeC_eq,
    G.minPrimalValue_vriezeC_eq,
    G.vriezeDecodeG_vriezeEncode] at hvalue
  linarith

/-- Unconditional finite zero-sum single-controller uniform-payoff theorem.

Existence follows more generally from Mertens and Neyman, “Stochastic Games,”
*International Journal of Game Theory* 10 (1981), 53–66,
doi:10.1007/BF01769259.  The formal proof here instead follows the specialized
undiscounted LP/single-controller route developed in O. J. Vrieze,
*Stochastic Games with Finite State and Action Spaces*, CWI Tract 33 (1987),
as described in `SingleController.lean`.  All Vrieze primal, dual,
flow-completion, harmonicity, transience, and reward-projection objects are
constructed internally. -/
theorem exists_uniformEquilibriumPayoff_of_isZeroSumBoolGame_of_isSingleController
    (G : StochasticGame Bool) [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (hzs : G.IsZeroSumBoolGame)
    {controller : Bool} (hSC : G.IsSingleController controller)
    (initialState : G.State) :
    ∃ payoff : Payoff Bool,
      G.IsUniformEquilibriumPayoff initialState payoff := by
  obtain ⟨x, g, v, hoptimal⟩ :=
    G.exists_isVriezePrimalOptimal controller hSC
  exact
    G.exists_uniformEquilibriumPayoff_of_singleController_of_vriezePrimalOptimal
      hzs hSC initialState hoptimal

end StochasticGame
end GameTheory
