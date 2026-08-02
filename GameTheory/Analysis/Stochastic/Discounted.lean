/-
# Discounted values of finite zero-sum stochastic games

At every state, the normalized Shapley operator evaluates the finite matrix

`(1 - β) * stage payoff + β * expected continuation value`.

The canonical matrix value is nonexpansive, so the operator is a
`β`-contraction in the finite-state sup metric.  Banach's theorem gives its
unique fixed point, and the matrix adapter selects stationary saddle actions
realizing the Bellman value at every state.

This module proves the value-equation and stationary one-shot statements.  It
does not introduce an infinite path law or claim optimality against arbitrary
infinite-history strategies.
-/

import GameTheory.Analysis.MatrixValue
import GameTheory.Stochastic.ZeroSum
import Mathlib.Topology.MetricSpace.Contracting

noncomputable section

namespace GameTheory.Stochastic.Game

open Probability MatrixGame
open scoped NNReal

variable (G : Game (Fin 2))

/-- The normalized auxiliary one-shot matrix at a state and continuation
value. -/
def auxiliaryMatrix (β : ℝ) (value : G.State → ℝ) (state : G.State) :
    G.Action 0 → G.Action 1 → ℝ :=
  fun row col =>
    (1 - β) * G.stageUtility state (G.pairAction row col) 0 +
      β * (G.transition state (G.pairAction row col)).expect value

/-- The auxiliary matrix's row utility is the normalized player-zero
one-step return. -/
@[simp]
theorem auxiliaryUtility_zero (β : ℝ) (value : G.State → ℝ)
    (state : G.State) (row : G.Action 0) (col : G.Action 1) :
    MatrixGame.utility (G.auxiliaryMatrix β value state) (row, col) 0 =
      (1 - β) * G.stageUtility state (G.pairAction row col) 0 +
        β * (G.transition state (G.pairAction row col)).expect value := rfl

/-- In a zero-sum stochastic game, the auxiliary matrix's column utility is
the normalized player-one return with the negated continuation value. -/
theorem auxiliaryUtility_one_eq (hzero : G.IsZeroSum) (β : ℝ)
    (value : G.State → ℝ) (state : G.State)
    (row : G.Action 0) (col : G.Action 1) :
    MatrixGame.utility (G.auxiliaryMatrix β value state) (row, col) 1 =
      (1 - β) * G.stageUtility state (G.pairAction row col) 1 +
        β * (G.transition state (G.pairAction row col)).expect
          (fun next => -value next) := by
  have hstage := (hzero state (G.pairAction row col)).eq_neg ()
  rw [MatrixGame.utility_one, auxiliaryMatrix, hstage]
  rw [show (fun next => -value next) =
      fun next => (-1 : ℝ) * value next by
    funext next
    simp, FinDist.expect_smul]
  ring

variable [Fintype G.State]
variable [∀ i, Fintype (G.Action i)] [∀ i, Nonempty (G.Action i)]

/-- Evaluate every auxiliary matrix at its finite zero-sum value. -/
def shapleyOperator (β : ℝ) (value : G.State → ℝ) : G.State → ℝ :=
  fun state => MatrixGame.value (G.auxiliaryMatrix β value state)

omit [∀ i, Fintype (G.Action i)] [∀ i, Nonempty (G.Action i)] in
private theorem abs_expect_sub_le_dist (law : FinDist G.State)
    (value other : G.State → ℝ) :
    |law.expect value - law.expect other| ≤ dist value other := by
  rw [abs_sub_le_iff]
  constructor
  · have hmono : law.expect value ≤
        law.expect (fun state => other state + dist value other) :=
      FinDist.expect_mono fun state _ => by
        have hcoord := dist_le_pi_dist value other state
        rw [Real.dist_eq, abs_sub_le_iff] at hcoord
        linarith [hcoord.1, hcoord.2]
    rw [FinDist.expect_add, FinDist.expect_const] at hmono
    linarith
  · have hmono : law.expect other ≤
        law.expect (fun state => value state + dist value other) :=
      FinDist.expect_mono fun state _ => by
        have hcoord := dist_le_pi_dist value other state
        rw [Real.dist_eq, abs_sub_le_iff] at hcoord
        linarith [hcoord.1, hcoord.2]
    rw [FinDist.expect_add, FinDist.expect_const] at hmono
    linarith

/-- Statewise perturbation bound for the Shapley operator. -/
theorem abs_shapleyOperator_sub_le {β : ℝ} (hβ : 0 ≤ β)
    (value other : G.State → ℝ) (state : G.State) :
    |G.shapleyOperator β value state - G.shapleyOperator β other state| ≤
      β * dist value other := by
  apply MatrixGame.abs_value_sub_le_of_entrywise_abs_le
  intro row col
  have hE := abs_expect_sub_le_dist G
    (G.transition state (G.pairAction row col)) value other
  calc
    |G.auxiliaryMatrix β value state row col -
        G.auxiliaryMatrix β other state row col|
        = β * |(G.transition state (G.pairAction row col)).expect value -
            (G.transition state (G.pairAction row col)).expect other| := by
          rw [auxiliaryMatrix, auxiliaryMatrix,
            add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ]
    _ ≤ β * dist value other := mul_le_mul_of_nonneg_left hE hβ

/-- The Shapley operator is `β`-Lipschitz in continuation values. -/
theorem lipschitzWith_shapleyOperator (β : ℝ≥0) :
    LipschitzWith β (G.shapleyOperator (β : ℝ)) := by
  refine LipschitzWith.of_dist_le_mul fun value other => ?_
  rw [dist_pi_le_iff (by positivity)]
  intro state
  rw [Real.dist_eq]
  exact G.abs_shapleyOperator_sub_le β.coe_nonneg value other state

/-- For `β < 1`, the Shapley operator is a contraction. -/
theorem contractingWith_shapleyOperator {β : ℝ≥0} (hβ : β < 1) :
    ContractingWith β (G.shapleyOperator (β : ℝ)) :=
  ⟨hβ, G.lipschitzWith_shapleyOperator β⟩

/-- Shapley's normalized discounted value equation has a unique solution. -/
theorem existsUnique_shapleyValue {β : ℝ≥0} (hβ : β < 1) :
    ∃! value : G.State → ℝ, G.shapleyOperator (β : ℝ) value = value := by
  have hc := G.contractingWith_shapleyOperator hβ
  exact ⟨hc.fixedPoint (G.shapleyOperator (β : ℝ)),
    hc.fixedPoint_isFixedPt,
    fun value hvalue => hc.fixedPoint_unique hvalue⟩

/-- The unique normalized discounted value selected by Banach's theorem. -/
noncomputable def discountedValue {β : ℝ≥0} (hβ : β < 1) : G.State → ℝ :=
  (G.contractingWith_shapleyOperator hβ).fixedPoint
    (G.shapleyOperator (β : ℝ))

/-- The discounted value satisfies the Shapley equation. -/
theorem shapleyOperator_discountedValue {β : ℝ≥0} (hβ : β < 1) :
    G.shapleyOperator (β : ℝ) (G.discountedValue hβ) =
      G.discountedValue hβ :=
  (G.contractingWith_shapleyOperator hβ).fixedPoint_isFixedPt

/-- Select the statewise stationary saddle actions at the discounted value. -/
noncomputable def stationarySaddleProfile {β : ℝ≥0} (hβ : β < 1)
    (state : G.State) :
    Profile (MatrixGame.form (G.Action 0) (G.Action 1)).sig.mixed :=
  MatrixGame.valueProfile
    (G.auxiliaryMatrix (β : ℝ) (G.discountedValue hβ) state)

/-- The selected stationary action pair is a saddle point of every auxiliary
one-shot game at the discounted continuation value. -/
theorem stationarySaddleProfile_isSaddlePoint {β : ℝ≥0} (hβ : β < 1)
    (state : G.State) :
    IsSaddlePoint
      (MatrixGame.utility
        (G.auxiliaryMatrix (β : ℝ) (G.discountedValue hβ) state))
      (G.stationarySaddleProfile hβ state) :=
  MatrixGame.valueProfile_isSaddlePoint
    (G.auxiliaryMatrix (β : ℝ) (G.discountedValue hβ) state)

/-- Bellman's value is realized by the selected stationary saddle actions. -/
theorem discountedValue_eq_stationaryExpectedUtility {β : ℝ≥0}
    (hβ : β < 1) (state : G.State) :
    G.discountedValue hβ state =
      expectedUtility
        (MatrixGame.utility
          (G.auxiliaryMatrix (β : ℝ) (G.discountedValue hβ) state)) 0
        ((MatrixGame.form (G.Action 0) (G.Action 1)).mixed.play
          (G.stationarySaddleProfile hβ state)) := by
  let A := G.auxiliaryMatrix (β : ℝ) (G.discountedValue hβ) state
  have hfixed : MatrixGame.value A = G.discountedValue hβ state := by
    exact congrFun (G.shapleyOperator_discountedValue hβ) state
  have hrealized :
      expectedUtility (MatrixGame.utility A) 0
          ((MatrixGame.form (G.Action 0) (G.Action 1)).mixed.play
            (MatrixGame.valueProfile A)) = MatrixGame.value A :=
    MatrixGame.valueProfile_expectedUtility A
  exact hfixed.symm.trans hrealized.symm

end GameTheory.Stochastic.Game
