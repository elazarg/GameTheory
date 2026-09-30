/-
# Discounted values of zero-sum stochastic games

At every state, the normalized Shapley operator evaluates the finite matrix

`(1 - β) * stage payoff + β * expected continuation value`.

Action sets are finite; the state space is arbitrary. When player zero's stage
utility is bounded, the operator preserves bounded continuation values, and
since the canonical matrix value is nonexpansive it is a `β`-contraction in the
sup norm of `ℓ^∞` on states. Banach's theorem gives its unique bounded fixed
point, and the matrix adapter selects stationary saddle actions realizing the
Bellman value at every state. Uniqueness is among bounded values only: on an
infinite state space the Bellman equation can also have unbounded solutions.

This module proves the value-equation and stationary one-shot statements.  It
does not introduce an infinite path law or claim optimality against arbitrary
infinite-history strategies.
-/

import GameTheory.Analysis.MatrixValue
import GameTheory.Stochastic.ZeroSum
import GameTheory.Stochastic.OneStep
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Lp.lpSpace

noncomputable section

namespace GameTheory.Stochastic.Game

open GameTheory.Math.Probability MatrixGame
open scoped NNReal ENNReal

variable (G : Game (Fin 2))

/-- The normalized auxiliary one-shot matrix at a state and continuation
value. -/
def auxiliaryMatrix (β : ℝ) (value : G.State → ℝ) (state : G.State) :
    G.Action 0 → G.Action 1 → ℝ :=
  fun row col =>
    G.normalizedOneStepUtility β value state (G.pairAction row col) 0

/-- The auxiliary matrix's row utility is the normalized player-zero
one-step return. -/
theorem auxiliaryUtility_zero (β : ℝ) (value : G.State → ℝ)
    (state : G.State)
    (row : G.Action 0) (col : G.Action 1) :
    MatrixGame.utility (G.auxiliaryMatrix β value state)
        (row, col) 0 =
      (1 - β) * G.stageUtility state (G.pairAction row col) 0 +
        β * expect (G.transition state (G.pairAction row col)) value := rfl

/-- In a zero-sum stochastic game, the auxiliary matrix's column utility is
the normalized player-one return with the negated continuation value. -/
theorem auxiliaryUtility_one_eq (hzero : G.IsZeroSum) (β : ℝ)
    (value : G.State → ℝ) (state : G.State)
    (row : G.Action 0) (col : G.Action 1) :
    MatrixGame.utility (G.auxiliaryMatrix β value state)
        (row, col) 1 =
      (1 - β) * G.stageUtility state (G.pairAction row col) 1 +
        β * expect (G.transition state (G.pairAction row col))
          (fun next => -value next) := by
  have hstage := (hzero state (G.pairAction row col)).eq_neg ()
  rw [MatrixGame.utility_one, auxiliaryMatrix, normalizedOneStepUtility,
    hstage]
  simp only [expect_neg]
  ring

/-- Player zero's stage utility is uniformly bounded over states and joint
actions. -/
def HasBoundedRowStageUtility : Prop :=
  ∃ bound : ℝ, ∀ state joint, |G.stageUtility state joint 0| ≤ bound

/-- Finite states and actions bound every stage utility. -/
theorem hasBoundedRowStageUtility_of_finite [Finite G.State]
    [∀ i, Finite (G.Action i)] : G.HasBoundedRowStageUtility := by
  obtain ⟨bound, hbound⟩ := (Set.finite_range
    fun pair : G.State × (∀ i, G.Action i) =>
      |G.stageUtility pair.1 pair.2 0|).bddAbove
  exact ⟨bound, fun state joint => hbound ⟨(state, joint), rfl⟩⟩

/-- Bounded continuation values: the sup-normed space `ℓ^∞` on states. -/
abbrev BoundedStateValue := lp (fun _ : G.State => ℝ) ∞

instance : Nonempty G.BoundedStateValue := ⟨0⟩

variable [∀ i, Fintype (G.Action i)] [∀ i, Nonempty (G.Action i)]

/-- Evaluate every auxiliary matrix at its finite zero-sum value. -/
def shapleyOperator (β : ℝ) (value : G.State → ℝ) : G.State → ℝ :=
  fun state => MatrixGame.value (G.auxiliaryMatrix β value state)

omit [∀ i, Fintype (G.Action i)] [∀ i, Nonempty (G.Action i)] in
private theorem abs_expect_sub_le (law : PMF G.State)
    {value other : G.State → ℝ} {valueBound otherBound distance : ℝ}
    (hvalue : ∀ state, |value state| ≤ valueBound)
    (hother : ∀ state, |other state| ≤ otherBound)
    (hdistance : ∀ state, |value state - other state| ≤ distance) :
    |expect law value - expect law other| ≤ distance := by
  obtain ⟨state, _⟩ := law.support_nonempty
  rw [← expect_sub (payoffIntegrable_of_bounded law value hvalue)
    (payoffIntegrable_of_bounded law other hother)]
  exact expect_abs_le_of_bounded ((abs_nonneg _).trans (hdistance state)) hdistance

/-- Statewise perturbation bound for the Shapley operator. -/
theorem abs_shapleyOperator_sub_le {β : ℝ} (hβ : 0 ≤ β)
    {value other : G.State → ℝ} {valueBound otherBound distance : ℝ}
    (hvalue : ∀ state, |value state| ≤ valueBound)
    (hother : ∀ state, |other state| ≤ otherBound)
    (hdistance : ∀ state, |value state - other state| ≤ distance)
    (state : G.State) :
    |G.shapleyOperator β value state - G.shapleyOperator β other state| ≤
      β * distance := by
  apply MatrixGame.abs_value_sub_le_of_entrywise_abs_le
  intro row col
  have hE := abs_expect_sub_le G
    (G.transition state (G.pairAction row col)) hvalue hother hdistance
  calc
    |G.auxiliaryMatrix β value state
         row col -
        G.auxiliaryMatrix β other state
           row col|
        = β * |expect (G.transition state (G.pairAction row col)) value -
            expect (G.transition state (G.pairAction row col)) other| := by
          rw [auxiliaryMatrix, auxiliaryMatrix,
            normalizedOneStepUtility, normalizedOneStepUtility,
            add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ]
    _ ≤ β * distance := mul_le_mul_of_nonneg_left hE hβ

/-- Bounded stage utility and a bounded continuation value give a bounded
Shapley image. -/
theorem abs_shapleyOperator_le {β stageBound valueBound : ℝ}
    (hstage : ∀ state joint, |G.stageUtility state joint 0| ≤ stageBound)
    {value : G.State → ℝ} (hvalue : ∀ state, |value state| ≤ valueBound)
    (state : G.State) :
    |G.shapleyOperator β value state| ≤
      |1 - β| * stageBound + |β| * valueBound := by
  apply MatrixGame.abs_value_le_of_entrywise_abs_le
  intro row col
  have hE : |expect (G.transition state (G.pairAction row col)) value| ≤
      valueBound := by
    obtain ⟨next, _⟩ := (G.transition state (G.pairAction row col)).support_nonempty
    exact expect_abs_le_of_bounded ((abs_nonneg _).trans (hvalue next)) hvalue
  rw [auxiliaryMatrix, normalizedOneStepUtility]
  calc
    |(1 - β) * G.stageUtility state (G.pairAction row col) 0 +
        β * expect (G.transition state (G.pairAction row col)) value| ≤
      |1 - β| * |G.stageUtility state (G.pairAction row col) 0| +
        |β| * |expect (G.transition state (G.pairAction row col)) value| := by
      rw [← abs_mul, ← abs_mul]
      exact abs_add_le _ _
    _ ≤ |1 - β| * stageBound + |β| * valueBound := by
      gcongr
      exact hstage state _

/-- The Shapley operator restricted to bounded continuation values. -/
def boundedShapleyOperator (hstage : G.HasBoundedRowStageUtility) (β : ℝ)
    (value : G.BoundedStateValue) : G.BoundedStateValue :=
  ⟨G.shapleyOperator β value, memℓp_infty (by
    obtain ⟨stageBound, hbound⟩ := hstage
    refine ⟨|1 - β| * stageBound + |β| * ‖value‖, ?_⟩
    rintro _ ⟨state, rfl⟩
    exact G.abs_shapleyOperator_le hbound
      (fun state => lp.norm_apply_le_norm ENNReal.top_ne_zero value state) state)⟩

@[simp]
theorem coe_boundedShapleyOperator (hstage : G.HasBoundedRowStageUtility)
    (β : ℝ) (value : G.BoundedStateValue) :
    ⇑(G.boundedShapleyOperator hstage β value) = G.shapleyOperator β value :=
  rfl

/-- The bounded Shapley operator is `β`-Lipschitz in continuation values. -/
theorem lipschitzWith_boundedShapleyOperator
    (hstage : G.HasBoundedRowStageUtility) (β : ℝ≥0) :
    LipschitzWith β (G.boundedShapleyOperator hstage (β : ℝ)) := by
  refine LipschitzWith.of_dist_le_mul fun value other => ?_
  rw [dist_eq_norm, dist_eq_norm]
  refine lp.norm_le_of_forall_le (by positivity) fun state => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, coe_boundedShapleyOperator,
    coe_boundedShapleyOperator, Real.norm_eq_abs]
  exact G.abs_shapleyOperator_sub_le β.coe_nonneg
    (fun state => lp.norm_apply_le_norm ENNReal.top_ne_zero value state)
    (fun state => lp.norm_apply_le_norm ENNReal.top_ne_zero other state)
    (fun state => by
      simpa only [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] using
        lp.norm_apply_le_norm ENNReal.top_ne_zero (value - other) state)
    state

/-- For `β < 1`, the bounded Shapley operator is a contraction. -/
theorem contractingWith_boundedShapleyOperator
    (hstage : G.HasBoundedRowStageUtility) {β : ℝ≥0} (hβ : β < 1) :
    ContractingWith β (G.boundedShapleyOperator hstage (β : ℝ)) :=
  ⟨hβ, G.lipschitzWith_boundedShapleyOperator hstage β⟩

/-- Shapley's normalized discounted value equation has a unique bounded
solution. -/
theorem existsUnique_shapleyValue (hstage : G.HasBoundedRowStageUtility)
    {β : ℝ≥0} (hβ : β < 1) :
    ∃! value : G.State → ℝ,
      (∃ bound : ℝ, ∀ state, |value state| ≤ bound) ∧
        G.shapleyOperator (β : ℝ) value = value := by
  have hc := G.contractingWith_boundedShapleyOperator hstage hβ
  let fixed := hc.fixedPoint (G.boundedShapleyOperator hstage (β : ℝ))
  refine ⟨fixed, ⟨⟨‖fixed‖, lp.norm_apply_le_norm ENNReal.top_ne_zero fixed⟩,
    congrArg (⇑) hc.fixedPoint_isFixedPt⟩, ?_⟩
  rintro value ⟨⟨bound, hbound⟩, hvalue⟩
  let lifted : G.BoundedStateValue :=
    ⟨value, memℓp_infty ⟨bound, by rintro _ ⟨state, rfl⟩; exact hbound state⟩⟩
  have hlifted : Function.IsFixedPt (G.boundedShapleyOperator hstage (β : ℝ))
      lifted :=
    Subtype.ext hvalue
  exact congrArg (⇑) (hc.fixedPoint_unique hlifted)

/-- The unique bounded normalized discounted value selected by Banach's
theorem. -/
noncomputable def discountedValue (hstage : G.HasBoundedRowStageUtility)
    {β : ℝ≥0} (hβ : β < 1) : G.State → ℝ :=
  ⇑((G.contractingWith_boundedShapleyOperator hstage hβ).fixedPoint
    (G.boundedShapleyOperator hstage (β : ℝ)))

/-- The discounted value is bounded. -/
theorem exists_abs_discountedValue_le (hstage : G.HasBoundedRowStageUtility)
    {β : ℝ≥0} (hβ : β < 1) :
    ∃ bound : ℝ, ∀ state, |G.discountedValue hstage hβ state| ≤ bound :=
  ⟨_, fun state => by
    rw [discountedValue]
    simpa only [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero
      ((G.contractingWith_boundedShapleyOperator hstage hβ).fixedPoint
        (G.boundedShapleyOperator hstage (β : ℝ))) state⟩

/-- The discounted value satisfies the Shapley equation. -/
theorem shapleyOperator_discountedValue (hstage : G.HasBoundedRowStageUtility)
    {β : ℝ≥0} (hβ : β < 1) :
    G.shapleyOperator (β : ℝ) (G.discountedValue hstage hβ) =
      G.discountedValue hstage hβ :=
  congrArg (⇑) (G.contractingWith_boundedShapleyOperator hstage hβ).fixedPoint_isFixedPt

/-- Select the statewise stationary saddle actions at the discounted value. -/
noncomputable def stationarySaddleProfile (hstage : G.HasBoundedRowStageUtility)
    {β : ℝ≥0} (hβ : β < 1) (state : G.State) :
    Profile (MatrixGame.form (G.Action 0) (G.Action 1)).sig.mixed :=
  MatrixGame.valueProfile
    (G.auxiliaryMatrix (β : ℝ) (G.discountedValue hstage hβ) state)

/-- The selected stationary action pair is a saddle point of every auxiliary
one-shot game at the discounted continuation value. -/
theorem stationarySaddleProfile_isSaddlePoint
    (hstage : G.HasBoundedRowStageUtility) {β : ℝ≥0} (hβ : β < 1)
    (state : G.State) :
    IsSaddlePoint
      (MatrixGame.utility
        (G.auxiliaryMatrix (β : ℝ) (G.discountedValue hstage hβ) state))
      (G.stationarySaddleProfile hstage hβ state) :=
  MatrixGame.valueProfile_isSaddlePoint
    (G.auxiliaryMatrix (β : ℝ) (G.discountedValue hstage hβ) state)

/-- Bellman's value is realized by the selected stationary saddle actions. -/
theorem discountedValue_eq_stationaryExpectedUtility
    (hstage : G.HasBoundedRowStageUtility) {β : ℝ≥0}
    (hβ : β < 1) (state : G.State) :
    G.discountedValue hstage hβ state =
      expectedUtility
        (MatrixGame.utility
          (G.auxiliaryMatrix (β : ℝ) (G.discountedValue hstage hβ) state)) 0
        ((MatrixGame.form (G.Action 0) (G.Action 1)).mixed.play
          (G.stationarySaddleProfile hstage hβ state)) := by
  let A := G.auxiliaryMatrix (β : ℝ) (G.discountedValue hstage hβ) state
  have hfixed : MatrixGame.value A = G.discountedValue hstage hβ state := by
    exact congrFun (G.shapleyOperator_discountedValue hstage hβ) state
  have hrealized :
      expectedUtility (MatrixGame.utility A) 0
          ((MatrixGame.form (G.Action 0) (G.Action 1)).mixed.play
            (MatrixGame.valueProfile A))
           = MatrixGame.value A :=
    MatrixGame.valueProfile_expectedUtility A
  exact hfixed.symm.trans hrealized.symm

end GameTheory.Stochastic.Game
