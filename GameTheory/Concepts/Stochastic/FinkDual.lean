/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.FinkLimit

/-!
# Coordinate certificates for the Fink supported tangent system

This file makes the abstract dual obstruction to supported tangent
feasibility concrete.  A dual functional is expanded into its residual and
pure-action coordinate weights, and the coordinate projections give small
certificates which can expose an infeasible tangent target directly.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open scoped BigOperators

variable {ι : Type}

/-- The coefficient with which a dual functional reads an on-profile
residual coordinate. -/
noncomputable def finkSupportResidualDualWeight
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (ℓ : Module.Dual ℝ G.FinkSupportTangentEquationVector)
    (s : G.State) (who : ι) : ℝ := by
  classical
  exact ℓ (Pi.single s (Pi.single who 1), 0)

/-- The coefficient with which a dual functional reads a supported
pure-action coordinate. -/
noncomputable def finkSupportActionDualWeight
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (ℓ : Module.Dual ℝ G.FinkSupportTangentEquationVector)
    (s : G.State) (who : ι) (d : G.Act who) : ℝ := by
  classical
  exact ℓ (0, Pi.single s (Pi.single who (Pi.single d 1)))

/-- Apply a linear map to the canonical finite dependent-function
decomposition. -/
theorem linearMap_apply_pi_eq_sum_single
    {R N : Type} [Semiring R] [AddCommMonoid N] [Module R N]
    {α : Type} [Fintype α] [DecidableEq α]
    {M : α → Type} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (f : ((i : α) → M i) →ₗ[R] N) (x : (i : α) → M i) :
    f x = ∑ i, f (Pi.single i (x i)) := by
  rw [← map_sum, Finset.univ_sum_single]

/-- Coordinate expansion of a functional on a finite real function space. -/
theorem linearMap_apply_pi_real_eq_sum
    {α : Type} [Fintype α] [DecidableEq α]
    (f : (α → ℝ) →ₗ[ℝ] ℝ) (x : α → ℝ) :
    f x = ∑ i, f (Pi.single i 1) * x i := by
  rw [linearMap_apply_pi_eq_sum_single f x]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show Pi.single i (x i) = x i • Pi.single i 1 by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]]
  simp [mul_comm]

/-- Coordinate expansion through two finite function layers. -/
theorem linearMap_apply_pi_pi_real_eq_sum
    {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (f : (α → β → ℝ) →ₗ[ℝ] ℝ) (x : α → β → ℝ) :
    f x = ∑ a, ∑ b,
      f (Pi.single a (Pi.single b 1)) * x a b := by
  rw [linearMap_apply_pi_eq_sum_single f x]
  apply Finset.sum_congr rfl
  intro a ha
  let fa : (β → ℝ) →ₗ[ℝ] ℝ :=
    f.comp (LinearMap.single ℝ (fun _ : α => β → ℝ) a)
  have hfa := linearMap_apply_pi_real_eq_sum fa (x a)
  simpa [fa] using hfa

/-- Coordinate expansion through a finite function layer, a finite player
layer, and a player-dependent finite action layer. -/
theorem linearMap_apply_pi_pi_pi_real_eq_sum
    {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {γ : β → Type} [∀ b, Fintype (γ b)] [∀ b, DecidableEq (γ b)]
    (f : (α → ∀ b, γ b → ℝ) →ₗ[ℝ] ℝ)
    (x : α → ∀ b, γ b → ℝ) :
    f x = ∑ a, ∑ b, ∑ c,
      f (Pi.single a (Pi.single b (Pi.single c 1))) * x a b c := by
  classical
  rw [linearMap_apply_pi_eq_sum_single f x]
  apply Finset.sum_congr rfl
  intro a ha
  let fa : (∀ b, γ b → ℝ) →ₗ[ℝ] ℝ :=
    f.comp (LinearMap.single ℝ (fun _ : α => ∀ b, γ b → ℝ) a)
  change fa (x a) = _
  rw [linearMap_apply_pi_eq_sum_single fa (x a)]
  apply Finset.sum_congr rfl
  intro b hb
  let fab : (γ b → ℝ) →ₗ[ℝ] ℝ :=
    fa.comp (LinearMap.single ℝ (fun b => γ b → ℝ) b)
  have hfab := linearMap_apply_pi_real_eq_sum fab (x a b)
  simpa [fa, fab] using hfab

/-- Every functional on the finite tangent-equation space is the sum of its
residual-coordinate and pure-action-coordinate weights. -/
theorem finkSupportDual_apply_eq_coordinateSum
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (ℓ : Module.Dual ℝ G.FinkSupportTangentEquationVector)
    (x : G.FinkSupportTangentEquationVector) :
    ℓ x =
      (∑ s, ∑ who,
        G.finkSupportResidualDualWeight ℓ s who * x.1 s who) +
      ∑ s, ∑ who, ∑ d,
        G.finkSupportActionDualWeight ℓ s who d * x.2 s who d := by
  classical
  let ℓresidual : (G.State → Payoff ι) →ₗ[ℝ] ℝ :=
    ℓ.comp (LinearMap.inl ℝ (G.State → Payoff ι) G.FinkPureActionVector)
  let ℓaction : G.FinkPureActionVector →ₗ[ℝ] ℝ :=
    ℓ.comp (LinearMap.inr ℝ (G.State → Payoff ι) G.FinkPureActionVector)
  have hresidual := linearMap_apply_pi_pi_real_eq_sum ℓresidual x.1
  have haction := linearMap_apply_pi_pi_pi_real_eq_sum ℓaction x.2
  have hx : x = (x.1, 0) + (0, x.2) := by
    ext <;> simp
  rw [hx, map_add]
  simpa [ℓresidual, ℓaction, finkSupportResidualDualWeight,
    finkSupportActionDualWeight] using congrArg₂ (· + ·) hresidual haction

/-- The elementary continuation-potential vector supported at one
state-player coordinate. -/
noncomputable def finkPotentialCoordinateBasis
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq G.State] [DecidableEq ι]
    (s : G.State) (who : ι) : G.State → Payoff ι :=
  Pi.single s (Pi.single who 1)

/-- Annihilating the supported tangent operator is equivalent to
annihilating it on the elementary continuation-potential coordinates.  This
is the finite adjoint-stationarity test. -/
theorem finkSupportDual_annihilates_operator_iff_basis
    (G : StochasticGame ι)
    [Fintype G.State] [DecidableEq G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (ℓ : Module.Dual ℝ G.FinkSupportTangentEquationVector) :
    (∀ A : G.State → Payoff ι,
      ℓ (G.finkSupportTangentOperator z A) = 0) ↔
    ∀ s who,
      ℓ (G.finkSupportTangentOperator z
        (G.finkPotentialCoordinateBasis s who)) = 0 := by
  classical
  constructor
  · intro h s who
    exact h _
  · intro h A
    let f : (G.State → Payoff ι) →ₗ[ℝ] ℝ :=
      ℓ.comp (G.finkSupportTangentOperator z)
    have hf := linearMap_apply_pi_pi_real_eq_sum f A
    change f A = 0
    rw [hf]
    apply Finset.sum_eq_zero
    intro s hs
    apply Finset.sum_eq_zero
    intro who hwho
    have hcoord := h s who
    change f (G.finkPotentialCoordinateBasis s who) = 0 at hcoord
    rw [mul_eq_zero]
    left
    simpa [finkPotentialCoordinateBasis] using hcoord

/-- Fully coordinatewise adjoint stationarity for a functional annihilating
the supported tangent operator. -/
theorem finkSupportDual_annihilates_operator_iff_coordinateStationary
    (G : StochasticGame ι)
    [Fintype G.State] [DecidableEq G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (ℓ : Module.Dual ℝ G.FinkSupportTangentEquationVector) :
    (∀ A : G.State → Payoff ι,
      ℓ (G.finkSupportTangentOperator z A) = 0) ↔
    ∀ t who,
      (∑ s, ∑ i,
        G.finkSupportResidualDualWeight ℓ s i *
          G.finkContinuationResidualVector
            (G.finkPotentialCoordinateBasis t who) z s i) +
      ∑ s, ∑ i, ∑ d,
        G.finkSupportActionDualWeight ℓ s i d *
          (if G.finkProfile z s i d ≠ 0 then
            G.finkContinuationGain
              (G.finkPotentialCoordinateBasis t who) z s i d else 0) = 0 := by
  rw [G.finkSupportDual_annihilates_operator_iff_basis z ℓ]
  constructor
  · intro h t who
    have hcoord := h t who
    rw [G.finkSupportDual_apply_eq_coordinateSum] at hcoord
    exact hcoord
  · intro h t who
    have hcoord := h t who
    rw [G.finkSupportDual_apply_eq_coordinateSum]
    exact hcoord

/-- The dual functional annihilates the supported tangent target exactly
when its pure-action weights annihilate the requested supported gains. -/
theorem finkSupportDual_target_eq_zero_iff_coordinateSum
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (ℓ : Module.Dual ℝ G.FinkSupportTangentEquationVector) :
    ℓ (G.finkSupportTangentTarget z H K) = 0 ↔
      ∑ s, ∑ who, ∑ d,
        G.finkSupportActionDualWeight ℓ s who d *
          (if G.finkProfile z s who d ≠ 0 then
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d else 0) = 0 := by
  rw [G.finkSupportDual_apply_eq_coordinateSum]
  simp [finkSupportTangentTarget]

/-- Projection onto one residual coordinate of the tangent-equation space. -/
def finkSupportResidualCoordinateDual
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s : G.State) (who : ι) :
    Module.Dual ℝ G.FinkSupportTangentEquationVector where
  toFun x := x.1 s who
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Projection onto one pure-action coordinate of the tangent-equation
space. -/
def finkSupportActionCoordinateDual
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s : G.State) (who : ι) (d : G.Act who) :
    Module.Dual ℝ G.FinkSupportTangentEquationVector where
  toFun x := x.2 s who d
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem finkSupportResidualCoordinateDual_apply
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s : G.State) (who : ι)
    (x : G.FinkSupportTangentEquationVector) :
    G.finkSupportResidualCoordinateDual s who x = x.1 s who := rfl

@[simp] theorem finkSupportActionCoordinateDual_apply
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s : G.State) (who : ι) (d : G.Act who)
    (x : G.FinkSupportTangentEquationVector) :
    G.finkSupportActionCoordinateDual s who d x = x.2 s who d := rfl

@[simp] theorem finkSupportResidualCoordinateDual_operator
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (A : G.State → Payoff ι) :
    G.finkSupportResidualCoordinateDual s who
        (G.finkSupportTangentOperator z A) =
      G.finkContinuationResidualVector A z s who := rfl

@[simp] theorem finkSupportActionCoordinateDual_operator
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who)
    (A : G.State → Payoff ι) :
    G.finkSupportActionCoordinateDual s who d
        (G.finkSupportTangentOperator z A) =
      if G.finkProfile z s who d ≠ 0 then
        G.finkContinuationGain A z s who d else 0 := rfl

@[simp] theorem finkSupportActionCoordinateDual_target
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who) :
    G.finkSupportActionCoordinateDual s who d
        (G.finkSupportTangentTarget z H K) =
      if G.finkProfile z s who d ≠ 0 then
        G.finkStageGain z s who d +
          G.finkContinuationGain (H - K) z s who d else 0 := rfl

/-- A supported action whose continuation gain vanishes on every potential,
but whose requested tangent gain is nonzero, gives an explicit dual
certificate of infeasibility. -/
theorem finkSupportActionCoordinateDual_is_obstruction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who)
    (hsupport : G.finkProfile z s who d ≠ 0)
    (hgain : ∀ A : G.State → Payoff ι,
      G.finkContinuationGain A z s who d = 0)
    (htarget : G.finkStageGain z s who d +
        G.finkContinuationGain (H - K) z s who d ≠ 0) :
    (∀ A : G.State → Payoff ι,
      G.finkSupportActionCoordinateDual s who d
        (G.finkSupportTangentOperator z A) = 0) ∧
      G.finkSupportActionCoordinateDual s who d
        (G.finkSupportTangentTarget z H K) ≠ 0 := by
  constructor
  · intro A
    rw [G.finkSupportActionCoordinateDual_operator]
    simp [hsupport, hgain]
  · rw [G.finkSupportActionCoordinateDual_target]
    simpa [hsupport] using htarget

/-- Coordinate obstruction, stated directly as failure of supported harmonic
adjustment existence. -/
theorem not_exists_finkSupportHarmonicAdjustment_of_actionCoordinate
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who)
    (hsupport : G.finkProfile z s who d ≠ 0)
    (hgain : ∀ A : G.State → Payoff ι,
      G.finkContinuationGain A z s who d = 0)
    (htarget : G.finkStageGain z s who d +
        G.finkContinuationGain (H - K) z s who d ≠ 0) :
    ¬ ∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d := by
  intro hA
  have hdual := G.finkSupportActionCoordinateDual_is_obstruction
    z H K s who d hsupport hgain htarget
  have hfeasible := (G.exists_finkSupportHarmonicAdjustment_iff_forall_dual
    z H K).1 hA
  exact hdual.2 (hfeasible _ hdual.1)

end StochasticGame
end GameTheory
