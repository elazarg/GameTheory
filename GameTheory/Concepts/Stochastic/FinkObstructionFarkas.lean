/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FinkObstruction
import Math.NormalizedFarkasBasis

/-!
# Finite Farkas coordinates for Fink obstruction flows

A Fink tangent obstruction has signed residual and supported-action
coefficients. This file writes its playerwise state-flow equations as one
finite homogeneous matrix system. The target pairing is the normalizing mass
functional.

The generic two-orientation construction in `Math.NormalizedFarkasBasis`
then converts the signed flow into an ordinary nonnegative normalized Farkas
certificate. Orientation records the sign of a public statistical contrast;
it does not reverse the controlled transition.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.LinearAlgebra

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- A residual coefficient or a supported pure-deviation coefficient. -/
abbrev FinkObstructionColumn (G : StochasticGame ι) :=
  Sum (G.State × ι) (Σ who : ι, G.State × G.Act who)

/-- One playerwise destination-state flow equation. -/
abbrev FinkObstructionRow (G : StochasticGame ι) :=
  ι × G.State

/-- Coordinate matrix of the signed Fink obstruction balance. -/
def finkObstructionBalance
    {U : ℝ} (z : G.finkDomain U) :
    Matrix (FinkObstructionRow G) (FinkObstructionColumn G) ℝ
  | (who, destination), Sum.inl (s, sourceWho) =>
      if sourceWho = who then
        (G.finkStateKernel z s destination).toReal -
          if s = destination then 1 else 0
      else 0
  | (who, destination), Sum.inr ⟨sourceWho, s, d⟩ =>
      if sourceWho = who then
        if G.finkProfile z s sourceWho d ≠ 0 then
          (G.finkPureDeviationStateKernel
              z s sourceWho d destination).toReal -
            (G.finkStateKernel z s destination).toReal
        else 0
      else 0

/-- Tangent target paired with each signed obstruction coordinate. -/
def finkObstructionMass
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) :
    FinkObstructionColumn G → ℝ
  | Sum.inl _ => 0
  | Sum.inr ⟨who, s, d⟩ =>
      if G.finkProfile z s who d ≠ 0 then
        G.finkStageGain z s who d +
          G.finkContinuationGain (H - K) z s who d
      else 0

/-- Read a concrete obstruction flow as one signed coefficient vector. -/
def NormalizedFinkSupportTangentObstructionFlow.coefficient
    {U : ℝ} {z : G.finkDomain U}
    {H K : G.State → Payoff ι}
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K) :
    FinkObstructionColumn G → ℝ
  | Sum.inl (s, who) => F.residualWeight s who
  | Sum.inr ⟨who, s, d⟩ => F.actionWeight s who d

omit [∀ i, DecidableEq (G.Act i)] in
/-- The abstract operator identity is exactly the finite coordinate balance
of the signed obstruction coefficient vector. -/
theorem NormalizedFinkSupportTangentObstructionFlow.balance_mulVec_coefficient
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K) :
    Matrix.mulVec (G.finkObstructionBalance z) F.coefficient = 0 := by
  classical
  funext row
  rcases row with ⟨who, destination⟩
  change
    Matrix.mulVec (G.finkObstructionBalance z) F.coefficient
      (who, destination) = 0
  have hbalance :=
    NormalizedFinkSupportTangentObstructionFlow.player_state_transition_balance
      G z H K F who destination
  simpa [Matrix.mulVec, dotProduct, finkObstructionBalance,
    NormalizedFinkSupportTangentObstructionFlow.coefficient,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma,
    mul_comm] using hbalance

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- Target normalization is exactly the finite mass equation. -/
theorem NormalizedFinkSupportTangentObstructionFlow.mass_coefficient
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K) :
    (∑ j, G.finkObstructionMass z H K j * F.coefficient j) = 1 := by
  classical
  have htarget := F.target_balance
  rw [Finset.sum_comm] at htarget
  simpa [finkObstructionMass,
    NormalizedFinkSupportTangentObstructionFlow.coefficient,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma,
    mul_comm] using htarget

omit [∀ i, DecidableEq (G.Act i)] in
/-- Every normalized signed Fink obstruction gives a nonnegative
two-orientation Farkas certificate. -/
theorem
    NormalizedFinkSupportTangentObstructionFlow.orientedFarkasCertificate
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (F : G.NormalizedFinkSupportTangentObstructionFlow z H K) :
    signedFarkasToOriented F.coefficient ∈
      normalizedFarkasCertificateSet
        (orientedFarkasBalance (G.finkObstructionBalance z))
        (orientedFarkasMass (G.finkObstructionMass z H K)) := by
  exact signedFarkasToOriented_mem_normalizedFarkasCertificateSet
    (G.finkObstructionBalance z) (G.finkObstructionMass z H K)
    F.coefficient F.balance_mulVec_coefficient F.mass_coefficient

/-- Read a payoff adjustment as a vector indexed by player and destination
state, the row type of the obstruction balance. -/
def finkAdjustmentCoefficient
    (A : G.State → Payoff ι) :
    FinkObstructionRow G → ℝ
  | (who, destination) => A destination who

omit [∀ i, DecidableEq (G.Act i)] in
/-- A residual coordinate of the transposed obstruction matrix is the
corresponding continuation residual. -/
theorem finkObstructionTranspose_mulVec_adjustment_residual
    {U : ℝ} (z : G.finkDomain U)
    (A : G.State → Payoff ι) (s : G.State) (who : ι) :
    Matrix.mulVec (G.finkObstructionBalance z).transpose
        (G.finkAdjustmentCoefficient A) (Sum.inl (s, who)) =
      G.finkContinuationResidualVector A z s who := by
  classical
  rw [G.finkContinuationResidualVector_eq_expect_stateKernel,
    Math.Probability.expect_eq_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    finkObstructionBalance, finkAdjustmentCoefficient,
    Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single who]
  · simp only
    calc
      (∑ destination,
          (((G.finkStateKernel z s destination).toReal -
              if s = destination then 1 else 0) *
            A destination who)) =
          (∑ destination,
              (G.finkStateKernel z s destination).toReal *
                A destination who) -
            ∑ destination,
              (if s = destination then 1 else 0) *
                A destination who := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro destination _
        ring
      _ = (∑ destination,
            (G.finkStateKernel z s destination).toReal *
              A destination who) - A s who := by
        simp
  · intro other hother
    simp [Ne.symm hother]

omit [∀ i, DecidableEq (G.Act i)] in
/-- A supported-action coordinate of the transposed obstruction matrix is
the corresponding pure-deviation continuation gain; unsupported coordinates
are zero. -/
theorem finkObstructionTranspose_mulVec_adjustment_action
    {U : ℝ} (z : G.finkDomain U)
    (A : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who) :
    Matrix.mulVec (G.finkObstructionBalance z).transpose
        (G.finkAdjustmentCoefficient A) (Sum.inr ⟨who, s, d⟩) =
      if G.finkProfile z s who d ≠ 0 then
        G.finkContinuationGain A z s who d
      else 0 := by
  classical
  by_cases hsupported : G.finkProfile z s who d ≠ 0
  · rw [if_pos hsupported,
      G.finkContinuationGain_eq_expect_stateKernels,
      Math.Probability.expect_eq_sum,
      Math.Probability.expect_eq_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      finkObstructionBalance, finkAdjustmentCoefficient,
      Fintype.sum_prod_type]
    rw [← Finset.sum_sub_distrib]
    rw [Fintype.sum_eq_single who]
    · simp only [if_pos hsupported]
      apply Finset.sum_congr rfl
      intro destination _
      simp only [if_true]
      ring
    · intro other hother
      simp [Ne.symm hother]
  · simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      finkObstructionBalance, finkAdjustmentCoefficient,
      hsupported]

omit [∀ i, DecidableEq (G.Act i)] in
/-- Supported harmonic adjustment is exactly solvability of the transposed
finite obstruction matrix with the tangent mass as right-hand side. -/
theorem exists_finkHarmonicAdjustment_iff_transpose_mulVec
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) :
    (∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d) ↔
      ∃ a : FinkObstructionRow G → ℝ,
        Matrix.mulVec (G.finkObstructionBalance z).transpose a =
          G.finkObstructionMass z H K := by
  classical
  constructor
  · rintro ⟨A, hresidual, haction⟩
    refine ⟨G.finkAdjustmentCoefficient A, ?_⟩
    funext column
    cases column with
    | inl residual =>
        rcases residual with ⟨s, who⟩
        rw [G.finkObstructionTranspose_mulVec_adjustment_residual]
        simpa [finkObstructionMass] using
          congrFun (congrFun hresidual s) who
    | inr e =>
        rcases e with ⟨who, s, d⟩
        rw [finkObstructionTranspose_mulVec_adjustment_action
          (G := G)]
        by_cases hsupported : G.finkProfile z s who d ≠ 0
        · rw [if_pos hsupported]
          simpa [finkObstructionMass, hsupported] using
            haction s who d hsupported
        · simp [finkObstructionMass, hsupported]
  · rintro ⟨a, ha⟩
    let A : G.State → Payoff ι :=
      fun destination who => a (who, destination)
    have hcoefficient :
        G.finkAdjustmentCoefficient A = a := by
      funext row
      rcases row with ⟨who, destination⟩
      rfl
    refine ⟨A, ?_, ?_⟩
    · funext s who
      have hcoordinate := congrFun ha (Sum.inl (s, who))
      rw [← hcoefficient,
        G.finkObstructionTranspose_mulVec_adjustment_residual]
        at hcoordinate
      simpa [finkObstructionMass] using hcoordinate
    · intro s who d hsupported
      have hcoordinate :=
        congrFun ha (Sum.inr ⟨who, s, d⟩)
      rw [← hcoefficient,
        finkObstructionTranspose_mulVec_adjustment_action
          (G := G)]
        at hcoordinate
      simpa [finkObstructionMass, hsupported] using hcoordinate

end StochasticGame
end GameTheory
