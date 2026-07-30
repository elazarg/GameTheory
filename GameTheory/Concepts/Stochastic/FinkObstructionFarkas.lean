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

end StochasticGame
end GameTheory
