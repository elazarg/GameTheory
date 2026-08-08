/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import UniformEquilibrium.VanishingDiscount.Fink.Limit

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
