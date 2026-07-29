/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.FinkSelectionCounterexample

/-!
# Dual obstructions to the supported Fink tangent system

This file makes the branch point after the discounted tangent hierarchy
explicit.  Either the supported tangent target has a harmonic preimage, or a
linear functional annihilates every harmonic adjustment while detecting the
target.  The latter object is the input that an obstruction-to-phase
constructor must turn into a public test, punishment, descent, or sublinear
charge.

The selection-resistant tangent example instantiates the obstruction branch.
Its forced rare-action rate shows that changing the discounted equilibrium
selection cannot move the example back to the feasible branch.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type}

/-- A finite-dimensional dual witness that the supported Fink tangent target
does not lie in the range of the harmonic-adjustment operator. -/
structure FinkSupportTangentDualObstruction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) where
  functional : Module.Dual ℝ G.FinkSupportTangentEquationVector
  operator_eq_zero : ∀ A : G.State → Payoff ι,
    functional (G.finkSupportTangentOperator z A) = 0
  target_ne_zero :
    functional (G.finkSupportTangentTarget z H K) ≠ 0

/-- A scale-fixed dual obstruction.  Normalizing the detected target to one
removes the irrelevant sign and magnitude ambiguity from the functional. -/
structure NormalizedFinkSupportTangentDualObstruction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) where
  functional : Module.Dual ℝ G.FinkSupportTangentEquationVector
  operator_eq_zero : ∀ A : G.State → Payoff ι,
    functional (G.finkSupportTangentOperator z A) = 0
  target_eq_one :
    functional (G.finkSupportTangentTarget z H K) = 1

/-- Forget the normalization while retaining the obstruction. -/
def NormalizedFinkSupportTangentDualObstruction.toDualObstruction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (O : G.NormalizedFinkSupportTangentDualObstruction z H K) :
    G.FinkSupportTangentDualObstruction z H K where
  functional := O.functional
  operator_eq_zero := O.operator_eq_zero
  target_ne_zero := by rw [O.target_eq_one]; norm_num

/-- Every nonzero dual obstruction has a canonical target-one scaling. -/
def FinkSupportTangentDualObstruction.normalize
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (O : G.FinkSupportTangentDualObstruction z H K) :
    G.NormalizedFinkSupportTangentDualObstruction z H K where
  functional :=
    (O.functional (G.finkSupportTangentTarget z H K))⁻¹ • O.functional
  operator_eq_zero := by
    intro A
    simp only [LinearMap.smul_apply, smul_eq_mul, O.operator_eq_zero, mul_zero]
  target_eq_one := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ O.target_ne_zero

/-- A dual obstruction rules out every supported harmonic adjustment. -/
theorem FinkSupportTangentDualObstruction.not_exists_harmonicAdjustment
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (O : G.FinkSupportTangentDualObstruction z H K) :
    ¬ ∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d := by
  rintro ⟨A, hA⟩
  have htarget :
      G.finkSupportTangentTarget z H K =
        G.finkSupportTangentOperator z A :=
    (G.finkSupportTangentOperator_eq_target_iff z H K A).2 hA |>.symm
  apply O.target_ne_zero
  rw [htarget]
  exact O.operator_eq_zero A

/-- Exact finite-dimensional branch point for the supported tangent system.
The obstruction branch carries data rather than only the negation of
feasibility. -/
theorem exists_harmonicAdjustment_or_dualObstruction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) :
    (∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d) ∨
      Nonempty (G.FinkSupportTangentDualObstruction z H K) := by
  classical
  by_cases hA : ∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d
  · exact Or.inl hA
  · right
    have hdual : ¬ ∀ ℓ : Module.Dual ℝ G.FinkSupportTangentEquationVector,
        (∀ A : G.State → Payoff ι,
          ℓ (G.finkSupportTangentOperator z A) = 0) →
        ℓ (G.finkSupportTangentTarget z H K) = 0 := by
      intro h
      exact hA ((G.exists_finkSupportHarmonicAdjustment_iff_forall_dual
        z H K).2 h)
    push Not at hdual
    obtain ⟨ℓ, hoperator, htarget⟩ := hdual
    exact ⟨{
      functional := ℓ
      operator_eq_zero := hoperator
      target_ne_zero := htarget
    }⟩

/-- Scale-fixed form of the tangent branch point.  This is the form intended
for quantitative obstruction responses. -/
theorem exists_harmonicAdjustment_or_normalizedDualObstruction
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) :
    (∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d) ∨
      Nonempty
        (G.NormalizedFinkSupportTangentDualObstruction z H K) := by
  rcases G.exists_harmonicAdjustment_or_dualObstruction z H K with
    hA | hO
  · exact Or.inl hA
  · obtain ⟨O⟩ := hO
    exact Or.inr ⟨O.normalize⟩

namespace FinkSelectionCounterexample
namespace Base

/-- The limiting Fink point from the tangent example, read in the
selection-resistant game.  The compact domain depends only on states and
actions, which are shared by the two games. -/
abbrev selectionLimitPoint : game.finkDomain 1 :=
  FinkTangentCounterexample.limitPoint

lemma selection_limit_live_playerOne_actionA_support :
    game.finkProfile selectionLimitPoint .live false false ≠ 0 := by
  change FinkTangentCounterexample.game.finkProfile
    FinkTangentCounterexample.limitPoint .live false false ≠ 0
  exact FinkTangentCounterexample.limit_live_playerOne_actionA_support

lemma selection_finkContinuationGain_limit_live_playerOne
    (A : CState → Payoff Player) (d : Bool) :
    game.finkContinuationGain A selectionLimitPoint .live false d = 0 := by
  change FinkTangentCounterexample.game.finkContinuationGain A
    FinkTangentCounterexample.limitPoint .live false d = 0
  exact FinkTangentCounterexample.finkContinuationGain_limit_live_playerOne A d

lemma selection_finkStageGain_limit_live_playerOne_actionA :
    game.finkStageGain selectionLimitPoint .live false false = -1 := by
  change FinkTangentCounterexample.game.finkStageGain
    FinkTangentCounterexample.limitPoint .live false false = -1
  exact FinkTangentCounterexample.finkStageGain_limit_live_playerOne_actionA

/-- Coordinate dual obstruction for the selection-resistant example. -/
def selectionTangentDualObstruction :
    game.FinkSupportTangentDualObstruction selectionLimitPoint
      (0 : CState → Payoff Player) 0 := by
  let ℓ := game.finkSupportActionCoordinateDual .live false false
  have h := game.finkSupportActionCoordinateDual_is_obstruction
    selectionLimitPoint (0 : CState → Payoff Player) 0 .live false false
    selection_limit_live_playerOne_actionA_support
    (fun A => selection_finkContinuationGain_limit_live_playerOne A false)
    (by
      rw [selection_finkStageGain_limit_live_playerOne_actionA]
      have hzero : game.finkContinuationGain
          ((0 : CState → Payoff Player) - 0) selectionLimitPoint
            .live false false = 0 := by
        simpa using selection_finkContinuationGain_limit_live_playerOne
          (0 : CState → Payoff Player) false
      rw [hzero]
      norm_num)
  exact {
    functional := ℓ
    operator_eq_zero := h.1
    target_ne_zero := h.2
  }

/-- Selection-resistant acceptance test for the obstruction branch.  The
same example forces the reciprocal-bias rare-action rate at every discounted
Bellman equilibrium and supplies a dual witness at its limiting tangent
system. -/
theorem selection_resistant_tangent_dualObstruction :
    Nonempty (game.FinkSupportTangentDualObstruction selectionLimitPoint
      (0 : CState → Payoff Player) 0) :=
  ⟨selectionTangentDualObstruction⟩

/-- Scale-fixed obstruction carried by the selection-resistant example. -/
theorem selection_resistant_tangent_normalizedDualObstruction :
    Nonempty
      (game.NormalizedFinkSupportTangentDualObstruction selectionLimitPoint
        (0 : CState → Payoff Player) 0) :=
  ⟨selectionTangentDualObstruction.normalize⟩

/-- The obstruction data rules out supported harmonic adjustment in the
selection-resistant game. -/
theorem no_selection_finkSupportHarmonicAdjustment :
    ¬ ∃ A : CState → Payoff Player,
      game.finkContinuationResidualVector A selectionLimitPoint = 0 ∧
        ∀ s who (d : Bool),
          game.finkProfile selectionLimitPoint s who d ≠ 0 →
            game.finkContinuationGain A selectionLimitPoint s who d =
              game.finkStageGain selectionLimitPoint s who d +
                game.finkContinuationGain
                  ((0 : CState → Payoff Player) - 0)
                    selectionLimitPoint s who d :=
  selectionTangentDualObstruction.not_exists_harmonicAdjustment

end Base
end FinkSelectionCounterexample

end StochasticGame
end GameTheory
