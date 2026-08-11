/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNashDefectMobiusIncidence
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtSemantics
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalPacketSimpleFallbackCounterexample

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingMobiusIncidenceCancellationRegression

open QuittingTerminalPacketSimpleFallbackCounterexample

/-- The positive singleton coefficient for player `false` is exactly offset
by the negative pair coefficient at the half--half root. -/
theorem mobiusCoeff_false_singleton :
    quittingStageMobiusCoeff reward (0 : Payoff Bool) false {false} = 1 := by
  have hpowerset : ({false} : Finset Bool).powerset =
      {∅, {false}} := by decide
  simp [quittingStageMobiusCoeff, quittingStageCenteredCoalGame,
    CoalGame.unanimityCoeff, quittingStageCoalitionPayoff, reward, hpowerset]

theorem mobiusCoeff_false_pair :
    quittingStageMobiusCoeff reward (0 : Payoff Bool) false {false, true} = -2 := by
  have hpowerset : ({false, true} : Finset Bool).powerset =
      {∅, {false}, {true}, {false, true}} := by decide
  unfold quittingStageMobiusCoeff CoalGame.unanimityCoeff
  rw [hpowerset]
  rw [Finset.sum_insert (by decide :
    (∅ : Finset Bool) ∉ ({ {false}, {true}, {false, true} } : Finset (Finset Bool)))]
  rw [Finset.sum_insert (by decide :
    ({false} : Finset Bool) ∉ ({ {true}, {false, true} } : Finset (Finset Bool)))]
  rw [Finset.sum_insert (by decide :
    ({true} : Finset Bool) ∉ ({ {false, true} } : Finset (Finset Bool)))]
  simp [quittingStageCenteredCoalGame, quittingStageCoalitionPayoff, reward]

/-- A positive played Möbius incidence can coexist with zero endpoint gain. -/
theorem positive_singleton_incidence_eq_half :
    quittingPlayedPositiveMobiusIncidenceTerm reward (0 : Payoff Bool)
        root false {false} = 1 / 2 := by
  rw [quittingPlayedPositiveMobiusIncidenceTerm]
  norm_num [mobiusCoeff_false_singleton, root, PMF.uniformOfFintype_apply,
    hazardOfRoot]

/-- The cancelling pair incidence is also positive, in the opposite action
orientation. -/
theorem negative_pair_incidence_eq_half :
    quittingPlayedNegativeMobiusIncidenceTerm reward (0 : Payoff Bool)
        root false {false, true} = 1 / 2 := by
  rw [quittingPlayedNegativeMobiusIncidenceTerm]
  norm_num [mobiusCoeff_false_pair, root, PMF.uniformOfFintype_apply,
    hazardOfRoot]

theorem endpointDifference_false_eq_zero :
    quittingRootEndpointDifference reward (0 : Payoff Bool) root false = 0 := by
  rw [quittingRootEndpointDifference, false_quitPayoff_root_zero,
    false_continuePayoff_root_zero]
  norm_num

/-- Hence raw incidence positivity does not imply even a strict one-stage
unilateral improvement, let alone a quantitative legal deviation. -/
theorem coordinateNashDefect_false_eq_zero :
    quittingRootCoordinateNashDefect reward (0 : Payoff Bool) root false = 0 := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart,
    endpointDifference_false_eq_zero]
  norm_num

end QuittingMobiusIncidenceCancellationRegression

/-- Any gain obtained by a finite-cutoff policy interpolation is still an
ordinary unilateral behavioral gain and is therefore already bounded by the
player's initial best-response debt.  Thus policy interpolation can expose
the defect occupation, but cannot by itself beat the semantic envelope from
which that debt was defined. -/
theorem quittingTerminalPayoff_update_sub_le_terminalSemanticDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalPayoff reward
          (Function.update profile who deviation) who -
        quittingTerminalPayoff reward profile who ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
  have hbest :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile who deviation hM hreward
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  exact sub_le_sub_right hbest _

end GameTheory
