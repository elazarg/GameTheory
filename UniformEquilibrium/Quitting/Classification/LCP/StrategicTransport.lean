/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.Normalization
import GameTheory.Concepts.Stochastic.Models.Quitting.Asymptotic

/-!
# Strategic transport across playerwise solo normalization

The normalized source game has the same histories and actions as the repository
quitting game, but its nontermination payoff is generally nonzero.  This file
therefore evaluates the normalized table directly on a repository behavior
profile: absorbed terminal masses receive the translated terminal rewards and
the residual nonabsorption mass receives the translated `never` payoff.

The resulting payoff is exactly the repository terminal payoff minus the
player's solo baseline, for every profile.  Consequently every unilateral
payoff difference, and hence every terminal approximate-Nash inequality, is
preserved in both directions.  This is the strategic normalization adapter;
it is not left implicit in the source interfaces.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Total limiting mass assigned to absorbing terminal states.  The remaining
mass is the probability of nontermination. -/
def quittingTerminalAbsorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  ∑ S : {S : Finset ι // S.Nonempty},
    quittingAbsorbedMassLimit reward profile S

/-- Expected payoff of the playerwise normalized table on a repository
behavior profile, including its translated nontermination payoff. -/
def normalizedQuittingTerminalPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) : ℝ :=
  (∑ S : {S : Finset ι // S.Nonempty},
      quittingAbsorbedMassLimit reward profile S *
        (normalizedQuittingPayoffTable reward).terminal S who) +
    (1 - quittingTerminalAbsorptionMass reward profile) *
      (normalizedQuittingPayoffTable reward).never who

/-- **Exact strategic translation.**  Every profile payoff is shifted by the
same playerwise solo baseline, including profiles that fail to absorb. -/
theorem normalizedQuittingTerminalPayoff_eq_sub_soloBaseline
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    normalizedQuittingTerminalPayoff reward profile who =
      quittingTerminalPayoff reward profile who -
        quittingSoloBaseline reward who := by
  classical
  let mass : {S : Finset ι // S.Nonempty} → ℝ :=
    fun S => quittingAbsorbedMassLimit reward profile S
  let baseline : ℝ := quittingSoloBaseline reward who
  have hterminal :
      (∑ S, mass S *
          (normalizedQuittingPayoffTable reward).terminal S who) =
        (∑ S, mass S * reward S who) +
          (∑ S, mass S) * (-baseline) := by
    calc
      (∑ S, mass S *
          (normalizedQuittingPayoffTable reward).terminal S who) =
          ∑ S, mass S * (reward S who + (-baseline)) := by
            apply Finset.sum_congr rfl
            intro S hS
            simp [normalizedQuittingPayoffTable,
              QuittingPayoffTable.translate,
              repositoryQuittingPayoffTable, baseline,
              quittingSoloBaseline]
      _ = (∑ S, mass S * reward S who) +
          ∑ S, mass S * (-baseline) := by
            simp_rw [mul_add]
            exact Finset.sum_add_distrib
      _ = (∑ S, mass S * reward S who) +
          (∑ S, mass S) * (-baseline) := by
            rw [Finset.sum_mul]
  unfold normalizedQuittingTerminalPayoff quittingTerminalPayoff
    quittingTerminalAbsorptionMass
  change
    (∑ S, mass S *
        (normalizedQuittingPayoffTable reward).terminal S who) +
      (1 - ∑ S, mass S) *
        (normalizedQuittingPayoffTable reward).never who =
      (∑ S, mass S * reward S who) - baseline
  rw [hterminal]
  have hnever :
      (normalizedQuittingPayoffTable reward).never who = -baseline := by
    simp [normalizedQuittingPayoffTable, QuittingPayoffTable.translate,
      repositoryQuittingPayoffTable, baseline, quittingSoloBaseline]
  rw [hnever]
  ring

/-- Playerwise translation preserves every terminal approximate-Nash
inequality, profile by profile and at the same error. -/
theorem isεAsymptoticNash_normalized_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (ε : ℝ) (profile : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).IsεAsymptoticNash
        (normalizedQuittingTerminalPayoff reward) ε profile ↔
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile := by
  constructor
  · intro hnash who deviation
    have h := hnash who deviation
    rw [normalizedQuittingTerminalPayoff_eq_sub_soloBaseline,
      normalizedQuittingTerminalPayoff_eq_sub_soloBaseline] at h
    linarith
  · intro hnash who deviation
    have h := hnash who deviation
    rw [normalizedQuittingTerminalPayoff_eq_sub_soloBaseline,
      normalizedQuittingTerminalPayoff_eq_sub_soloBaseline]
    linarith

end QuittingLCPClassification
end GameTheory
