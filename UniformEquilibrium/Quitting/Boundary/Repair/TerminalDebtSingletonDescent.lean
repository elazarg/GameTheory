/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailUniformAbsorption
import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix

/-!
# Strict terminal-debt descent from a singleton gap

An exact root prefix contracts literal terminal deviation debt.  If one
player's singleton reward exceeds the actual continuation payoff by a fixed
positive amount, the contraction is uniformly strict.  Large opponent
absorption contracts the old deviation opportunity; small opponent absorption
makes pure Quit strictly optimal at the new root.

The continuation in every theorem is an actual behavior profile.  Applying
the result to a compactified or conditioned boundary requires a separate
literal-payoff realization theorem.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual singleton gap is bounded below by the root endpoint gain,
up to four reward bounds times opponent absorption. -/
theorem singletonGap_ge_quittingRootEndpointDifference_sub_four_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    quittingRootEndpointDifference reward
          (fun player => quittingTerminalPayoff reward continuation player)
          root who -
        4 * M * quittingRootOpponentAbsorptionMass root who ≤
      reward (quittingSingletonTerminal who) who -
        quittingTerminalPayoff reward continuation who := by
  let opponentAbsorption := quittingRootOpponentAbsorptionMass root who
  let singletonGap := reward (quittingSingletonTerminal who) who -
    quittingTerminalPayoff reward continuation who
  let joining := quittingOutsiderJoiningContribution reward root who
  have hopponentNonneg : 0 ≤ opponentAbsorption :=
    quittingRootOpponentAbsorptionMass_nonneg root who
  have hactualAbs := abs_quittingTerminalPayoff_le
    reward continuation who hM hreward
  have hsingletonAbs := hreward (quittingSingletonTerminal who) who
  have hgapAbs : |singletonGap| ≤ 2 * M := by
    dsimp [singletonGap]
    calc
      |reward (quittingSingletonTerminal who) who -
          quittingTerminalPayoff reward continuation who| ≤
          |reward (quittingSingletonTerminal who) who| +
            |quittingTerminalPayoff reward continuation who| := abs_sub _ _
      _ ≤ M + M := add_le_add hsingletonAbs hactualAbs
      _ = 2 * M := by ring
  have hweightedGapLower : -(2 * M * opponentAbsorption) ≤
      opponentAbsorption * singletonGap := by
    have hlower := neg_le_of_abs_le hgapAbs
    have hmul := mul_le_mul_of_nonneg_left hlower hopponentNonneg
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  have hjoiningAbs :=
    abs_quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
      reward root who hM hreward
  have hjoiningUpper : joining ≤ 2 * M * opponentAbsorption := by
    exact (le_abs_self joining).trans (by simpa [joining] using hjoiningAbs)
  have hdecomposition :=
    quittingRootEndpointDifference_eq_outsiderNever
      reward (fun player => quittingTerminalPayoff reward continuation player)
        root who
  rw [show quittingRootAbsorptionMass
      (Function.update root who (PMF.pure false)) = opponentAbsorption by rfl]
    at hdecomposition
  change _ - 4 * M * opponentAbsorption ≤ singletonGap
  rw [hdecomposition]
  nlinarith

/-- A positive endpoint gain and sufficiently small opponent absorption give
a positive gap between singleton reward and the actual suffix payoff. -/
theorem half_le_singletonGap_of_endpointDifference_and_small_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (root : ι → PMF Bool) (who : ι) {M delta : ℝ}
    (hM : 0 < M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hendpoint : delta ≤ quittingRootEndpointDifference reward
      (fun player => quittingTerminalPayoff reward continuation player)
      root who)
    (habsorption : quittingRootOpponentAbsorptionMass root who ≤
      delta / (8 * M)) :
    delta / 2 ≤ reward (quittingSingletonTerminal who) who -
      quittingTerminalPayoff reward continuation who := by
  have hgap :=
    singletonGap_ge_quittingRootEndpointDifference_sub_four_mul
      reward continuation root who hM.le hreward
  have hdenom : 0 < 8 * M := by positivity
  have hcharge : 8 * M * quittingRootOpponentAbsorptionMass root who ≤
      delta := by
    have h := (le_div_iff₀ hdenom).mp habsorption
    nlinarith
  nlinarith

/-- A singleton gap controls the exact Quit-minus-Continue endpoint up to
four reward bounds times opponent absorption. -/
theorem quittingRootEndpointDifference_ge_singletonGap_sub_four_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (root : ι → PMF Bool) (who : ι) {M gap : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsingleton : gap ≤ reward (quittingSingletonTerminal who) who -
      quittingTerminalPayoff reward continuation who) :
    gap - 4 * M * quittingRootOpponentAbsorptionMass root who ≤
      quittingRootEndpointDifference reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who := by
  let opponentAbsorption := quittingRootOpponentAbsorptionMass root who
  let singleton := reward (quittingSingletonTerminal who) who
  let actual := quittingTerminalPayoff reward continuation who
  have hactualAbs : |actual| ≤ M := by
    exact abs_quittingTerminalPayoff_le reward continuation who hM hreward
  have hsingletonAbs : |singleton| ≤ M :=
    hreward (quittingSingletonTerminal who) who
  have hgapBound : gap ≤ 2 * M := by
    have hsingletonUpper := (le_abs_self singleton).trans hsingletonAbs
    have hactualLower := neg_le_of_abs_le hactualAbs
    dsimp [singleton, actual] at hsingletonUpper hactualLower
    linarith
  have hopponentNonneg : 0 ≤ opponentAbsorption := by
    exact quittingRootOpponentAbsorptionMass_nonneg root who
  have hopponentLeOne : opponentAbsorption ≤ 1 := by
    exact quittingRootOpponentAbsorptionMass_le_one root who
  have hjoiningAbs :=
    abs_quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
      reward root who hM hreward
  have hjoiningLower : -(2 * M * opponentAbsorption) ≤
      quittingOutsiderJoiningContribution reward root who := by
    simpa [opponentAbsorption] using neg_le_of_abs_le hjoiningAbs
  have hsurvivalNonneg : 0 ≤ 1 - opponentAbsorption := by linarith
  have hweightedGap : (1 - opponentAbsorption) * gap ≤
      (1 - opponentAbsorption) * (singleton - actual) := by
    exact mul_le_mul_of_nonneg_left (by simpa [singleton, actual] using hsingleton)
      hsurvivalNonneg
  have hdecomposition :=
    quittingRootEndpointDifference_eq_outsiderNever
      reward (fun player => quittingTerminalPayoff reward continuation player)
        root who
  rw [show quittingRootAbsorptionMass
      (Function.update root who (PMF.pure false)) = opponentAbsorption by rfl]
    at hdecomposition
  change gap - 4 * M * opponentAbsorption ≤ _
  calc
    gap - 4 * M * opponentAbsorption ≤
        (1 - opponentAbsorption) * gap -
          2 * M * opponentAbsorption := by
      nlinarith [mul_nonneg hopponentNonneg (sub_nonneg.mpr hgapBound)]
    _ ≤ (1 - opponentAbsorption) * (singleton - actual) +
          quittingOutsiderJoiningContribution reward root who := by
      linarith
    _ = quittingRootEndpointDifference reward
          (fun player => quittingTerminalPayoff reward continuation player)
          root who := by
      simpa [singleton, actual] using hdecomposition.symm

/-- Quantitative strict descent of one player's literal terminal debt under
every exact root Nash prefix against the continuation's literal payoff. -/
theorem quittingTerminalDeviationDebt_rootThenContinuation_le_sub_min
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) {M gap : ℝ} (hM : 0 ≤ M) (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsingleton : gap ≤ reward (quittingSingletonTerminal who) who -
      quittingTerminalPayoff reward continuation who)
    (hnash : IsεQuittingRootEndpointNash reward
      (fun player => quittingTerminalPayoff reward continuation player)
      0 root) :
    quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward root continuation) who ≤
      quittingTerminalDeviationDebt reward continuation who -
        min
          ((gap / (8 * M)) *
            quittingTerminalDeviationDebt reward continuation who)
          (gap / 2) := by
  let base : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  let debt := quittingTerminalDeviationDebt reward continuation who
  let opponentAbsorption := quittingRootOpponentAbsorptionMass root who
  let opponentContinue := quittingRootOpponentContinueMass root who
  let threshold := gap / (8 * M)
  let quitValue := quittingRootQuitPayoff reward base root who
  let continueValue := quittingRootContinuePayoff reward base root who
  have hactualAbs : |base who| ≤ M := by
    exact abs_quittingTerminalPayoff_le reward continuation who hM hreward
  have hsingletonAbs :
      |reward (quittingSingletonTerminal who) who| ≤ M :=
    hreward (quittingSingletonTerminal who) who
  have hgapBound : gap ≤ 2 * M := by
    have hsingletonUpper :=
      (le_abs_self (reward (quittingSingletonTerminal who) who)).trans
        hsingletonAbs
    have hactualLower := neg_le_of_abs_le hactualAbs
    dsimp [base] at hactualLower
    linarith
  have hMpos : 0 < M := by linarith
  have hthresholdPos : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hthresholdLeOne : threshold ≤ 1 := by
    dsimp [threshold]
    apply (div_le_one (by positivity : 0 < 8 * M)).2
    linarith
  have hdebtNonneg : 0 ≤ debt := by
    exact quittingTerminalDeviationDebt_nonneg
      reward continuation who hM hreward
  have hopponentNonneg : 0 ≤ opponentAbsorption :=
    quittingRootOpponentAbsorptionMass_nonneg root who
  have hopponentContinueNonneg : 0 ≤ opponentContinue :=
    quittingRootOpponentContinueMass_nonneg root who
  have hopponentContinueLeOne : opponentContinue ≤ 1 :=
    quittingRootOpponentContinueMass_le_one root who
  have hcomplement : opponentContinue = 1 - opponentAbsorption := by
    exact quittingRootOpponentContinueMass_eq_one_sub_absorptionMass root who
  have hnashRoot : IsεQuittingRootNash reward base 0 root := by
    exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward base 0 root).mp hnash
  have hrecursion :=
    quittingTerminalDeviationDebt_rootThenContinuation_eq
      reward root continuation who hM hreward hnashRoot
  have hmonotone :=
    quittingTerminalDeviationDebt_rootThenContinuation_le
      reward root continuation who hM hreward hnashRoot
  have hendpoint : gap - 4 * M * opponentAbsorption ≤
      quitValue - continueValue := by
    simpa [base, quitValue, continueValue, opponentAbsorption,
      quittingRootEndpointDifference] using
      quittingRootEndpointDifference_ge_singletonGap_sub_four_mul
        reward continuation root who hM hreward hsingleton
  by_cases hlarge : threshold ≤ opponentAbsorption
  · have hcontinueBound : opponentContinue ≤ 1 - threshold := by
      rw [hcomplement]
      linarith
    have hscaled : opponentContinue * debt ≤ (1 - threshold) * debt :=
      mul_le_mul_of_nonneg_right hcontinueBound hdebtNonneg
    have hmin : min (threshold * debt) (gap / 2) ≤ threshold * debt :=
      min_le_left _ _
    change quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward root continuation) who ≤
      debt - min (threshold * debt) (gap / 2)
    change quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward root continuation) who ≤
      opponentContinue * debt at hmonotone
    linarith
  · have hsmall : opponentAbsorption < threshold := lt_of_not_ge hlarge
    have hdenom : 0 < 8 * M := by positivity
    have hscaledAbsorption : opponentAbsorption * (8 * M) < gap := by
      exact (lt_div_iff₀ hdenom).mp (by simpa [threshold] using hsmall)
    have hendpointStrict : gap / 2 < quitValue - continueValue := by
      nlinarith
    have hquitDominates : continueValue ≤ quitValue := by linarith
    have hminThreshold : min (threshold * debt) (gap / 2) ≤
        threshold * debt := min_le_left _ _
    have hminGap : min (threshold * debt) (gap / 2) ≤ gap / 2 :=
      min_le_right _ _
    have hthresholdDebtLe : threshold * debt ≤ debt := by
      nlinarith
    change quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward root continuation) who ≤
      debt - min (threshold * debt) (gap / 2)
    rw [hrecursion]
    change max quitValue (continueValue + opponentContinue * debt) -
        max quitValue continueValue ≤
      debt - min (threshold * debt) (gap / 2)
    rw [max_eq_left hquitDominates]
    by_cases hnew : continueValue + opponentContinue * debt ≤ quitValue
    · rw [max_eq_left hnew]
      nlinarith
    · have hnew' : quitValue ≤ continueValue + opponentContinue * debt :=
        le_of_not_ge hnew
      rw [max_eq_right hnew']
      have hcontinueDebt : opponentContinue * debt ≤ debt :=
        mul_le_of_le_one_left hdebtNonneg hopponentContinueLeOne
      linarith

end GameTheory
