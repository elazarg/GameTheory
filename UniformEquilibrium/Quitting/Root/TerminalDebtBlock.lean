/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.SurvivalWeightedObstructionAction
import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix

/-!
# Literal terminal debt as a survival-block action

For one player at one exact root prefix, the block survival is the probability
that every opponent Continues and the block charge is the positive part of the
root's immediate Quit-minus-Continue endpoint difference.  The literal debt
of the prefixed profile is exactly the positive-part action of this block on
the continuation debt.

This is a playerwise construction: different players have different deleted
survival factors.  All values and best-response caps come from the same actual
continuation profile.
-/

noncomputable section

namespace GameTheory

open Math.Probability
open Math.SurvivalWeightedObstruction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Positive immediate-exercise premium at a quitting root. -/
def quittingRootExercisePremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) : ℝ :=
  max 0 (quittingRootEndpointDifference reward tail root who)

theorem quittingRootExercisePremium_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    0 ≤ quittingRootExercisePremium reward tail root who :=
  le_max_left _ _

/-- Deleted Continue mass is at most every displayed opponent's Continue
probability. -/
theorem quittingRootOpponentContinueMass_le_continueProbability_of_ne
    (root : ι → PMF Bool) {who other : ι} (hne : other ≠ who) :
    quittingRootOpponentContinueMass root who ≤
      (root other false).toReal := by
  have hmass := quittingStationaryContinueMass_le_ownContinueProbability
    (Function.update root who (PMF.pure false)) other
  simpa [quittingRootOpponentContinueMass, Function.update_of_ne hne] using
    hmass

/-- An opponent's displayed Quit probability is bounded by the absorption
hazard seen after forcing the selected player to Continue. -/
theorem quittingRoot_quitProbability_le_opponentAbsorptionMass_of_ne
    (root : ι → PMF Bool) {who other : ι} (hne : other ≠ who) :
    (root other true).toReal ≤
      quittingRootOpponentAbsorptionMass root who := by
  have hcontinue :=
    quittingRootOpponentContinueMass_le_continueProbability_of_ne root hne
  have hsum := quittingRoot_continueProbability_add_quitProbability root other
  rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass] at hcontinue
  linarith

/-- Playerwise survival block attached to one literal root prefix. -/
def quittingLiteralTerminalDebtBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (root : ι → PMF Bool) (who : ι) : Block Unit where
  survival := quittingRootOpponentContinueMass root who
  survival_nonneg := quittingRootOpponentContinueMass_nonneg root who
  survival_le_one := quittingRootOpponentContinueMass_le_one root who
  charge :=
    { value := fun _ => quittingRootExercisePremium reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who
      nonneg := fun _ => quittingRootExercisePremium_nonneg reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who }

@[simp]
theorem quittingLiteralTerminalDebtBlock_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (root : ι → PMF Bool) (who : ι) :
    (quittingLiteralTerminalDebtBlock reward continuation root who).survival =
      quittingRootOpponentContinueMass root who := rfl

@[simp]
theorem quittingLiteralTerminalDebtBlock_charge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (root : ι → PMF Bool) (who : ι) :
    (quittingLiteralTerminalDebtBlock reward continuation root who).charge.value
        () =
      quittingRootExercisePremium reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who := rfl

/-- Exact one-step positive-part normal form for literal terminal debt. -/
theorem quittingTerminalDeviationDebt_rootThenContinuation_eq_blockAct
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player)
      0 root) :
    quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward root continuation) who =
      (quittingLiteralTerminalDebtBlock reward continuation root who).act
        ()
        (quittingTerminalDeviationDebt reward continuation who) := by
  let base : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  let debt := quittingTerminalDeviationDebt reward continuation who
  let quitValue := quittingRootQuitPayoff reward base root who
  let continueValue := quittingRootContinuePayoff reward base root who
  let survived := quittingRootOpponentContinueMass root who * debt
  have hdebt : 0 ≤ debt :=
    quittingTerminalDeviationDebt_nonneg reward continuation who hM hreward
  have hsurvived : 0 ≤ survived :=
    mul_nonneg (quittingRootOpponentContinueMass_nonneg root who) hdebt
  have hrecursion := quittingTerminalDeviationDebt_rootThenContinuation_eq
    reward root continuation who hM hreward hnash
  rw [hrecursion]
  change max quitValue (continueValue + survived) - max quitValue continueValue =
    max 0 (survived - max 0 (quitValue - continueValue))
  exact Block.max_add_sub_max_eq_posPart_sub_posPart
    quitValue continueValue survived hsurvived

/-- Exact one-step utilization law.  Literal debt loss is the sum of debt
killed by opponent absorption and the positive endpoint premium actually
consumed from survived debt. -/
theorem quittingTerminalDebt_utilization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player)
      0 root) :
    quittingTerminalDeviationDebt reward continuation who -
        quittingTerminalDeviationDebt reward
          (quittingRootThenContinuationProfile reward root continuation) who =
      quittingRootOpponentAbsorptionMass root who *
          quittingTerminalDeviationDebt reward continuation who +
        min
          (quittingRootOpponentContinueMass root who *
            quittingTerminalDeviationDebt reward continuation who)
          (quittingRootExercisePremium reward
            (fun player => quittingTerminalPayoff reward continuation player)
            root who) := by
  have hdebt := quittingTerminalDeviationDebt_nonneg
    reward continuation who hM hreward
  rw [quittingTerminalDeviationDebt_rootThenContinuation_eq_blockAct
    reward root continuation who hM hreward hnash]
  have haccount := Block.debt_sub_act_eq_killed_add_min
    (quittingLiteralTerminalDebtBlock reward continuation root who)
    () hdebt
  simpa [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass] using
    haccount

/-- Nonnegative playerwise debt utilization at one literal exact prefix. -/
def quittingTerminalDebtUtilization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) : ℝ :=
  quittingRootOpponentAbsorptionMass root who *
      quittingTerminalDeviationDebt reward continuation who +
    min
      (quittingRootOpponentContinueMass root who *
        quittingTerminalDeviationDebt reward continuation who)
      (quittingRootExercisePremium reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who)

theorem quittingTerminalDebtUtilization_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    0 ≤ quittingTerminalDebtUtilization reward root continuation who := by
  unfold quittingTerminalDebtUtilization
  apply add_nonneg
  · exact mul_nonneg (quittingRootOpponentAbsorptionMass_nonneg root who)
      (quittingTerminalDeviationDebt_nonneg reward continuation who hM hreward)
  · apply le_min
    · exact mul_nonneg (quittingRootOpponentContinueMass_nonneg root who)
        (quittingTerminalDeviationDebt_nonneg reward continuation who hM hreward)
    · exact quittingRootExercisePremium_nonneg reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who

/-- Summed Lyapunov identity for one literal exact prefix. -/
theorem sum_quittingTerminalDebt_sub_prefixed_eq_sum_utilization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player)
      0 root) :
    (∑ who, quittingTerminalDeviationDebt reward continuation who) -
        ∑ who, quittingTerminalDeviationDebt reward
          (quittingRootThenContinuationProfile reward root continuation) who =
      ∑ who, quittingTerminalDebtUtilization reward root continuation who := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro who _
  exact quittingTerminalDebt_utilization
    reward root continuation who hM hreward hnash

/-- A small total debt drop forces a macroscopic debtor to see little
opponent absorption.  The estimate is division-free. -/
theorem quittingRootOpponentAbsorptionMass_mul_debtFloor_le_of_sumDebtDrop_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (debtFloor error : ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player)
      0 root)
    (hfloor : debtFloor ≤
      quittingTerminalDeviationDebt reward continuation who)
    (hdrop :
      (∑ player, quittingTerminalDeviationDebt reward continuation player) -
          ∑ player, quittingTerminalDeviationDebt reward
            (quittingRootThenContinuationProfile reward root continuation)
            player ≤ error) :
    quittingRootOpponentAbsorptionMass root who * debtFloor ≤ error := by
  have hterm_le_sum :
      quittingTerminalDebtUtilization reward root continuation who ≤
        ∑ player, quittingTerminalDebtUtilization reward root continuation player :=
    Finset.single_le_sum
      (fun player _ => quittingTerminalDebtUtilization_nonneg
        reward root continuation player hM hreward)
      (Finset.mem_univ who)
  have hterm_le_error :
      quittingTerminalDebtUtilization reward root continuation who ≤ error := by
    apply hterm_le_sum.trans
    rw [← sum_quittingTerminalDebt_sub_prefixed_eq_sum_utilization
      reward root continuation hM hreward hnash]
    exact hdrop
  calc
    quittingRootOpponentAbsorptionMass root who * debtFloor ≤
        quittingRootOpponentAbsorptionMass root who *
          quittingTerminalDeviationDebt reward continuation who :=
      mul_le_mul_of_nonneg_left hfloor
        (quittingRootOpponentAbsorptionMass_nonneg root who)
    _ ≤ quittingTerminalDebtUtilization reward root continuation who := by
      unfold quittingTerminalDebtUtilization
      exact le_add_of_nonneg_right <| le_min
        (mul_nonneg (quittingRootOpponentContinueMass_nonneg root who)
          (quittingTerminalDeviationDebt_nonneg reward continuation who hM hreward))
        (quittingRootExercisePremium_nonneg reward
          (fun player => quittingTerminalPayoff reward continuation player)
          root who)
    _ ≤ error := hterm_le_error

/-- Under a genuinely small total drop, the immediate exercise premium of a
macroscopic debtor is itself charged by that drop. -/
theorem quittingRootExercisePremium_le_of_sumDebtDrop_lt_half_debtFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (debtFloor error : ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player)
      0 root)
    (hfloor : debtFloor ≤
      quittingTerminalDeviationDebt reward continuation who)
    (hdrop :
      (∑ player, quittingTerminalDeviationDebt reward continuation player) -
          ∑ player, quittingTerminalDeviationDebt reward
            (quittingRootThenContinuationProfile reward root continuation)
            player ≤ error)
    (hsmall : error < debtFloor / 2) :
    quittingRootExercisePremium reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who ≤ error := by
  have hterm_le_sum :
      quittingTerminalDebtUtilization reward root continuation who ≤
        ∑ player, quittingTerminalDebtUtilization reward root continuation player :=
    Finset.single_le_sum
      (fun player _ => quittingTerminalDebtUtilization_nonneg
        reward root continuation player hM hreward)
      (Finset.mem_univ who)
  have hterm_le_error :
      quittingTerminalDebtUtilization reward root continuation who ≤ error := by
    apply hterm_le_sum.trans
    rw [← sum_quittingTerminalDebt_sub_prefixed_eq_sum_utilization
      reward root continuation hM hreward hnash]
    exact hdrop
  have herror_nonneg : 0 ≤ error :=
    (quittingTerminalDebtUtilization_nonneg
      reward root continuation who hM hreward).trans hterm_le_error
  have habs :=
    quittingRootOpponentAbsorptionMass_mul_debtFloor_le_of_sumDebtDrop_le
      reward root continuation who debtFloor error hM hreward hnash
      hfloor hdrop
  have hsurvived_floor :
      error < quittingRootOpponentContinueMass root who * debtFloor := by
    rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass]
    nlinarith
  have hsurvived :
      error < quittingRootOpponentContinueMass root who *
        quittingTerminalDeviationDebt reward continuation who :=
    hsurvived_floor.trans_le <|
      mul_le_mul_of_nonneg_left hfloor
        (quittingRootOpponentContinueMass_nonneg root who)
  have hmin_le_error :
      min
          (quittingRootOpponentContinueMass root who *
            quittingTerminalDeviationDebt reward continuation who)
          (quittingRootExercisePremium reward
            (fun player => quittingTerminalPayoff reward continuation player)
            root who) ≤ error := by
    calc
      min
          (quittingRootOpponentContinueMass root who *
            quittingTerminalDeviationDebt reward continuation who)
          (quittingRootExercisePremium reward
            (fun player => quittingTerminalPayoff reward continuation player)
            root who) ≤
          quittingTerminalDebtUtilization reward root continuation who := by
        unfold quittingTerminalDebtUtilization
        exact le_add_of_nonneg_left <| mul_nonneg
          (quittingRootOpponentAbsorptionMass_nonneg root who)
          (quittingTerminalDeviationDebt_nonneg reward continuation who hM hreward)
      _ ≤ error := hterm_le_error
  by_contra hpremium
  have hpremium_lt : error < quittingRootExercisePremium reward
      (fun player => quittingTerminalPayoff reward continuation player)
      root who := lt_of_not_ge hpremium
  exact (not_lt_of_ge hmin_le_error) (lt_min hsurvived hpremium_lt)

/-- Near preservation of a macroscopic debtor bounds every opponent's Quit
probability. -/
theorem quittingRoot_quitProbability_mul_debtFloor_le_of_sumDebtDrop_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {who other : ι} (hne : other ≠ who) (debtFloor error : ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player)
      0 root)
    (hfloor_nonneg : 0 ≤ debtFloor)
    (hfloor : debtFloor ≤
      quittingTerminalDeviationDebt reward continuation who)
    (hdrop :
      (∑ player, quittingTerminalDeviationDebt reward continuation player) -
          ∑ player, quittingTerminalDeviationDebt reward
            (quittingRootThenContinuationProfile reward root continuation)
            player ≤ error) :
    (root other true).toReal * debtFloor ≤ error := by
  calc
    (root other true).toReal * debtFloor ≤
        quittingRootOpponentAbsorptionMass root who * debtFloor :=
      mul_le_mul_of_nonneg_right
        (quittingRoot_quitProbability_le_opponentAbsorptionMass_of_ne root hne)
        hfloor_nonneg
    _ ≤ error :=
      quittingRootOpponentAbsorptionMass_mul_debtFloor_le_of_sumDebtDrop_le
        reward root continuation who debtFloor error hM hreward hnash
        hfloor hdrop

/-- If two distinct debt coordinates are macroscopic, every marginal is
quantitatively close to Continue. -/
theorem quittingRoot_all_quitProbability_mul_debtFloor_le_of_two_debtors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {first second : ι} (hdistinct : first ≠ second)
    (debtFloor error : ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player)
      0 root)
    (hfloor_nonneg : 0 ≤ debtFloor)
    (hfirst : debtFloor ≤
      quittingTerminalDeviationDebt reward continuation first)
    (hsecond : debtFloor ≤
      quittingTerminalDeviationDebt reward continuation second)
    (hdrop :
      (∑ player, quittingTerminalDeviationDebt reward continuation player) -
          ∑ player, quittingTerminalDeviationDebt reward
            (quittingRootThenContinuationProfile reward root continuation)
            player ≤ error) :
    ∀ player, (root player true).toReal * debtFloor ≤ error := by
  intro player
  by_cases hplayer : player = first
  · subst player
    exact quittingRoot_quitProbability_mul_debtFloor_le_of_sumDebtDrop_le
      reward root continuation hdistinct debtFloor error hM hreward hnash
      hfloor_nonneg hsecond hdrop
  · exact quittingRoot_quitProbability_mul_debtFloor_le_of_sumDebtDrop_le
      reward root continuation hplayer debtFloor error hM hreward hnash
      hfloor_nonneg hfirst hdrop

/-- A positive literal debt is preserved by an exact root precisely when
every opponent Continues surely and the immediate exercise premium is zero.
-/
theorem quittingTerminalDeviationDebt_rootThenContinuation_eq_self_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player)
      0 root)
    (hdebt : 0 < quittingTerminalDeviationDebt reward continuation who) :
    quittingTerminalDeviationDebt reward
          (quittingRootThenContinuationProfile reward root continuation) who =
        quittingTerminalDeviationDebt reward continuation who ↔
      quittingRootOpponentContinueMass root who = 1 ∧
        quittingRootExercisePremium reward
          (fun player => quittingTerminalPayoff reward continuation player)
          root who = 0 := by
  rw [quittingTerminalDeviationDebt_rootThenContinuation_eq_blockAct
    reward root continuation who hM hreward hnash]
  exact Block.act_eq_self_iff_of_pos
    (quittingLiteralTerminalDebtBlock reward continuation root who)
    () hdebt

end GameTheory
