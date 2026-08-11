/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashChronology
import UniformEquilibrium.Quitting.Boundary.Repair.LocalGlobalCounterexample
import UniformEquilibrium.Quitting.Cycles.ConditionedPeriodicRenewal

/-!
# Debt descent versus renewal drift for cap--Nash prefixes

Long-window periodic renewal gives honest profiles whose prescribed payoffs
approach a conditioned target.  Backward cap--Nash prefixing gives honest
descendants and scales total debt exactly.  The two operations do not commute
for free: a fixed proportional debt descent requires a fixed amount of prefix
absorption, while the available payoff-return estimate is only linear in that
same absorption budget.

This file records the exact quantitative tradeoff.  It also gives an honest
period-one regression in which the renewal profile has debt strictly above the
global infimum but the all-Continue root is already exact Nash against its cap.
Repeatedly choosing that legitimate cap--Nash root produces no descent at all.
Thus cap--Nash iteration needs a root-selection or conditioned-cancellation
theorem; mixed Nash existence alone cannot close renewal tightness.
-/

noncomputable section

namespace GameTheory

open Math.Probability StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## The exact descent/absorption tradeoff -/

/-- Any cap--Nash stack which lowers total debt from `D` to at most `target`
must spend at least the relative debt drop `(D-target)/D` in unweighted
one-stage absorption. -/
theorem debtDrop_div_terminalDebt_le_capNashStackAbsorptionSum
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (target : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hstack : IsQuittingCapNashRootStack reward roots terminal)
    (hdebt : 0 < quittingTerminalDebtSum reward terminal)
    (hdescendant : quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward roots terminal) ≤ target) :
    (quittingTerminalDebtSum reward terminal - target) /
        quittingTerminalDebtSum reward terminal ≤
      quittingCapNashStackAbsorptionSum roots := by
  have hscale := quittingTerminalDebtSum_capNashRootStack_eq
    (reward := reward) roots terminal hM hreward hstack
  have hproductGap := one_sub_capNashStackContinueProduct_le_absorptionSum
    roots
  have hscaled : quittingCapNashStackContinueProduct roots *
      quittingTerminalDebtSum reward terminal ≤ target := by
    rw [← hscale]
    exact hdescendant
  apply (div_le_iff₀ hdebt).2
  have hdebtNonneg := hdebt.le
  nlinarith

/-- Specialization to a descendant within `epsilon` of the global literal
debt infimum. -/
theorem debtExcess_sub_error_div_debt_le_capNashStackAbsorptionSum
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (epsilon : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hstack : IsQuittingCapNashRootStack reward roots terminal)
    (hdebt : 0 < quittingTerminalDebtSum reward terminal)
    (hnear : quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward roots terminal) ≤
      quittingTerminalDebtSumInf reward + epsilon) :
    (quittingTerminalDebtSum reward terminal -
          quittingTerminalDebtSumInf reward - epsilon) /
        quittingTerminalDebtSum reward terminal ≤
      quittingCapNashStackAbsorptionSum roots := by
  have hbound := debtDrop_div_terminalDebt_le_capNashStackAbsorptionSum
    (reward := reward) roots terminal
      (quittingTerminalDebtSumInf reward + epsilon)
      hM hreward hstack hdebt hnear
  simpa [sub_add_eq_sub_sub] using hbound

/-! ## What the standard payoff estimate preserves -/

omit [DecidableEq ι] in
/-- Cap--Nash prefixing preserves any supplied comparison target only up to
the terminal comparison error plus the root word's absorption budget.  This
is the direct interface for the honest periodized renewal profiles. -/
theorem abs_capNashRootStack_payoff_sub_comparison_le
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (comparison : Payoff ι) (who : ι)
    {M error : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hterminal : |quittingTerminalPayoff reward terminal who -
      comparison who| ≤ error) :
    |quittingTerminalPayoff reward
          (quittingLiteralRootStackProfile reward roots terminal) who -
        comparison who| ≤
      error + 2 * M * quittingCapNashStackAbsorptionSum roots := by
  calc
    |quittingTerminalPayoff reward
          (quittingLiteralRootStackProfile reward roots terminal) who -
        comparison who| ≤
      |quittingTerminalPayoff reward
          (quittingLiteralRootStackProfile reward roots terminal) who -
        quittingTerminalPayoff reward terminal who| +
      |quittingTerminalPayoff reward terminal who - comparison who| :=
        abs_sub_le _ _ _
    _ ≤ 2 * M * quittingCapNashStackAbsorptionSum roots + error :=
      add_le_add
        (abs_quittingTerminalPayoff_rootStack_sub_terminal_le
          (reward := reward) roots terminal who hM hreward)
        hterminal
    _ = error + 2 * M * quittingCapNashStackAbsorptionSum roots := by ring

/-- The exact normalized absorbing delivery of a finite prefix word.  When
the word absorbs with positive probability, this is its payoff conditional
on absorption before the terminal continuation is reached. -/
def quittingCapNashStackConditionalDelivery
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι) : ℝ :=
  (quittingTerminalPayoff reward
      (quittingLiteralRootStackProfile reward roots terminal) who -
    quittingCapNashStackContinueProduct roots *
      quittingTerminalPayoff reward terminal who) /
    (1 - quittingCapNashStackContinueProduct roots)

omit [DecidableEq ι] in
/-- Exact split of the descendant payoff into prefix absorption and surviving
terminal continuation. -/
theorem quittingTerminalPayoff_capNashRootStack_eq_conditionedSplit
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι)
    (habsorbs : quittingCapNashStackContinueProduct roots < 1) :
    quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward roots terminal) who =
      (1 - quittingCapNashStackContinueProduct roots) *
          quittingCapNashStackConditionalDelivery
            (reward := reward) roots terminal who +
        quittingCapNashStackContinueProduct roots *
          quittingTerminalPayoff reward terminal who := by
  unfold quittingCapNashStackConditionalDelivery
  have hne : 1 - quittingCapNashStackContinueProduct roots ≠ 0 := by
    linarith
  field_simp
  ring

omit [DecidableEq ι] in
/-- Equivalently, all unexpectedly small prescribed-payoff drift during a
nontrivial debt descent is exact cancellation by the prefix's conditioned
absorbing delivery. -/
theorem quittingTerminalPayoff_capNashRootStack_sub_terminal_eq
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι)
    (habsorbs : quittingCapNashStackContinueProduct roots < 1) :
    quittingTerminalPayoff reward
          (quittingLiteralRootStackProfile reward roots terminal) who -
        quittingTerminalPayoff reward terminal who =
      (1 - quittingCapNashStackContinueProduct roots) *
        (quittingCapNashStackConditionalDelivery
            (reward := reward) roots terminal who -
          quittingTerminalPayoff reward terminal who) := by
  rw [quittingTerminalPayoff_capNashRootStack_eq_conditionedSplit
    (reward := reward) roots terminal who habsorbs]
  ring

/-! ## Honest period-one stalling regression -/

/-- Exact terminal Nash bounds every literal debt coordinate by zero. -/
theorem quittingTerminalDeviationDebt_le_zero_of_isZeroAsymptoticNash
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 profile) :
    quittingTerminalDeviationDebt reward profile who ≤ 0 := by
  let values : Set ℝ := Set.range fun deviation :
      (quittingGame reward).BehaviorStrategy who =>
    quittingTerminalPayoff reward (Function.update profile who deviation) who
  have hvalues : values.Nonempty := by
    exact ⟨quittingTerminalPayoff reward
      (Function.update profile who (profile who)) who, profile who, rfl⟩
  have hcap : quittingContinuationBestResponseValue reward profile who ≤
      quittingTerminalPayoff reward profile who := by
    unfold quittingContinuationBestResponseValue
    apply csSup_le hvalues
    rintro value ⟨deviation, rfl⟩
    simpa using hnash who deviation
  unfold quittingTerminalDeviationDebt
  linarith

/-- Under bounded rewards, exact terminal Nash has total literal debt zero. -/
theorem quittingTerminalDebtSum_eq_zero_of_isZeroAsymptoticNash
    (profile : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 profile) :
    quittingTerminalDebtSum reward profile = 0 := by
  apply le_antisymm
  · unfold quittingTerminalDebtSum
    exact (Finset.sum_nonpos fun who _ =>
      quittingTerminalDeviationDebt_le_zero_of_isZeroAsymptoticNash
        (reward := reward) profile who hnash).trans_eq (by simp)
  · unfold quittingTerminalDebtSum
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalDeviationDebt_nonneg reward profile who hM hreward

/-- The local-to-global table is uniformly one-bounded. -/
theorem abs_localGlobalCounterexampleReward_le_one
    (S : {S : Finset Bool // S.Nonempty}) (who : Bool) :
    |localGlobalCounterexampleReward S who| ≤ 1 := by
  unfold localGlobalCounterexampleReward
  split_ifs <;> norm_num

/-- The local-to-global table has global literal total-debt infimum zero. -/
theorem quittingTerminalDebtSumInf_localGlobalCounterexample_eq_zero :
    quittingTerminalDebtSumInf localGlobalCounterexampleReward = 0 := by
  have hzero : quittingTerminalDebtSum localGlobalCounterexampleReward
      (quittingAlwaysContinueProfile localGlobalCounterexampleReward) = 0 :=
    quittingTerminalDebtSum_eq_zero_of_isZeroAsymptoticNash
      (reward := localGlobalCounterexampleReward)
      (quittingAlwaysContinueProfile localGlobalCounterexampleReward)
      (M := 1) (by norm_num) abs_localGlobalCounterexampleReward_le_one
      isAsymptoticNash_quittingAlwaysContinue_localGlobalCounterexample
  apply le_antisymm
  · exact (quittingTerminalDebtSumInf_le
      (reward := localGlobalCounterexampleReward)
      (quittingAlwaysContinueProfile localGlobalCounterexampleReward)
      (M := 1) (by norm_num)
      abs_localGlobalCounterexampleReward_le_one).trans_eq hzero
  · unfold quittingTerminalDebtSumInf
    apply (le_csInf_iff
      (bddBelow_range_quittingTerminalDebtSum
        (reward := localGlobalCounterexampleReward)
        (M := 1) (by norm_num) abs_localGlobalCounterexampleReward_le_one)
      (Set.range_nonempty _)).2
    rintro total ⟨profile, rfl⟩
    unfold quittingTerminalDebtSum
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalDeviationDebt_nonneg
        localGlobalCounterexampleReward profile who
        (M := 1) (by norm_num) abs_localGlobalCounterexampleReward_le_one

/-- Constant live roots presenting the local-to-global profile as an honest
period-one renewal profile. -/
def localGlobalRenewalRoots : ℕ → Bool → PMF Bool :=
  fun _ => localGlobalCounterexampleRoot

/-- The zero-length tail window is the one-phase local-to-global cycle. -/
theorem quittingTailWindowCycle_localGlobalRenewalRoots_zero :
    quittingTailWindowCycle localGlobalRenewalRoots 0 0 =
      fun _ : Fin 1 => localGlobalCounterexampleRoot := by
  funext phase who
  rfl

/-- The supplied high-debt profile is literally the honest cyclic behavior
profile obtained by repeating that one-phase tail window. -/
theorem cyclicBehaviorProfile_tailWindow_localGlobal_eq :
    quittingCyclicBehaviorProfile localGlobalCounterexampleReward
        (quittingTailWindowCycle localGlobalRenewalRoots 0 0) 0 =
      localGlobalCounterexampleProfile := by
  rw [localGlobalCounterexampleProfile_eq_stationary]
  funext who time history
  simp [quittingCyclicBehaviorProfile, quittingRootSequenceProfile,
    quittingCyclicRootSequence,
    quittingTailWindowCycle, localGlobalRenewalRoots,
    StochasticGame.stationaryBehaviorProfile]

/-- The supplied local-to-global profile has cap at least every solo endpoint,
so the all-Continue root is exact Nash against its actual unilateral cap. -/
theorem isZeroQuittingRootNash_allContinue_localGlobal_actualCap :
    IsεQuittingRootNash localGlobalCounterexampleReward
      (fun who => quittingContinuationBestResponseValue
        localGlobalCounterexampleReward localGlobalCounterexampleProfile who)
      0 quittingAllContinueRoot := by
  apply (isZeroQuittingRootNash_allContinue_iff_singleton_le
    localGlobalCounterexampleReward _).2
  intro who
  have hdebt := quittingTerminalDeviationDebt_nonneg
    localGlobalCounterexampleReward localGlobalCounterexampleProfile who
    (M := 1) (by norm_num) abs_localGlobalCounterexampleReward_le_one
  cases who with
  | false =>
      rw [localGlobalCounterexampleReward_singleton_false]
      unfold quittingTerminalDeviationDebt at hdebt
      rw [quittingTerminalPayoff_localGlobalCounterexampleProfile_false]
        at hdebt
      linarith
  | true =>
      rw [localGlobalCounterexampleReward_singleton_true]
      unfold quittingTerminalDeviationDebt at hdebt
      rw [quittingTerminalPayoff_localGlobalCounterexampleProfile_true]
        at hdebt
      linarith

/-- Prefixing this honest profile by the legitimate all-Continue cap--Nash
root leaves its entire prescribed/cap semantic pair unchanged. -/
theorem semanticPair_allContinue_capNashPrefix_localGlobal :
    quittingTerminalSemanticPair localGlobalCounterexampleReward
        (quittingRootThenContinuationProfile localGlobalCounterexampleReward
          quittingAllContinueRoot localGlobalCounterexampleProfile) =
      quittingTerminalSemanticPair localGlobalCounterexampleReward
        localGlobalCounterexampleProfile := by
  rw [quittingTerminalSemanticPair_rootThenContinuation
    localGlobalCounterexampleReward quittingAllContinueRoot
      localGlobalCounterexampleProfile (M := 1) (by norm_num)
      abs_localGlobalCounterexampleReward_le_one]
  apply Prod.ext
  · funext who
    change quittingRootSuccessorPayoff localGlobalCounterexampleReward
      (quittingTerminalSemanticPair localGlobalCounterexampleReward
        localGlobalCounterexampleProfile).1 quittingAllContinueRoot who =
      (quittingTerminalSemanticPair localGlobalCounterexampleReward
        localGlobalCounterexampleProfile).1 who
    rw [quittingRootSuccessorPayoff_eq_endpointMix]
    simp [quittingAllContinueRoot]
  · funext who
    simp only [quittingTerminalSemanticPrefix,
      quittingRootQuitPayoff_allContinueRoot,
      quittingRootContinuePayoff_allContinueRoot, Function.update_self]
    have hsolo :=
      (isZeroQuittingRootNash_allContinue_iff_singleton_le
        localGlobalCounterexampleReward _).1
        isZeroQuittingRootNash_allContinue_localGlobal_actualCap who
    exact max_eq_right hsolo

/-- The stalled profile nevertheless has terminal debt at least one. -/
theorem one_le_terminalDebtSum_localGlobalCounterexample :
    1 ≤ quittingTerminalDebtSum localGlobalCounterexampleReward
      localGlobalCounterexampleProfile := by
  have hfalse : 1 ≤ quittingTerminalDeviationDebt
      localGlobalCounterexampleReward localGlobalCounterexampleProfile false := by
    have hdeviation :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        localGlobalCounterexampleReward localGlobalCounterexampleProfile false
        (quittingAlwaysContinueStrategy localGlobalCounterexampleReward false)
        (M := 1) (by norm_num) abs_localGlobalCounterexampleReward_le_one
    rw [quittingTerminalPayoff_localGlobalCounterexampleDeviation_false]
      at hdeviation
    unfold quittingTerminalDeviationDebt
    rw [quittingTerminalPayoff_localGlobalCounterexampleProfile_false]
    linarith
  have htrue := quittingTerminalDeviationDebt_nonneg
    localGlobalCounterexampleReward localGlobalCounterexampleProfile true
    (M := 1) (by norm_num) abs_localGlobalCounterexampleReward_le_one
  unfold quittingTerminalDebtSum
  simpa using add_le_add htrue hfalse

/-- **Stalling regression.**  An honest period-one renewal profile can have
debt at least one above a zero global infimum while the all-Continue root is a
valid exact cap--Nash prefix and leaves total debt unchanged.  Therefore
iterated mixed-Nash existence does not select a descending cap chronology. -/
theorem localGlobal_periodOne_capNash_stalls_above_inf :
    quittingTerminalDebtSumInf localGlobalCounterexampleReward = 0 ∧
    1 ≤ quittingTerminalDebtSum localGlobalCounterexampleReward
      localGlobalCounterexampleProfile ∧
    IsQuittingCapNashRootStack localGlobalCounterexampleReward
      [quittingAllContinueRoot] localGlobalCounterexampleProfile ∧
    quittingTerminalDebtSum localGlobalCounterexampleReward
        (quittingLiteralRootStackProfile localGlobalCounterexampleReward
          [quittingAllContinueRoot] localGlobalCounterexampleProfile) =
      quittingTerminalDebtSum localGlobalCounterexampleReward
        localGlobalCounterexampleProfile := by
  refine ⟨quittingTerminalDebtSumInf_localGlobalCounterexample_eq_zero,
    one_le_terminalDebtSum_localGlobalCounterexample, ?_, ?_⟩
  · exact ⟨isZeroQuittingRootNash_allContinue_localGlobal_actualCap, trivial⟩
  · rw [quittingLiteralRootStackProfile_cons,
      quittingLiteralRootStackProfile_nil,
      quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
        (reward := localGlobalCounterexampleReward) quittingAllContinueRoot
        localGlobalCounterexampleProfile (M := 1) (by norm_num)
        abs_localGlobalCounterexampleReward_le_one
        isZeroQuittingRootNash_allContinue_localGlobal_actualCap]
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    simp [quittingAllContinueRoot]

end GameTheory
