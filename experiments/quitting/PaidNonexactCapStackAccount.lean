/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import experiments.quitting.CapChangingLawRetainedSquareNoGo
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMacroscopicAtomNashProvenance

/-!
# Paid nonexact cap-stack accounting

An approximate cap root does not evade the debt telescope for free.  At one
literal row, the new total semantic debt is exactly joint survival times the
suffix debt plus the root's total Nash defect against the suffix's behavioral
best-response cap.  Iterating this identity through an arbitrary finite word
gives the sharp account

`Dmin * total absorption <= reset excess + cumulative total Nash defect`.

There is no cardinal loss in this form: the error is already the sum of the
playerwise coordinate defects.  If every coordinate is merely certified
`epsilon`-Nash, the familiar `card players` factor appears.  Thus a summable
error schedule remains debt-budgeted.  Any absorption charge exceeding the
ordinary reset excess by a positive margin must pay at least that margin in
cumulative playerwise Nash defect, or at least the margin divided by the
number of players in common `epsilon` error.

Every suffix below is the literal executable root-stack profile.  Hence the
behavioral cap is recomputed from the actual suffix and the complete terminal
law provenance is retained by construction.  This is an architectural no-go,
not a counterexample-regime closure: paid nonexact prefixing moves the missing
source-matched gain into an explicit error account.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact one-row debt identity for an arbitrary root selected against the
behavioral cap coordinate of a semantic pair.  No Nash hypothesis is used. -/
theorem quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who +
        quittingRootCoordinateNashDefect reward pair.2 root who := by
  have hquit : quittingRootQuitPayoff reward pair.1 root who =
      quittingRootQuitPayoff reward pair.2 root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward pair.1 pair.2 root who
  have hcontinue :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        quittingRootContinuePayoff reward pair.2 root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp
  have hsuccessor := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    reward pair.2 pair.1 root who
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
    quittingRootCoordinateNashDefect
  dsimp only
  rw [hquit, hcontinue]
  linarith

/-- Total-debt version of the arbitrary-root cap identity. -/
theorem quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward root pair) =
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum pair +
        quittingRootTotalNashDefect reward pair.2 root := by
  unfold quittingTerminalSemanticDebtSum quittingRootTotalNashDefect
  simp_rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect
    reward pair root]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Cumulative sum of the exact playerwise Nash defects incurred by a root
word.  Each defect is evaluated against the behavioral cap of its actual
literal executable suffix. -/
def quittingCapStackNashDefectSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    List (ι → PMF Bool) → (quittingGame reward).BehaviorProfile → ℝ
  | [], _ => 0
  | root :: roots, terminal =>
      quittingRootTotalNashDefect reward
          (fun who => quittingContinuationBestResponseValue reward
            (quittingLiteralRootStackProfile reward roots terminal) who)
          root +
        quittingCapStackNashDefectSum reward roots terminal

@[simp]
theorem quittingCapStackNashDefectSum_nil
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingCapStackNashDefectSum reward [] terminal = 0 := rfl

@[simp]
theorem quittingCapStackNashDefectSum_cons
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingCapStackNashDefectSum reward (root :: roots) terminal =
      quittingRootTotalNashDefect reward
          (fun who => quittingContinuationBestResponseValue reward
            (quittingLiteralRootStackProfile reward roots terminal) who)
          root +
        quittingCapStackNashDefectSum reward roots terminal := rfl

/-- Literal specialization of the one-row arbitrary-root cap identity. -/
theorem quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_add_capDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalDebtSum reward
        (quittingRootThenContinuationProfile reward root continuation) =
      quittingStationaryContinueMass root *
          quittingTerminalDebtSum reward continuation +
        quittingRootTotalNashDefect reward
          (fun who => quittingContinuationBestResponseValue reward continuation who)
          root := by
  have hpair := quittingTerminalSemanticPair_rootThenContinuation
    reward root continuation hM hreward
  have hidentity :=
    quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect
      reward (quittingTerminalSemanticPair reward continuation) root
  rw [← hpair] at hidentity
  simpa [quittingTerminalSemanticDebtSum,
    quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
    quittingTerminalDebtSum, quittingTerminalDeviationDebt] using hidentity

/-- **Sharp paid-stack account.**  For every finite word of arbitrary roots,
the positive semantic minimum charges its unweighted absorption sum, up to
the exact cumulative playerwise Nash defect of those same literal rows. -/
theorem semanticMinimum_mul_capStackAbsorptionSum_le_debtDrop_add_defectSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (roots : List (ι → PMF Bool)) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    quittingTerminalSemanticDebtSum minimum *
        quittingCapNashStackAbsorptionSum roots ≤
      quittingTerminalDebtSum reward terminal -
          quittingTerminalDebtSum reward
            (quittingLiteralRootStackProfile reward roots terminal) +
        quittingCapStackNashDefectSum reward roots terminal := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      let suffix := quittingLiteralRootStackProfile reward roots terminal
      let current := quittingRootThenContinuationProfile reward root suffix
      have hminimumLeSuffix : quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalDebtSum reward suffix := by
        have hle := hminimum
          (quittingTerminalSemanticPair reward suffix)
          (quittingTerminalSemanticPair_mem_carrier reward suffix)
        simpa [quittingTerminalSemanticDebtSum,
          quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
          quittingTerminalDebtSum, quittingTerminalDeviationDebt] using hle
      have habsorption : 0 ≤ quittingRootAbsorptionMass root :=
        quittingRootAbsorptionMass_nonneg root
      have hminimumCharge : quittingTerminalSemanticDebtSum minimum *
            quittingRootAbsorptionMass root ≤
          quittingTerminalDebtSum reward suffix *
            quittingRootAbsorptionMass root := by
        exact mul_le_mul_of_nonneg_right hminimumLeSuffix habsorption
      have hstep :=
        quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_add_capDefect
          reward root suffix hM hreward
      have hcomplement : quittingRootAbsorptionMass root =
          1 - quittingStationaryContinueMass root := rfl
      change quittingTerminalSemanticDebtSum minimum *
          (quittingRootAbsorptionMass root +
            quittingCapNashStackAbsorptionSum roots) ≤
        quittingTerminalDebtSum reward terminal -
          quittingTerminalDebtSum reward current +
            (quittingRootTotalNashDefect reward
                (fun who => quittingContinuationBestResponseValue reward suffix who)
                root +
              quittingCapStackNashDefectSum reward roots terminal)
      dsimp only [current]
      dsimp only [suffix] at hminimumCharge hstep ⊢
      rw [hstep]
      rw [hcomplement] at hminimumCharge ⊢
      nlinarith

/-- The final literal stack profile is again an executable carrier point, so
the sharp account is bounded by the reset endpoint's excess above the global
semantic minimum plus the paid Nash-defect account. -/
theorem semanticMinimum_mul_capStackAbsorptionSum_le_semanticBudget_add_defectSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (roots : List (ι → PMF Bool)) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    quittingTerminalSemanticDebtSum minimum *
        quittingCapNashStackAbsorptionSum roots ≤
      quittingTerminalDebtSum reward terminal -
          quittingTerminalSemanticDebtSum minimum +
        quittingCapStackNashDefectSum reward roots terminal := by
  have haccount :=
    semanticMinimum_mul_capStackAbsorptionSum_le_debtDrop_add_defectSum
      reward minimum terminal roots hM hreward hminimum
  have hminimumLeFinal : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward roots terminal) := by
    have hle := hminimum
      (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots terminal))
      (quittingTerminalSemanticPair_mem_carrier reward _)
    simpa [quittingTerminalSemanticDebtSum,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
      quittingTerminalDebtSum, quittingTerminalDeviationDebt] using hle
  linarith

/-- A root word together with a rowwise common `epsilon` certificate, always
evaluated against the behavioral cap of the actual literal suffix. -/
def IsQuittingCapNashRootStackWithErrors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    List (ι → PMF Bool) → List ℝ →
      (quittingGame reward).BehaviorProfile → Prop
  | [], [], _ => True
  | root :: roots, ε :: errors, terminal =>
      IsεQuittingRootNash reward
          (fun who => quittingContinuationBestResponseValue reward
            (quittingLiteralRootStackProfile reward roots terminal) who)
          ε root ∧
        IsQuittingCapNashRootStackWithErrors reward roots errors terminal
  | _, _, _ => False

/-- Common rowwise `epsilon` bounds pay for the sharp cumulative defect with
the optimal conversion factor `card players`. -/
theorem capStackNashDefectSum_le_card_mul_errorSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) :
    ∀ (roots : List (ι → PMF Bool)) (errors : List ℝ),
      IsQuittingCapNashRootStackWithErrors reward roots errors terminal →
        quittingCapStackNashDefectSum reward roots terminal ≤
          Fintype.card ι * errors.sum := by
  intro roots
  induction roots with
  | nil =>
      intro errors hstack
      cases errors with
      | nil => simp
      | cons ε errors => contradiction
  | cons root roots ih =>
      intro errors hstack
      cases errors with
      | nil => contradiction
      | cons ε errors =>
          have hroot := hstack.1
          have htail := ih errors hstack.2
          have hdefect :=
            quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
              reward
                (fun who => quittingContinuationBestResponseValue reward
                  (quittingLiteralRootStackProfile reward roots terminal) who)
                root ε hroot
          simp only [quittingCapStackNashDefectSum_cons, List.sum_cons]
          linarith

/-- `epsilon`-schedule specialization of the paid-stack account.  In
particular, a summable error schedule supplies a uniform finite absorption
budget; pointwise vanishing without summability does not. -/
theorem semanticMinimum_mul_capStackAbsorptionSum_le_semanticBudget_add_card_mul_errorSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (roots : List (ι → PMF Bool)) (errors : List ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hstack : IsQuittingCapNashRootStackWithErrors
      reward roots errors terminal) :
    quittingTerminalSemanticDebtSum minimum *
        quittingCapNashStackAbsorptionSum roots ≤
      quittingTerminalDebtSum reward terminal -
          quittingTerminalSemanticDebtSum minimum +
        Fintype.card ι * errors.sum := by
  have haccount :=
    semanticMinimum_mul_capStackAbsorptionSum_le_semanticBudget_add_defectSum
      reward minimum terminal roots hM hreward hminimum
  have herrors := capStackNashDefectSum_le_card_mul_errorSum
    reward terminal roots errors hstack
  linarith

/-- Any charge beyond the ordinary reset-debt budget requires a matching
strict payment in the exact cumulative playerwise Nash-defect account. -/
theorem margin_lt_capStackNashDefectSum_of_offBudget_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (roots : List (ι → PMF Bool)) (margin : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hoffBudget :
      quittingTerminalDebtSum reward terminal -
            quittingTerminalSemanticDebtSum minimum + margin <
        quittingTerminalSemanticDebtSum minimum *
          quittingCapNashStackAbsorptionSum roots) :
    margin < quittingCapStackNashDefectSum reward roots terminal := by
  have haccount :=
    semanticMinimum_mul_capStackAbsorptionSum_le_semanticBudget_add_defectSum
      reward minimum terminal roots hM hreward hminimum
  linarith

end GameTheory
