/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Quitting.Debt.Marked.TimeAdvance
import UniformEquilibrium.Quitting.Root.LiteralExactPrefixStack

/-!
# Finite cap--Nash chronologies

Finite mixed Nash existence can be iterated backwards against the *actual
unilateral cap* of the already constructed suffix.  This gives a literal
state-matched cap chronology: every displayed tail is an executable profile,
and every root is exact Nash against that tail's coordinatewise behavioral
best-response envelope.

The cancellation from cap--Nash prefixing then folds without loss.  Every
debt coordinate, and hence total debt, is multiplied by the product of the
joint Continue masses.  More sharply, the sum of the one-stage absorption
masses is charged by the total-debt drop at the global literal debt infimum.

Consequently, if the global infimum is positive, a near-minimal terminal
profile admits cap--Nash chronologies of arbitrary finite depth whose *entire
unweighted absorption budget* is small.  Their joint survival is bounded
away from zero uniformly in the depth.  Thus iteration supplies a genuine
cap chronology, but it does not by itself supply an absorbing renewal or a
conditioned-tail compiler: in the positive-debt regime its limiting behavior
is a summable-hazard obstruction with uniformly positive finite-block
survival.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Every root is exact Nash against the unilateral cap of the remaining
executable suffix.  This differs from a literal exact-root stack, whose tail
vector is the prescribed payoff rather than the best-response envelope. -/
def IsQuittingCapNashRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    List (ι → PMF Bool) → (quittingGame reward).BehaviorProfile → Prop
  | [], _ => True
  | root :: roots, terminal =>
      IsεQuittingRootNash reward
        (fun player => quittingContinuationBestResponseValue reward
          (quittingLiteralRootStackProfile reward roots terminal) player)
        0 root ∧
      IsQuittingCapNashRootStack reward roots terminal

@[simp]
theorem isQuittingCapNashRootStack_nil
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) :
    IsQuittingCapNashRootStack reward [] terminal := trivial

theorem isQuittingCapNashRootStack_cons_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    IsQuittingCapNashRootStack reward (root :: roots) terminal ↔
      IsεQuittingRootNash reward
        (fun player => quittingContinuationBestResponseValue reward
          (quittingLiteralRootStackProfile reward roots terminal) player)
        0 root ∧
      IsQuittingCapNashRootStack reward roots terminal := by
  rfl

/-- Dropping a chronological prefix preserves the cap--Nash stack property.
-/
theorem IsQuittingCapNashRootStack.drop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (hstack : IsQuittingCapNashRootStack reward roots terminal)
    (count : ℕ) :
    IsQuittingCapNashRootStack reward (roots.drop count) terminal := by
  induction roots generalizing count with
  | nil => simp
  | cons root roots ih =>
      cases count with
      | zero => simpa using hstack
      | succ count =>
          rw [isQuittingCapNashRootStack_cons_iff] at hstack
          simpa using ih hstack.2 count

/-- Exact cap--Nash stacks exist over every executable terminal continuation
at every finite depth. -/
theorem exists_quittingCapNashRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) (depth : ℕ) :
    ∃ roots : List (ι → PMF Bool),
      roots.length = depth ∧
        IsQuittingCapNashRootStack reward roots terminal := by
  induction depth with
  | zero => exact ⟨[], rfl, trivial⟩
  | succ depth ih =>
      obtain ⟨roots, hlength, hstack⟩ := ih
      let suffix := quittingLiteralRootStackProfile reward roots terminal
      obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash
        (reward := reward)
        (fun player => quittingContinuationBestResponseValue reward suffix player)
      refine ⟨root :: roots, by simp [hlength], ?_⟩
      exact ⟨by simpa [suffix] using hnash, hstack⟩

/-- Joint survival of a finite root word. -/
def quittingCapNashStackContinueProduct
    (roots : List (ι → PMF Bool)) : ℝ :=
  (roots.map quittingStationaryContinueMass).prod

/-- Unweighted sum of the root absorption hazards in a finite word. -/
def quittingCapNashStackAbsorptionSum
    (roots : List (ι → PMF Bool)) : ℝ :=
  (roots.map quittingRootAbsorptionMass).sum

omit [DecidableEq ι] in
@[simp]
theorem quittingCapNashStackContinueProduct_nil :
    quittingCapNashStackContinueProduct ([] : List (ι → PMF Bool)) = 1 := rfl

omit [DecidableEq ι] in
@[simp]
theorem quittingCapNashStackContinueProduct_cons
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool)) :
    quittingCapNashStackContinueProduct (root :: roots) =
      quittingStationaryContinueMass root *
        quittingCapNashStackContinueProduct roots := rfl

omit [DecidableEq ι] in
@[simp]
theorem quittingCapNashStackAbsorptionSum_nil :
    quittingCapNashStackAbsorptionSum ([] : List (ι → PMF Bool)) = 0 := rfl

omit [DecidableEq ι] in
@[simp]
theorem quittingCapNashStackAbsorptionSum_cons
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool)) :
    quittingCapNashStackAbsorptionSum (root :: roots) =
      quittingRootAbsorptionMass root +
        quittingCapNashStackAbsorptionSum roots := rfl

omit [DecidableEq ι] in
theorem quittingCapNashStackContinueProduct_nonneg
    (roots : List (ι → PMF Bool)) :
    0 ≤ quittingCapNashStackContinueProduct roots := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      rw [quittingCapNashStackContinueProduct_cons]
      exact mul_nonneg (quittingStationaryContinueMass_nonneg root) ih

omit [DecidableEq ι] in
theorem quittingCapNashStackContinueProduct_le_one
    (roots : List (ι → PMF Bool)) :
    quittingCapNashStackContinueProduct roots ≤ 1 := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      rw [quittingCapNashStackContinueProduct_cons]
      have hrootNonneg := quittingStationaryContinueMass_nonneg root
      have hrootLe := quittingStationaryContinueMass_le_one root
      have htailNonneg := quittingCapNashStackContinueProduct_nonneg roots
      nlinarith [mul_nonneg hrootNonneg htailNonneg,
        mul_nonneg (sub_nonneg.mpr hrootLe) htailNonneg]

omit [DecidableEq ι] in
theorem quittingCapNashStackAbsorptionSum_nonneg
    (roots : List (ι → PMF Bool)) :
    0 ≤ quittingCapNashStackAbsorptionSum roots := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      rw [quittingCapNashStackAbsorptionSum_cons]
      exact add_nonneg (quittingRootAbsorptionMass_nonneg root) ih

omit [DecidableEq ι] in
/-- The loss of joint survival is at most the unweighted sum of the displayed
one-stage absorption hazards. -/
theorem one_sub_capNashStackContinueProduct_le_absorptionSum
    (roots : List (ι → PMF Bool)) :
    1 - quittingCapNashStackContinueProduct roots ≤
      quittingCapNashStackAbsorptionSum roots := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      have hrootLe := quittingStationaryContinueMass_le_one root
      have htailLe := quittingCapNashStackContinueProduct_le_one roots
      have hgapNonneg :
          0 ≤ 1 - quittingCapNashStackContinueProduct roots :=
        sub_nonneg.mpr htailLe
      have hscaled :
          quittingStationaryContinueMass root *
              (1 - quittingCapNashStackContinueProduct roots) ≤
            1 - quittingCapNashStackContinueProduct roots :=
        by simpa using mul_le_mul_of_nonneg_right hrootLe hgapNonneg
      rw [quittingCapNashStackContinueProduct_cons,
        quittingCapNashStackAbsorptionSum_cons]
      unfold quittingRootAbsorptionMass
      nlinarith

omit [DecidableEq ι] in
/-- A finite root word moves its prescribed terminal payoff by at most the
reward diameter times its unweighted absorption budget.  In particular the
cap--Nash chronologies below are approximate payoff returns when their debt
excess is small. -/
theorem abs_quittingTerminalPayoff_rootStack_sub_terminal_le
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    |quittingTerminalPayoff reward
          (quittingLiteralRootStackProfile reward roots terminal) who -
        quittingTerminalPayoff reward terminal who| ≤
      2 * M * quittingCapNashStackAbsorptionSum roots := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      let suffix := quittingLiteralRootStackProfile reward roots terminal
      have hsuffixBound :
          |quittingTerminalPayoff reward suffix who| ≤ M :=
        abs_quittingTerminalPayoff_le reward suffix who hM hreward
      have hstep :=
        abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
          reward (fun player => quittingTerminalPayoff reward suffix player)
          root who M hreward hsuffixBound
      rw [quittingLiteralRootStackProfile_cons,
        quittingTerminalPayoff_rootThenContinuation_eq]
      calc
        |quittingRootSuccessorPayoff reward
              (fun player => quittingTerminalPayoff reward suffix player)
              root who - quittingTerminalPayoff reward terminal who| ≤
            |quittingRootSuccessorPayoff reward
                (fun player => quittingTerminalPayoff reward suffix player)
                root who - quittingTerminalPayoff reward suffix who| +
              |quittingTerminalPayoff reward suffix who -
                quittingTerminalPayoff reward terminal who| :=
          abs_sub_le _ _ _
        _ ≤ 2 * M * quittingRootAbsorptionMass root +
              2 * M * quittingCapNashStackAbsorptionSum roots :=
          add_le_add hstep ih
        _ = 2 * M *
              quittingCapNashStackAbsorptionSum (root :: roots) := by
          rw [quittingCapNashStackAbsorptionSum_cons]
          ring

/-- Exact folded playerwise debt scaling along a cap--Nash chronology. -/
theorem quittingTerminalDeviationDebt_capNashRootStack_eq
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    quittingTerminalDeviationDebt reward
        (quittingLiteralRootStackProfile reward roots terminal) who =
      quittingCapNashStackContinueProduct roots *
        quittingTerminalDeviationDebt reward terminal who := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      rw [isQuittingCapNashRootStack_cons_iff] at hstack
      rw [quittingLiteralRootStackProfile_cons,
        quittingTerminalDeviationDebt_rootThenContinuation_eq_continueMass_mul_of_capNash
          (reward := reward) root
          (quittingLiteralRootStackProfile reward roots terminal) who
          hM hreward hstack.1,
        ih hstack.2]
      rw [quittingCapNashStackContinueProduct_cons]
      ring

/-- The unilateral best-response cap of a cap--Nash chronology returns to the
terminal cap with a linear-in-absorption error.  Together with the payoff
bound above, this makes the stack a genuine approximate semantic return, but
only at `O(absorption)` rather than the `o(absorption)` needed for automatic
renewal tightness. -/
theorem abs_quittingContinuationBestResponseValue_capNashRootStack_sub_terminal_le
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    |quittingContinuationBestResponseValue reward
          (quittingLiteralRootStackProfile reward roots terminal) who -
        quittingContinuationBestResponseValue reward terminal who| ≤
      4 * M * quittingCapNashStackAbsorptionSum roots := by
  let stack := quittingLiteralRootStackProfile reward roots terminal
  let survival := quittingCapNashStackContinueProduct roots
  let absorption := quittingCapNashStackAbsorptionSum roots
  let terminalDebt := quittingTerminalDeviationDebt reward terminal who
  let stackDebt := quittingTerminalDeviationDebt reward stack who
  have hpayoff :
      |quittingTerminalPayoff reward stack who -
          quittingTerminalPayoff reward terminal who| ≤
        2 * M * absorption := by
    exact abs_quittingTerminalPayoff_rootStack_sub_terminal_le
      (reward := reward) roots terminal who hM hreward
  have hdebtEq : stackDebt = survival * terminalDebt := by
    exact quittingTerminalDeviationDebt_capNashRootStack_eq
      (reward := reward) roots terminal who hM hreward hstack
  have hterminalDebtNonneg : 0 ≤ terminalDebt := by
    exact quittingTerminalDeviationDebt_nonneg
      reward terminal who hM hreward
  have hterminalDebtLe : terminalDebt ≤ 2 * M := by
    have hcapBound := abs_quittingContinuationBestResponseValue_le
      reward terminal who hM hreward
    have hpayoffBound := abs_quittingTerminalPayoff_le
      reward terminal who hM hreward
    have hcapUpper := le_of_abs_le hcapBound
    have hpayoffLower := neg_le_of_abs_le hpayoffBound
    dsimp [terminalDebt]
    unfold quittingTerminalDeviationDebt
    linarith
  have hsurvivalLe : survival ≤ 1 :=
    quittingCapNashStackContinueProduct_le_one roots
  have habsorptionNonneg : 0 ≤ absorption :=
    quittingCapNashStackAbsorptionSum_nonneg roots
  have hunion : 1 - survival ≤ absorption :=
    one_sub_capNashStackContinueProduct_le_absorptionSum roots
  have hdebtDifference : |stackDebt - terminalDebt| ≤ 2 * M * absorption := by
    rw [hdebtEq]
    have hnonpos : survival * terminalDebt - terminalDebt ≤ 0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsurvivalLe)
        hterminalDebtNonneg]
    rw [abs_of_nonpos hnonpos]
    calc
      -(survival * terminalDebt - terminalDebt) =
          (1 - survival) * terminalDebt := by ring
      _ ≤ absorption * terminalDebt :=
        mul_le_mul_of_nonneg_right hunion hterminalDebtNonneg
      _ ≤ absorption * (2 * M) :=
        mul_le_mul_of_nonneg_left hterminalDebtLe habsorptionNonneg
      _ = 2 * M * absorption := by ring
  have hidentity :
      quittingContinuationBestResponseValue reward stack who -
          quittingContinuationBestResponseValue reward terminal who =
        (quittingTerminalPayoff reward stack who -
            quittingTerminalPayoff reward terminal who) +
          (stackDebt - terminalDebt) := by
    dsimp [stackDebt, terminalDebt]
    unfold quittingTerminalDeviationDebt
    ring
  rw [hidentity]
  calc
    |(quittingTerminalPayoff reward stack who -
          quittingTerminalPayoff reward terminal who) +
        (stackDebt - terminalDebt)| ≤
      |quittingTerminalPayoff reward stack who -
          quittingTerminalPayoff reward terminal who| +
        |stackDebt - terminalDebt| := abs_add_le _ _
    _ ≤ 2 * M * absorption + 2 * M * absorption :=
      add_le_add hpayoff hdebtDifference
    _ = 4 * M * absorption := by ring

/-- Exact folded total-debt scaling along a cap--Nash chronology. -/
theorem quittingTerminalDebtSum_capNashRootStack_eq
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward roots terminal) =
      quittingCapNashStackContinueProduct roots *
        quittingTerminalDebtSum reward terminal := by
  unfold quittingTerminalDebtSum
  simp_rw [quittingTerminalDeviationDebt_capNashRootStack_eq
    (reward := reward) roots terminal _ hM hreward hstack]
  rw [Finset.mul_sum]

/-- The global literal total-debt infimum lies below the product-scaled debt
of every finite cap--Nash chronology. -/
theorem debtSumInf_le_capNashStackContinueProduct_mul_debtSum
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    quittingTerminalDebtSumInf reward ≤
      quittingCapNashStackContinueProduct roots *
        quittingTerminalDebtSum reward terminal := by
  have hinf := quittingTerminalDebtSumInf_le
    (reward := reward)
    (quittingLiteralRootStackProfile reward roots terminal) hM hreward
  rwa [quittingTerminalDebtSum_capNashRootStack_eq
    (reward := reward) roots terminal hM hreward hstack] at hinf

/-- Every one-stage absorption hazard in the cap chronology is paid by the
drop of total debt, at the scale of the global literal debt infimum. -/
theorem debtSumInf_mul_capNashStackAbsorptionSum_le_debtDrop
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    quittingTerminalDebtSumInf reward *
        quittingCapNashStackAbsorptionSum roots ≤
      quittingTerminalDebtSum reward terminal -
        quittingTerminalDebtSum reward
          (quittingLiteralRootStackProfile reward roots terminal) := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      rw [isQuittingCapNashRootStack_cons_iff] at hstack
      let suffix := quittingLiteralRootStackProfile reward roots terminal
      have hinfSuffix : quittingTerminalDebtSumInf reward ≤
          quittingTerminalDebtSum reward suffix :=
        quittingTerminalDebtSumInf_le (reward := reward) suffix hM hreward
      have habsorption : 0 ≤ quittingRootAbsorptionMass root := by
        unfold quittingRootAbsorptionMass
        linarith [quittingStationaryContinueMass_le_one root]
      have hlocal : quittingTerminalDebtSumInf reward *
            quittingRootAbsorptionMass root ≤
          quittingTerminalDebtSum reward suffix *
            quittingRootAbsorptionMass root :=
        mul_le_mul_of_nonneg_right hinfSuffix habsorption
      have hscale :=
        quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
          (reward := reward) root suffix hM hreward hstack.1
      have htail := ih hstack.2
      change quittingTerminalDebtSumInf reward *
          (quittingRootAbsorptionMass root +
            quittingCapNashStackAbsorptionSum roots) ≤
        quittingTerminalDebtSum reward terminal -
          quittingTerminalDebtSum reward
            (quittingRootThenContinuationProfile reward root suffix)
      unfold quittingRootAbsorptionMass at hlocal ⊢
      dsimp [suffix] at hinfSuffix hlocal hscale
      rw [hscale]
      nlinarith

/-- Near-minimality controls the unweighted absorption budget of the whole
finite chronology, independently of its depth. -/
theorem capNashStack_absorptionBudget_of_nearMinimum
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (epsilon : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hstack : IsQuittingCapNashRootStack reward roots terminal)
    (hnear : quittingTerminalDebtSum reward terminal ≤
      quittingTerminalDebtSumInf reward + epsilon) :
    quittingTerminalDebtSumInf reward *
        quittingCapNashStackAbsorptionSum roots ≤ epsilon := by
  have hbudget := debtSumInf_mul_capNashStackAbsorptionSum_le_debtDrop
    (reward := reward) roots terminal hM hreward hstack
  have hinfStack := quittingTerminalDebtSumInf_le
    (reward := reward)
    (quittingLiteralRootStackProfile reward roots terminal) hM hreward
  linarith

/-- In the positive-infimum regime, the full chronological survival product
is uniformly bounded away from zero, regardless of the stack depth. -/
theorem capNashStack_continueProduct_lowerBound
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hinf : 0 < quittingTerminalDebtSumInf reward)
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    quittingTerminalDebtSumInf reward /
        quittingTerminalDebtSum reward terminal ≤
      quittingCapNashStackContinueProduct roots := by
  have hterminalPos : 0 < quittingTerminalDebtSum reward terminal :=
    hinf.trans_le
      (quittingTerminalDebtSumInf_le (reward := reward) terminal hM hreward)
  have hscaled :=
    debtSumInf_le_capNashStackContinueProduct_mul_debtSum
      (reward := reward) roots terminal hM hreward hstack
  apply (div_le_iff₀ hterminalPos).2
  simpa [mul_comm] using hscaled

/-- Every row in a finite cap--Nash chronology has strictly positive joint
Continue mass when the global literal debt infimum is positive. -/
theorem capNashRootStack_continueMass_pos_of_debtSumInf_pos
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hinf : 0 < quittingTerminalDebtSumInf reward)
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    ∀ root ∈ roots, 0 < quittingStationaryContinueMass root := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      rw [isQuittingCapNashRootStack_cons_iff] at hstack
      intro selected hselected
      simp only [List.mem_cons] at hselected
      rcases hselected with rfl | htail
      · exact capNash_continueMass_pos_of_debtSumInf_pos
          (reward := reward) selected
          (quittingLiteralRootStackProfile reward roots terminal)
          hM hreward hinf hstack.1
      · exact ih hstack.2 selected htail

omit [DecidableEq ι] in
/-- Positivity of every row's joint Continue mass is equivalent to positivity
of the folded survival product in the direction needed below. -/
theorem quittingCapNashStackContinueProduct_pos
    (roots : List (ι → PMF Bool))
    (hpositive : ∀ root ∈ roots,
      0 < quittingStationaryContinueMass root) :
    0 < quittingCapNashStackContinueProduct roots := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      rw [quittingCapNashStackContinueProduct_cons]
      exact mul_pos
        (hpositive root (by simp))
        (ih (fun selected hselected =>
          hpositive selected (by simp [hselected])))

omit [DecidableEq ι] in
/-- The sum of the one-row absorption hazards of a finite cap--Nash
chronology is bounded by minus the logarithm of its joint survival product.
The positivity assumption is essential only to make the logarithm additive. -/
theorem capNashStack_absorptionSum_le_neg_log_continueProduct
    (roots : List (ι → PMF Bool))
    (hpositive : ∀ root ∈ roots,
      0 < quittingStationaryContinueMass root) :
    quittingCapNashStackAbsorptionSum roots ≤
      -Real.log (quittingCapNashStackContinueProduct roots) := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      have hroot : 0 < quittingStationaryContinueMass root :=
        hpositive root (by simp)
      have htailPositive : ∀ selected ∈ roots,
          0 < quittingStationaryContinueMass selected := by
        intro selected hselected
        exact hpositive selected (by simp [hselected])
      have htail := ih htailPositive
      have htailProduct : 0 < quittingCapNashStackContinueProduct roots :=
        quittingCapNashStackContinueProduct_pos roots htailPositive
      have hrowLog := Real.log_le_sub_one_of_pos hroot
      rw [quittingCapNashStackAbsorptionSum_cons,
        quittingCapNashStackContinueProduct_cons,
        Real.log_mul (ne_of_gt hroot) (ne_of_gt htailProduct)]
      unfold quittingRootAbsorptionMass
      linarith

/-- **Sharp logarithmic absorption budget for finite cap--Nash words.**
If the literal debt infimum is positive, the cumulative one-row absorption
hazard is bounded by the logarithm of the terminal profile's debt ratio.
This is stronger than the qualitative capacity theorem for ordinary
Nash--Bellman rows, whose coordinatewise contraction factors are opponent
Continue masses rather than joint Continue mass. -/
theorem capNashStack_absorptionSum_le_log_debtRatio
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hinf : 0 < quittingTerminalDebtSumInf reward)
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    quittingCapNashStackAbsorptionSum roots ≤
      Real.log (quittingTerminalDebtSum reward terminal /
        quittingTerminalDebtSumInf reward) := by
  have hterminalPos : 0 < quittingTerminalDebtSum reward terminal :=
    hinf.trans_le
      (quittingTerminalDebtSumInf_le (reward := reward) terminal hM hreward)
  have hproductLower := capNashStack_continueProduct_lowerBound
    (reward := reward) roots terminal hM hreward hinf hstack
  have hproductPos : 0 < quittingCapNashStackContinueProduct roots := by
    exact (div_pos hinf hterminalPos).trans_le hproductLower
  have hlogMonotone :
      Real.log (quittingTerminalDebtSumInf reward /
          quittingTerminalDebtSum reward terminal) ≤
        Real.log (quittingCapNashStackContinueProduct roots) :=
    Real.strictMonoOn_log.monotoneOn
      (div_pos hinf hterminalPos) hproductPos hproductLower
  have hlogBudget :=
    capNashStack_absorptionSum_le_neg_log_continueProduct roots
      (capNashRootStack_continueMass_pos_of_debtSumInf_pos
        (reward := reward) roots terminal hM hreward hinf hstack)
  calc
    quittingCapNashStackAbsorptionSum roots ≤
        -Real.log (quittingCapNashStackContinueProduct roots) := hlogBudget
    _ ≤ -Real.log (quittingTerminalDebtSumInf reward /
        quittingTerminalDebtSum reward terminal) := neg_le_neg hlogMonotone
    _ = Real.log (quittingTerminalDebtSum reward terminal /
        quittingTerminalDebtSumInf reward) := by
      rw [Real.log_div (ne_of_gt hinf) (ne_of_gt hterminalPos),
        Real.log_div (ne_of_gt hterminalPos) (ne_of_gt hinf)]
      ring

/-- Arbitrarily deep exact cap chronologies over one near-minimal actual
profile have a depth-independent absorption budget and a positive finite-block
survival floor.  This is the sharp finite obstruction to reading cap--Nash iteration
as an absorbing renewal construction. -/
theorem exists_deep_nearMinimum_capNashChronology
    (terminal : (quittingGame reward).BehaviorProfile)
    (depth : ℕ) (epsilon : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hinf : 0 < quittingTerminalDebtSumInf reward)
    (hnear : quittingTerminalDebtSum reward terminal ≤
      quittingTerminalDebtSumInf reward + epsilon) :
    ∃ roots : List (ι → PMF Bool),
      roots.length = depth ∧
      IsQuittingCapNashRootStack reward roots terminal ∧
      quittingTerminalDebtSumInf reward *
          quittingCapNashStackAbsorptionSum roots ≤ epsilon ∧
      quittingTerminalDebtSumInf reward /
          quittingTerminalDebtSum reward terminal ≤
        quittingCapNashStackContinueProduct roots ∧
      (∀ who,
        |quittingTerminalPayoff reward
              (quittingLiteralRootStackProfile reward roots terminal) who -
            quittingTerminalPayoff reward terminal who| ≤
          2 * M * quittingCapNashStackAbsorptionSum roots) ∧
      (∀ who,
        |quittingContinuationBestResponseValue reward
              (quittingLiteralRootStackProfile reward roots terminal) who -
            quittingContinuationBestResponseValue reward terminal who| ≤
          4 * M * quittingCapNashStackAbsorptionSum roots) := by
  obtain ⟨roots, hlength, hstack⟩ :=
    exists_quittingCapNashRootStack reward terminal depth
  exact ⟨roots, hlength, hstack,
    capNashStack_absorptionBudget_of_nearMinimum
      (reward := reward) roots terminal epsilon hM hreward hstack hnear,
    capNashStack_continueProduct_lowerBound
      (reward := reward) roots terminal hM hreward hinf hstack,
    fun who => abs_quittingTerminalPayoff_rootStack_sub_terminal_le
      (reward := reward) roots terminal who hM hreward,
    fun who =>
      abs_quittingContinuationBestResponseValue_capNashRootStack_sub_terminal_le
        (reward := reward) roots terminal who hM hreward hstack⟩

end GameTheory
