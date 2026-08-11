/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed
import UniformEquilibrium.Quitting.Root.TerminalDebtBlock

/-!
# Finite literal exact-root prefix stacks

Starting from any actual continuation profile, finite mixed Nash existence can
be iterated backwards for any prescribed finite depth.  Each chosen root is
exact Nash against the literal payoff of the already constructed suffix.
Hence every intermediate payoff and best-response cap is co-realized by an
actual executable suffix.

Playerwise terminal debt along the stack is the action of the concatenated
survival block.  Positive debt removes the terminal positive-part truncation
and yields exact aggregate conservation.
-/

noncomputable section

namespace GameTheory

open Math.Probability
open Math.SurvivalWeightedObstruction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Executable profile obtained by prepending a chronological finite root
word to an actual terminal continuation profile. -/
def quittingLiteralRootStackProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  roots.foldr
    (fun root continuation =>
      quittingRootThenContinuationProfile reward root continuation)
    terminal

omit [DecidableEq ι] in
@[simp]
theorem quittingLiteralRootStackProfile_nil
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingLiteralRootStackProfile reward [] terminal = terminal := rfl

omit [DecidableEq ι] in
@[simp]
theorem quittingLiteralRootStackProfile_cons
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingLiteralRootStackProfile reward (root :: roots) terminal =
      quittingRootThenContinuationProfile reward root
        (quittingLiteralRootStackProfile reward roots terminal) := rfl

/-- Every root in the word is exact endpoint Nash against the literal payoff
of the remaining executable suffix. -/
def IsQuittingLiteralExactRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    List (ι → PMF Bool) → (quittingGame reward).BehaviorProfile → Prop
  | [], _ => True
  | root :: roots, terminal =>
      IsεQuittingRootEndpointNash reward
        (fun player => quittingTerminalPayoff reward
          (quittingLiteralRootStackProfile reward roots terminal) player)
        0 root ∧
      IsQuittingLiteralExactRootStack reward roots terminal

@[simp]
theorem isQuittingLiteralExactRootStack_nil
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) :
    IsQuittingLiteralExactRootStack reward [] terminal := trivial

theorem isQuittingLiteralExactRootStack_cons_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    IsQuittingLiteralExactRootStack reward (root :: roots) terminal ↔
      IsεQuittingRootEndpointNash reward
        (fun player => quittingTerminalPayoff reward
          (quittingLiteralRootStackProfile reward roots terminal) player)
        0 root ∧
      IsQuittingLiteralExactRootStack reward roots terminal := by
  rfl

/-- Dropping any initial segment of an exact literal stack leaves an exact
literal stack over the same terminal continuation. -/
theorem IsQuittingLiteralExactRootStack.drop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (hstack : IsQuittingLiteralExactRootStack reward roots terminal)
    (count : ℕ) :
    IsQuittingLiteralExactRootStack reward (roots.drop count) terminal := by
  induction roots generalizing count with
  | nil => simp
  | cons root roots ih =>
      cases count with
      | zero => simpa using hstack
      | succ count =>
          rw [isQuittingLiteralExactRootStack_cons_iff] at hstack
          simpa using ih hstack.2 count

/-- Exact literal prefix stacks exist at every finite depth. -/
theorem exists_quittingLiteralExactRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) (depth : ℕ) :
    ∃ roots : List (ι → PMF Bool),
      roots.length = depth ∧
        IsQuittingLiteralExactRootStack reward roots terminal := by
  induction depth with
  | zero => exact ⟨[], rfl, trivial⟩
  | succ depth ih =>
      obtain ⟨roots, hlength, hstack⟩ := ih
      let suffix := quittingLiteralRootStackProfile reward roots terminal
      obtain ⟨root, hnash⟩ :=
        exists_isZeroQuittingRootEndpointNash_simplex reward
          (fun player => quittingTerminalPayoff reward suffix player)
      let root' := quittingRootOfSimplex root
      refine ⟨root' :: roots, by simp [hlength], ?_⟩
      exact ⟨by simpa [suffix, root'] using hnash, hstack⟩

/-- Playerwise sequence of one-step literal debt blocks along a root stack. -/
def quittingLiteralTerminalDebtBlocks
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    List (ι → PMF Bool) → (quittingGame reward).BehaviorProfile →
      ι → List (Block Unit)
  | [], _, _ => []
  | root :: roots, terminal, who =>
      quittingLiteralTerminalDebtBlock reward
          (quittingLiteralRootStackProfile reward roots terminal) root who ::
        quittingLiteralTerminalDebtBlocks reward roots terminal who

@[simp]
theorem quittingLiteralTerminalDebtBlocks_nil
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingLiteralTerminalDebtBlocks reward [] terminal who = [] := rfl

@[simp]
theorem quittingLiteralTerminalDebtBlocks_cons
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingLiteralTerminalDebtBlocks reward (root :: roots) terminal who =
      quittingLiteralTerminalDebtBlock reward
          (quittingLiteralRootStackProfile reward roots terminal) root who ::
        quittingLiteralTerminalDebtBlocks reward roots terminal who := rfl

/-- Aggregate playerwise block of a literal root stack. -/
def quittingLiteralTerminalDebtAggregateBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι) :
    Block Unit :=
  Block.concatList
    (quittingLiteralTerminalDebtBlocks reward roots terminal who)

/-- Exact folded terminal-debt formula for a literal exact-root stack. -/
theorem quittingTerminalDeviationDebt_literalRootStack_eq_blockAct
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hstack : IsQuittingLiteralExactRootStack reward roots terminal) :
    quittingTerminalDeviationDebt reward
        (quittingLiteralRootStackProfile reward roots terminal) who =
      (quittingLiteralTerminalDebtAggregateBlock reward roots terminal who).act
        () (quittingTerminalDeviationDebt reward terminal who) := by
  induction roots with
  | nil =>
      have hdebt := quittingTerminalDeviationDebt_nonneg
        reward terminal who hM hreward
      exact (Block.act_identity_of_nonneg () hdebt).symm
  | cons root roots ih =>
      rw [isQuittingLiteralExactRootStack_cons_iff] at hstack
      let suffix := quittingLiteralRootStackProfile reward roots terminal
      have hnashRoot : IsεQuittingRootNash reward
          (fun player => quittingTerminalPayoff reward suffix player)
          0 root :=
        (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
          reward (fun player => quittingTerminalPayoff reward suffix player)
          0 root).mp hstack.1
      rw [quittingLiteralRootStackProfile_cons,
        quittingTerminalDeviationDebt_rootThenContinuation_eq_blockAct
          reward root suffix who hM hreward hnashRoot]
      rw [ih hstack.2]
      exact (Block.act_concat
        (quittingLiteralTerminalDebtBlock reward suffix root who)
        (quittingLiteralTerminalDebtAggregateBlock reward roots terminal who)
        () (quittingTerminalDeviationDebt reward terminal who)).symm

/-- Every coordinate of terminal debt weakly decreases across a finite literal
exact-root stack. -/
theorem quittingTerminalDeviationDebt_literalRootStack_le_terminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hstack : IsQuittingLiteralExactRootStack reward roots terminal) :
    quittingTerminalDeviationDebt reward
        (quittingLiteralRootStackProfile reward roots terminal) who ≤
      quittingTerminalDeviationDebt reward terminal who := by
  rw [quittingTerminalDeviationDebt_literalRootStack_eq_blockAct
    reward roots terminal who hM hreward hstack]
  exact Block.act_le_debt
    (quittingLiteralTerminalDebtAggregateBlock reward roots terminal who)
    () (quittingTerminalDeviationDebt_nonneg reward terminal who hM hreward)

/-- Total terminal debt cannot increase across a finite literal exact-root
stack. -/
theorem sum_quittingTerminalDeviationDebt_literalRootStack_le_terminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hstack : IsQuittingLiteralExactRootStack reward roots terminal) :
    (∑ who, quittingTerminalDeviationDebt reward
        (quittingLiteralRootStackProfile reward roots terminal) who) ≤
      ∑ who, quittingTerminalDeviationDebt reward terminal who := by
  exact Finset.sum_le_sum fun who _ =>
    quittingTerminalDeviationDebt_literalRootStack_le_terminal
      reward roots terminal who hM hreward hstack

/-- Positive initial debt gives exact folded conservation: terminal debt times
aggregate deleted survival equals initial debt plus aggregate exercise charge.
-/
theorem quittingLiteralRootStack_debt_conservation_of_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hstack : IsQuittingLiteralExactRootStack reward roots terminal)
    (hpositive : 0 < quittingTerminalDeviationDebt reward
      (quittingLiteralRootStackProfile reward roots terminal) who) :
    (quittingLiteralTerminalDebtAggregateBlock reward roots terminal who).survival *
          quittingTerminalDeviationDebt reward terminal who =
      quittingTerminalDeviationDebt reward
          (quittingLiteralRootStackProfile reward roots terminal) who +
        (quittingLiteralTerminalDebtAggregateBlock reward roots terminal who).charge.value
          () := by
  have hfold := quittingTerminalDeviationDebt_literalRootStack_eq_blockAct
    reward roots terminal who hM hreward hstack
  have hact : 0 <
      (quittingLiteralTerminalDebtAggregateBlock reward roots terminal who).act
        () (quittingTerminalDeviationDebt reward terminal who) := by
    rwa [← hfold]
  simpa only [← hfold] using
    Block.survival_mul_debt_eq_act_add_charge_of_act_pos
      (quittingLiteralTerminalDebtAggregateBlock reward roots terminal who)
      () (quittingTerminalDeviationDebt reward terminal who) hact

end GameTheory
