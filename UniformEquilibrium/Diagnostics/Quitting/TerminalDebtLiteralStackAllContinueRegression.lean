/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalDebtLiteralStack
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-!
# All-Continue regression for literal exact-prefix stacks

Deep literal exact-prefix stacks do not by themselves force an absorption
packet.  If the literal terminal payoff of the chosen continuation already
dominates every singleton quitting payoff, the all-Continue root is exact
Nash.  It can then be iterated to arbitrary finite depth, while the entire
literal semantic pair remains unchanged.

This is the precise negative control for attempts to turn a profitable atom
inside a continuation profile into owner mass in a separately selected exact
prefix stack.  Such a conversion requires an additional co-realization or
support-incidence premise.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Prepending any finite number of all-Continue roots preserves the literal
terminal semantic pair, provided all Continue is exact Nash at the terminal
prescribed payoff. -/
theorem quittingTerminalSemanticPair_literalAllContinueStack_eq_terminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) (depth : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who ≤
      quittingTerminalPayoff reward terminal who) :
    quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward
          (List.replicate depth
            (quittingAllContinueRoot : ι → PMF Bool)) terminal) =
      quittingTerminalSemanticPair reward terminal := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      let suffix := quittingLiteralRootStackProfile reward
        (List.replicate depth
          (quittingAllContinueRoot : ι → PMF Bool)) terminal
      have hsuffix : quittingTerminalSemanticPair reward suffix =
          quittingTerminalSemanticPair reward terminal := by
        simpa only [suffix] using ih
      have hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward terminal) who := by
        intro who
        exact quittingTerminalDeviationDebt_nonneg
          reward terminal who hM hreward
      have hnash : IsεQuittingRootNash reward
          (quittingTerminalSemanticPair reward terminal).1 0
          (quittingAllContinueRoot : ι → PMF Bool) := by
        apply (isZeroQuittingRootNash_allContinue_iff_singleton_le
          reward (quittingTerminalSemanticPair reward terminal).1).mpr
        exact hsolo
      have hprefix :=
        quittingTerminalSemanticPrefix_allContinue_eq_of_isZeroNash
          reward (quittingTerminalSemanticPair reward terminal) hdebt hnash
      rw [List.replicate_succ, quittingLiteralRootStackProfile_cons,
        quittingTerminalSemanticPair_rootThenContinuation
          reward quittingAllContinueRoot suffix hM hreward,
        hsuffix]
      exact hprefix

/-- Under the same singleton domination, an all-Continue literal exact stack
exists at every requested depth.  Hence depth alone supplies neither positive
absorption nor normalized owner mass. -/
theorem isQuittingLiteralExactRootStack_replicate_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) (depth : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who ≤
      quittingTerminalPayoff reward terminal who) :
    IsQuittingLiteralExactRootStack reward
      (List.replicate depth
        (quittingAllContinueRoot : ι → PMF Bool)) terminal := by
  induction depth with
  | zero => trivial
  | succ depth ih =>
      rw [List.replicate_succ,
        isQuittingLiteralExactRootStack_cons_iff]
      constructor
      · have hsemantic :=
          quittingTerminalSemanticPair_literalAllContinueStack_eq_terminal
            reward terminal depth hM hreward hsolo
        have hpayoff : (fun player => quittingTerminalPayoff reward
            (quittingLiteralRootStackProfile reward
              (List.replicate depth
                (quittingAllContinueRoot : ι → PMF Bool)) terminal) player) =
            fun player => quittingTerminalPayoff reward terminal player := by
          exact congrArg Prod.fst hsemantic
        rw [hpayoff]
        apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
          reward (fun player => quittingTerminalPayoff reward terminal player)
            quittingAllContinueRoot).mpr
        exact (isZeroQuittingRootNash_allContinue_iff_singleton_le
          reward (fun player =>
            quittingTerminalPayoff reward terminal player)).mpr hsolo
      · exact ih

end GameTheory
