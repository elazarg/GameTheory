/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalDebtPrefixDescent
import UniformEquilibrium.Quitting.Root.LiteralExactPrefixStack

/-!
# Lexicographically near-minimal literal exact-prefix stacks

An exact literal root stack over a lexicographic near-minimizer remains in the
same maximum-exploitability sublevel.  Since every displayed continuation is
an actual suffix of one executable profile, the secondary near-minimality
bound controls the total debt drop at every root of the stack.

The resulting finite triangular stacks have arbitrary depth.  At each node,
the literal debt utilization law gives quantitative atomic/all-Continue
rigidity without identifying conditioned values or stored annotations with
literal suffix payoffs.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Maximum literal terminal exploitability does not increase across an exact
literal root stack. -/
theorem quittingTerminalExploitability_literalRootStack_le_terminal
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hstack : IsQuittingLiteralExactRootStack reward roots terminal) :
    quittingTerminalExploitability reward
        (quittingLiteralRootStackProfile reward roots terminal) ≤
      quittingTerminalExploitability reward terminal := by
  induction roots with
  | nil => exact le_rfl
  | cons root roots ih =>
      rw [isQuittingLiteralExactRootStack_cons_iff] at hstack
      calc
        quittingTerminalExploitability reward
            (quittingLiteralRootStackProfile reward (root :: roots) terminal) ≤
          quittingTerminalExploitability reward
            (quittingLiteralRootStackProfile reward roots terminal) := by
              rw [quittingLiteralRootStackProfile_cons]
              exact quittingTerminalExploitability_rootThenContinuation_le
                reward root
                (quittingLiteralRootStackProfile reward roots terminal)
                hM hreward hstack.1
        _ ≤ quittingTerminalExploitability reward terminal := ih hstack.2

/-- Every root of a literal exact stack over a lexicographic near-minimizer
has one-step total debt drop strictly below the common accuracy. -/
theorem quittingTerminalDebtSum_literalExactStack_step_drop_lt
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    {accuracy M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hterminalMax : quittingTerminalExploitability reward terminal ≤
      quittingTerminalExploitabilityInf reward + accuracy)
    (hterminalSum : quittingTerminalDebtSum reward terminal <
      sInf (quittingTerminalDebtSumSublevelValues reward
        (quittingTerminalExploitabilityInf reward + accuracy)) + accuracy)
    (hstack : IsQuittingLiteralExactRootStack
      reward (root :: roots) terminal) :
    quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward roots terminal) -
      quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward (root :: roots) terminal) <
      accuracy := by
  rw [isQuittingLiteralExactRootStack_cons_iff] at hstack
  let prefixed :=
    quittingLiteralRootStackProfile reward (root :: roots) terminal
  have hprefixedMax : quittingTerminalExploitability reward prefixed ≤
      quittingTerminalExploitabilityInf reward + accuracy := by
    exact (quittingTerminalExploitability_literalRootStack_le_terminal
      reward (root :: roots) terminal hM hreward ⟨hstack.1, hstack.2⟩).trans
      hterminalMax
  have hinfLe :
      sInf (quittingTerminalDebtSumSublevelValues reward
        (quittingTerminalExploitabilityInf reward + accuracy)) ≤
      quittingTerminalDebtSum reward prefixed := by
    apply csInf_le
    · exact bddBelow_quittingTerminalDebtSumSublevelValues reward
        (quittingTerminalExploitabilityInf reward + accuracy) hM hreward
    · exact ⟨prefixed, hprefixedMax, rfl⟩
  have htailSum : quittingTerminalDebtSum reward
      (quittingLiteralRootStackProfile reward roots terminal) ≤
      quittingTerminalDebtSum reward terminal := by
    unfold quittingTerminalDebtSum
    exact sum_quittingTerminalDeviationDebt_literalRootStack_le_terminal
      reward roots terminal hM hreward hstack.2
  change quittingTerminalDebtSum reward
      (quittingLiteralRootStackProfile reward roots terminal) -
    quittingTerminalDebtSum reward prefixed < accuracy
  linarith

/-- Quantitative one-step rigidity at every node of a literal exact stack:
a macroscopic debt coordinate sees little opponent absorption. -/
theorem quittingLiteralExactStack_step_opponentAbsorption_mul_debtFloor_lt
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (who : ι) (debtFloor : ℝ)
    {accuracy M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hterminalMax : quittingTerminalExploitability reward terminal ≤
      quittingTerminalExploitabilityInf reward + accuracy)
    (hterminalSum : quittingTerminalDebtSum reward terminal <
      sInf (quittingTerminalDebtSumSublevelValues reward
        (quittingTerminalExploitabilityInf reward + accuracy)) + accuracy)
    (hstack : IsQuittingLiteralExactRootStack
      reward (root :: roots) terminal)
    (hfloor : debtFloor ≤ quittingTerminalDeviationDebt reward
      (quittingLiteralRootStackProfile reward roots terminal) who) :
    quittingRootOpponentAbsorptionMass root who * debtFloor < accuracy := by
  have hstep := quittingTerminalDebtSum_literalExactStack_step_drop_lt
    reward root roots terminal hM hreward hterminalMax hterminalSum hstack
  rw [isQuittingLiteralExactRootStack_cons_iff] at hstack
  have hnash :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward roots terminal) player)
      0 root).mp hstack.1
  exact (quittingRootOpponentAbsorptionMass_mul_debtFloor_le_of_sumDebtDrop_le
    reward root (quittingLiteralRootStackProfile reward roots terminal)
    who debtFloor
    (quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward roots terminal) -
      quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward (root :: roots) terminal))
    hM hreward hnash hfloor le_rfl).trans_lt hstep

/-- A sufficiently accurate stack charges the whole positive endpoint premium
of every macroscopic debtor by the common lexicographic accuracy. -/
theorem quittingLiteralExactStack_step_exercisePremium_le
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (who : ι) (debtFloor : ℝ)
    {accuracy M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hterminalMax : quittingTerminalExploitability reward terminal ≤
      quittingTerminalExploitabilityInf reward + accuracy)
    (hterminalSum : quittingTerminalDebtSum reward terminal <
      sInf (quittingTerminalDebtSumSublevelValues reward
        (quittingTerminalExploitabilityInf reward + accuracy)) + accuracy)
    (hstack : IsQuittingLiteralExactRootStack
      reward (root :: roots) terminal)
    (hfloor : debtFloor ≤ quittingTerminalDeviationDebt reward
      (quittingLiteralRootStackProfile reward roots terminal) who)
    (hsmall : accuracy < debtFloor / 2) :
    quittingRootExercisePremium reward
        (fun player => quittingTerminalPayoff reward
          (quittingLiteralRootStackProfile reward roots terminal) player)
        root who ≤ accuracy := by
  have hstep := quittingTerminalDebtSum_literalExactStack_step_drop_lt
    reward root roots terminal hM hreward hterminalMax hterminalSum hstack
  rw [isQuittingLiteralExactRootStack_cons_iff] at hstack
  have hnash :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward roots terminal) player)
      0 root).mp hstack.1
  have hpremium :=
    quittingRootExercisePremium_le_of_sumDebtDrop_lt_half_debtFloor
      reward root (quittingLiteralRootStackProfile reward roots terminal)
      who debtFloor
      (quittingTerminalDebtSum reward
          (quittingLiteralRootStackProfile reward roots terminal) -
        quittingTerminalDebtSum reward
          (quittingLiteralRootStackProfile reward (root :: roots) terminal))
      hM hreward hnash hfloor le_rfl (hstep.trans hsmall)
  exact hpremium.trans hstep.le

/-- If two coordinates remain macroscopic at a stack node, the displayed
root is quantitatively close to all-Continue in every marginal. -/
theorem quittingLiteralExactStack_step_all_quitProbability_mul_debtFloor_lt
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    {first second : ι} (hdistinct : first ≠ second)
    (debtFloor : ℝ)
    {accuracy M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hterminalMax : quittingTerminalExploitability reward terminal ≤
      quittingTerminalExploitabilityInf reward + accuracy)
    (hterminalSum : quittingTerminalDebtSum reward terminal <
      sInf (quittingTerminalDebtSumSublevelValues reward
        (quittingTerminalExploitabilityInf reward + accuracy)) + accuracy)
    (hstack : IsQuittingLiteralExactRootStack
      reward (root :: roots) terminal)
    (hfloor_nonneg : 0 ≤ debtFloor)
    (hfirst : debtFloor ≤ quittingTerminalDeviationDebt reward
      (quittingLiteralRootStackProfile reward roots terminal) first)
    (hsecond : debtFloor ≤ quittingTerminalDeviationDebt reward
      (quittingLiteralRootStackProfile reward roots terminal) second) :
    ∀ player, (root player true).toReal * debtFloor < accuracy := by
  have hstep := quittingTerminalDebtSum_literalExactStack_step_drop_lt
    reward root roots terminal hM hreward hterminalMax hterminalSum hstack
  rw [isQuittingLiteralExactRootStack_cons_iff] at hstack
  have hnash :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward roots terminal) player)
      0 root).mp hstack.1
  intro player
  exact (quittingRoot_all_quitProbability_mul_debtFloor_le_of_two_debtors
    reward root (quittingLiteralRootStackProfile reward roots terminal)
    hdistinct debtFloor
    (quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward roots terminal) -
      quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward (root :: roots) terminal))
    hM hreward hnash hfloor_nonneg hfirst hsecond le_rfl player).trans_lt hstep

/-- Arbitrarily deep finite literal stacks exist over lexicographic
near-minimizers.  Every dropped suffix remains in the same maximum-debt
sublevel and is within the same total-debt accuracy of the terminal profile.
-/
theorem exists_deep_lexicographicallyNearMinimal_literalExactRootStack
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (depth : ℕ) {accuracy M : ℝ} (haccuracy : 0 < accuracy)
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    ∃ (terminal : (quittingGame reward).BehaviorProfile)
        (roots : List (ι → PMF Bool)),
      roots.length = depth ∧
      IsQuittingLiteralExactRootStack reward roots terminal ∧
      quittingTerminalExploitability reward terminal ≤
        quittingTerminalExploitabilityInf reward + accuracy ∧
      quittingTerminalDebtSum reward terminal <
        sInf (quittingTerminalDebtSumSublevelValues reward
          (quittingTerminalExploitabilityInf reward + accuracy)) + accuracy ∧
      ∀ count,
        quittingTerminalExploitability reward
            (quittingLiteralRootStackProfile reward (roots.drop count) terminal) ≤
          quittingTerminalExploitabilityInf reward + accuracy ∧
        quittingTerminalDebtSum reward
            (quittingLiteralRootStackProfile reward (roots.drop count) terminal) ≤
          quittingTerminalDebtSum reward terminal ∧
        quittingTerminalDebtSum reward terminal -
            quittingTerminalDebtSum reward
              (quittingLiteralRootStackProfile reward (roots.drop count) terminal) <
          accuracy := by
  obtain ⟨terminal, hterminalMax, hterminalSum⟩ :=
    exists_lexicographicallyNearMinimal_terminalProfile
      reward haccuracy hM hreward
  obtain ⟨roots, hlength, hstack⟩ :=
    exists_quittingLiteralExactRootStack reward terminal depth
  refine ⟨terminal, roots, hlength, hstack, hterminalMax, hterminalSum, ?_⟩
  intro count
  have hdropped : IsQuittingLiteralExactRootStack reward
      (roots.drop count) terminal :=
    IsQuittingLiteralExactRootStack.drop
      (reward := reward) (roots := roots) (terminal := terminal) hstack count
  have hmax := quittingTerminalExploitability_literalRootStack_le_terminal
    reward (roots.drop count) terminal hM hreward hdropped
  have hsum : quittingTerminalDebtSum reward
      (quittingLiteralRootStackProfile reward (roots.drop count) terminal) ≤
      quittingTerminalDebtSum reward terminal := by
    unfold quittingTerminalDebtSum
    exact sum_quittingTerminalDeviationDebt_literalRootStack_le_terminal
      reward (roots.drop count) terminal hM hreward hdropped
  have hinfLe :
      sInf (quittingTerminalDebtSumSublevelValues reward
        (quittingTerminalExploitabilityInf reward + accuracy)) ≤
      quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward (roots.drop count) terminal) := by
    apply csInf_le
    · exact bddBelow_quittingTerminalDebtSumSublevelValues reward
        (quittingTerminalExploitabilityInf reward + accuracy) hM hreward
    · exact ⟨quittingLiteralRootStackProfile reward (roots.drop count) terminal,
        hmax.trans hterminalMax, rfl⟩
  refine ⟨hmax.trans hterminalMax, hsum, ?_⟩
  linarith

end GameTheory
