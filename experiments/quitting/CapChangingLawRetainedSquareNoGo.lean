/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import experiments.quitting.UniqueAllContinueCapStackNoGo

/-!
# Cap-changing exact prefixes remain debt-budgeted

A change of the behavioral cap is not, by itself, an escape from the
positive-minimum telescope.  Start from any literal unilateral reset of an
executable profile and then prefix an arbitrary finite word of roots, each
chosen exact Nash against the behavioral cap of its actual suffix.  Even
though the cap is recomputed and can change at every row, the unweighted
absorption charge of the whole word is bounded by the reset profile's
ordinary total-debt excess above the positive semantic minimum.

At zero excess the statement is sharper: every root in the word is literally
all-Continue, the profile and complete terminal law are unchanged, and a
retained atom remains a suffix atom rather than becoming current absorption.

This is an architectural no-go, not a counterexample-regime closure.  It
rules out the proposed ``off-budget charge'' output for every construction
made only of exact cap--Nash prefixes after one cap-changing reset.  A useful
square must therefore use its other edge: a source-matched signed reset gain,
or an operation not governed by exact cap debt scaling.  The retained law,
the fixed-law premium, and endpoint commutation alone do not alter this
calculation.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The positive semantic minimum charges every absorption hazard in an
arbitrary finite, state-changing cap--Nash word.  Unlike the earlier maximal
root specialization, no root selector is fixed here. -/
theorem semanticMinimum_mul_capNashStackAbsorptionSum_le_debtDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (roots : List (ι → PMF Bool)) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    quittingTerminalSemanticDebtSum minimum *
        quittingCapNashStackAbsorptionSum roots ≤
      quittingTerminalDebtSum reward terminal -
        quittingTerminalDebtSum reward
          (quittingLiteralRootStackProfile reward roots terminal) := by
  induction roots with
  | nil => simp [quittingCapNashStackAbsorptionSum]
  | cons root roots ih =>
      rw [isQuittingCapNashRootStack_cons_iff] at hstack
      let suffix := quittingLiteralRootStackProfile reward roots terminal
      have hsuffixMinimum : quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalDebtSum reward suffix := by
        have hle := hminimum
          (quittingTerminalSemanticPair reward suffix)
          (quittingTerminalSemanticPair_mem_carrier reward suffix)
        simpa [quittingTerminalSemanticDebtSum,
          quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
          quittingTerminalDebtSum, quittingTerminalDeviationDebt] using hle
      have habsorption : 0 ≤ quittingRootAbsorptionMass root :=
        quittingRootAbsorptionMass_nonneg root
      have hlocal : quittingTerminalSemanticDebtSum minimum *
            quittingRootAbsorptionMass root ≤
          quittingTerminalDebtSum reward suffix *
            quittingRootAbsorptionMass root :=
        mul_le_mul_of_nonneg_right hsuffixMinimum habsorption
      have hscale :=
        quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
          (reward := reward) root suffix hM hreward hstack.1
      have htail := ih hstack.2
      change quittingTerminalSemanticDebtSum minimum *
          (quittingRootAbsorptionMass root +
            quittingCapNashStackAbsorptionSum roots) ≤
        quittingTerminalDebtSum reward terminal -
          quittingTerminalDebtSum reward
            (quittingRootThenContinuationProfile reward root suffix)
      unfold quittingRootAbsorptionMass at hlocal ⊢
      dsimp [suffix] at hsuffixMinimum hlocal hscale
      rw [hscale]
      nlinarith

/-- **Cap-changing square no-go.**  Perform one literal unilateral reset,
then any finite exact cap--Nash word.  Its charge is bounded by the ordinary
debt excess of that reset endpoint.  If the reset endpoint itself lies on the
minimum fiber, every exact row is all-Continue and the complete retained law
is unchanged.

The atom premise is deliberately literal.  The final clause shows that at
zero excess it remains positive in the unchanged suffix law, but it cannot be
promoted into current absorption by the exact cap word. -/
theorem literalReset_capNashStack_debtBudget_or_identity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (roots : List (ι → PMF Bool))
    (atom : {S : Finset ι // S.Nonempty}) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hstack : IsQuittingCapNashRootStack reward roots
      (Function.update profile mover target))
    (hatom : 0 < quittingTerminalOutcomeMass reward
      (Function.update profile mover target) (some atom)) :
    quittingCapNashStackAbsorptionSum roots ≤
        (quittingTerminalDebtSum reward
              (Function.update profile mover target) -
            quittingTerminalSemanticDebtSum minimum) /
          quittingTerminalSemanticDebtSum minimum ∧
      (quittingTerminalSemanticDebtSum minimum <
          quittingTerminalDebtSum reward
            (Function.update profile mover target) ∨
        (roots = List.replicate roots.length
              (quittingAllContinueRoot : ι → PMF Bool) ∧
          quittingTerminalSemanticPair reward
              (quittingLiteralRootStackProfile reward roots
                (Function.update profile mover target)) =
            quittingTerminalSemanticPair reward
              (Function.update profile mover target) ∧
          quittingTerminalOutcomeMass reward
              (quittingLiteralRootStackProfile reward roots
                (Function.update profile mover target)) (some atom) =
            quittingTerminalOutcomeMass reward
              (Function.update profile mover target) (some atom) ∧
          0 < quittingTerminalOutcomeMass reward
              (quittingLiteralRootStackProfile reward roots
                (Function.update profile mover target)) (some atom))) := by
  let reset := Function.update profile mover target
  have hbudget :=
    semanticMinimum_mul_capNashStackAbsorptionSum_le_debtDrop
      reward minimum reset roots hM hreward hminimum hstack
  have hstackMinimum : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward roots reset) := by
    have hle := hminimum
      (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots reset))
      (quittingTerminalSemanticPair_mem_carrier reward _)
    simpa [quittingTerminalSemanticDebtSum,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
      quittingTerminalDebtSum, quittingTerminalDeviationDebt] using hle
  have habsorptionBound : quittingCapNashStackAbsorptionSum roots ≤
      (quittingTerminalDebtSum reward reset -
          quittingTerminalSemanticDebtSum minimum) /
        quittingTerminalSemanticDebtSum minimum := by
    apply (le_div_iff₀ hminimumPositive).2
    nlinarith
  refine ⟨by simpa only [reset] using habsorptionBound, ?_⟩
  have hresetMinimum : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalDebtSum reward reset := by
    have hle := hminimum
      (quittingTerminalSemanticPair reward reset)
      (quittingTerminalSemanticPair_mem_carrier reward reset)
    simpa [quittingTerminalSemanticDebtSum,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
      quittingTerminalDebtSum, quittingTerminalDeviationDebt] using hle
  rcases hresetMinimum.eq_or_lt with heq | hstrict
  · right
    have hunique : ∀ candidate : ι → PMF Bool,
        IsεQuittingRootNash reward
            (quittingTerminalSemanticPair reward reset).2 0 candidate →
          candidate = (quittingAllContinueRoot : ι → PMF Bool) := by
      intro candidate hnash
      let prefixed := quittingRootThenContinuationProfile reward candidate reset
      have hprefixedMinimum : quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalDebtSum reward prefixed := by
        have hle := hminimum
          (quittingTerminalSemanticPair reward prefixed)
          (quittingTerminalSemanticPair_mem_carrier reward prefixed)
        simpa [quittingTerminalSemanticDebtSum,
          quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
          quittingTerminalDebtSum, quittingTerminalDeviationDebt] using hle
      have hscale :=
        quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
          (reward := reward) candidate reset hM hreward hnash
      have hresetPositive : 0 < quittingTerminalDebtSum reward reset := by
        rw [← heq]
        exact hminimumPositive
      have hcontinueLe := quittingStationaryContinueMass_le_one candidate
      have hcontinue : quittingStationaryContinueMass candidate = 1 := by
        dsimp only [prefixed] at hprefixedMinimum
        rw [hscale, heq] at hprefixedMinimum
        nlinarith
      funext who
      simpa [quittingAllContinueRoot] using
        eq_pure_false_of_quittingStationaryContinueMass_eq_one
          hcontinue who
    have hstackData :=
      capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap
        reward reset roots hM hreward hunique hstack
    have hlaw :=
      capNashRootStack_terminalOutcomeMass_eq_of_unique_terminalCap
        reward reset roots hM hreward hunique hstack
    refine ⟨hstackData.1, ?_, ?_, ?_⟩
    · simpa only [reset] using hstackData.2
    · exact congrFun hlaw (some atom)
    · rw [hlaw]
      exact hatom
  · exact Or.inl (by simpa only [reset] using hstrict)

end GameTheory
