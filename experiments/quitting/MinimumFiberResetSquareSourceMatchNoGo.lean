/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import experiments.quitting.CounterfactualAtomMinimumResetSquare

/-!
# Conditional accounting on a minimum-fiber reset square

Putting all four vertices of a commuting unilateral reset square on one
total-semantic-debt fiber does not transport the sign of the second edge to
the parallel source edge.  It gives an exact conservation law instead: on
each face, the moving player's payoff gain is exactly its debt loss and,
because total debt is fixed, exactly the aggregate debt transferred to the
other players.

The theorem below assumes a positive target-side gain, a nonpositive
source-side gain, and equality of the four total debts, and derives the exact
opponent-transfer account.  It does **not** construct a quitting-game square
satisfying those hypotheses.  In particular it is conditional bookkeeping,
not an architectural no-go for source matching on the positive global
minimum fiber.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Minimum-fiber square conservation/no-go.**

Let `source`, `first`, `observerFirst`, and `both` be the four literal
vertices obtained by resetting two distinct players.  If all four vertices
have the same total semantic debt, then on both parallel observer edges the
observer payoff gain is exactly the observer debt loss and the aggregate
opponent debt gain.  Consequently the sign on the target edge supplies no
sign on the source edge: under an explicitly positive target gain and
nonpositive source gain, the two opponent-transport sums have those same
opposite signs.

No minimality premise beyond equality of the four debt totals is used.  The
joint realizability of the displayed sign hypotheses on a positive global
minimum fiber remains open. -/
theorem minimumFiber_resetSquare_sourceMismatch_eq_opponentTransport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : mover ≠ observer)
    (moverTarget : (quittingGame reward).BehaviorStrategy mover)
    (observerResponse : (quittingGame reward).BehaviorStrategy observer)
    (htargetPositive : 0 <
      quittingTerminalPayoff reward
          (Function.update (Function.update source mover moverTarget)
            observer observerResponse) observer -
        quittingTerminalPayoff reward
          (Function.update source mover moverTarget) observer)
    (hsourceNonpositive :
      quittingTerminalPayoff reward
          (Function.update source observer observerResponse) observer -
        quittingTerminalPayoff reward source observer ≤ 0)
    (hfirstFiber :
      quittingTerminalDebtSum reward
          (Function.update source mover moverTarget) =
        quittingTerminalDebtSum reward source)
    (hobserverFirstFiber :
      quittingTerminalDebtSum reward
          (Function.update source observer observerResponse) =
        quittingTerminalDebtSum reward source)
    (hbothFiber :
      quittingTerminalDebtSum reward
          (Function.update (Function.update source mover moverTarget)
            observer observerResponse) =
        quittingTerminalDebtSum reward source) :
    let first := Function.update source mover moverTarget
    let observerFirst := Function.update source observer observerResponse
    let both := Function.update first observer observerResponse
    both = Function.update observerFirst mover moverTarget ∧
      quittingTerminalPayoff reward both observer -
          quittingTerminalPayoff reward first observer =
        quittingTerminalDeviationDebt reward first observer -
          quittingTerminalDeviationDebt reward both observer ∧
      quittingTerminalPayoff reward observerFirst observer -
          quittingTerminalPayoff reward source observer =
        quittingTerminalDeviationDebt reward source observer -
          quittingTerminalDeviationDebt reward observerFirst observer ∧
      0 < ∑ other ∈ Finset.univ.erase observer,
        quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward first)
          (quittingTerminalSemanticPair reward both) other ∧
      (∑ other ∈ Finset.univ.erase observer,
        quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward source)
          (quittingTerminalSemanticPair reward observerFirst) other) ≤ 0 := by
  dsimp only
  let first := Function.update source mover moverTarget
  let observerFirst := Function.update source observer observerResponse
  let both := Function.update first observer observerResponse
  have hcommute : both = Function.update observerFirst mover moverTarget := by
    dsimp only [both, observerFirst, first]
    exact Function.update_comm hne _ _ source
  have htargetDebt :
      quittingTerminalPayoff reward both observer -
          quittingTerminalPayoff reward first observer =
        quittingTerminalDeviationDebt reward first observer -
          quittingTerminalDeviationDebt reward both observer := by
    simp only [quittingTerminalDeviationDebt, both]
    rw [quittingContinuationBestResponseValue_update_self]
    ring
  have hsourceDebt :
      quittingTerminalPayoff reward observerFirst observer -
          quittingTerminalPayoff reward source observer =
        quittingTerminalDeviationDebt reward source observer -
          quittingTerminalDeviationDebt reward observerFirst observer := by
    simp only [quittingTerminalDeviationDebt, observerFirst]
    rw [quittingContinuationBestResponseValue_update_self]
    ring
  have htargetAccount :=
    sum_opponent_debtChange_update_eq_totalChange_add_debtDecrease
      reward first observer observerResponse
  have hsourceAccount :=
    sum_opponent_debtChange_update_eq_totalChange_add_debtDecrease
      reward source observer observerResponse
  have hfirstBoth : quittingTerminalDebtSum reward both =
      quittingTerminalDebtSum reward first := by
    rw [hbothFiber, hfirstFiber]
  have hsourceObserverFirst :
      quittingTerminalDebtSum reward observerFirst =
        quittingTerminalDebtSum reward source := by
    exact hobserverFirstFiber
  have htargetTransport :
      (∑ other ∈ Finset.univ.erase observer,
        quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward first)
          (quittingTerminalSemanticPair reward both) other) =
        quittingTerminalPayoff reward both observer -
          quittingTerminalPayoff reward first observer := by
    dsimp only at htargetAccount
    change (∑ other ∈ Finset.univ.erase observer,
        quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward first)
          (quittingTerminalSemanticPair reward both) other) = _ at htargetAccount
    rw [show quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward both) =
        quittingTerminalDebtSum reward both by rfl,
      show quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward first) =
        quittingTerminalDebtSum reward first by rfl,
      hfirstBoth, sub_self, zero_add] at htargetAccount
    rw [htargetAccount]
    change quittingTerminalDeviationDebt reward first observer -
        quittingTerminalDeviationDebt reward both observer = _
    exact htargetDebt.symm
  have hsourceTransport :
      (∑ other ∈ Finset.univ.erase observer,
        quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward source)
          (quittingTerminalSemanticPair reward observerFirst) other) =
        quittingTerminalPayoff reward observerFirst observer -
          quittingTerminalPayoff reward source observer := by
    dsimp only at hsourceAccount
    change (∑ other ∈ Finset.univ.erase observer,
        quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward source)
          (quittingTerminalSemanticPair reward observerFirst) other) = _ at hsourceAccount
    rw [show quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward observerFirst) =
        quittingTerminalDebtSum reward observerFirst by rfl,
      show quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward source) =
        quittingTerminalDebtSum reward source by rfl,
      hsourceObserverFirst, sub_self, zero_add] at hsourceAccount
    rw [hsourceAccount]
    change quittingTerminalDeviationDebt reward source observer -
        quittingTerminalDeviationDebt reward observerFirst observer = _
    exact hsourceDebt.symm
  refine ⟨hcommute, htargetDebt, hsourceDebt, ?_, ?_⟩
  · rwa [htargetTransport]
  · rwa [hsourceTransport]

end GameTheory
