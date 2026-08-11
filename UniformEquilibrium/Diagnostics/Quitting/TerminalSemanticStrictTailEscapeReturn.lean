/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetExcursionReturn

/-!
# The exact return threshold for a strict semantic tail escape

A literal semantic prefix is oriented backward: a root prefixes its shifted
tail to produce the current point.  Consequently a shifted tail strictly
above the global minimum-debt fiber is compatible with a lower current point;
absorption at the prefix can consume precisely that excess.

This file isolates the minimal scalar premise needed to turn such an escape
into a cap--Nash return.  For an exact Nash root against the tail's displayed
cap, the absorption charge

`D(tail) * rootAbsorption`

is at most the tail excess above the global minimum.  It returns within
`tolerance` of that minimum exactly when it spends all but `tolerance` of the
excess.  On the cap-dominating singleton face the all-Continue exact Nash root
spends zero, so a strict escape may stall without contradiction.

The result is debt-semantic only.  Using it as a reset excursion additionally
requires a reset coordinate at the shifted tail; retaining an old terminal
law additionally requires positive all-Continue survival.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- **Exact oriented escape account.**

An exact cap--Nash prefix of an attainable shifted tail subtracts exactly its
absorption charge from total semantic debt.  Global minimality bounds that
charge by the tail's excess.  Thus positive absorption is compatible with a
strict tail escape; it is the mechanism by which the backward prefix can land
closer to the minimum. -/
theorem capNashPrefix_tailEscape_exact_account
    (minimum tail : QuittingTerminalSemanticPair iota)
    (root : iota → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward tail.2 0 root) :
    let returned := quittingTerminalSemanticPrefix reward root tail
    returned ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum returned ∧
      quittingTerminalSemanticDebtSum returned =
        quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum tail *
            quittingRootAbsorptionMass root ∧
      quittingTerminalSemanticDebtSum tail *
          quittingRootAbsorptionMass root ≤
        quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum := by
  let returned := quittingTerminalSemanticPrefix reward root tail
  have hreturned : returned ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier
      reward root tail hM hreward htail
  have hminimumReturned : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum returned :=
    hminimum returned hreturned
  have hscale : quittingTerminalSemanticDebtSum returned =
      quittingStationaryContinueMass root *
        quittingTerminalSemanticDebtSum tail :=
    quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) tail root hnash
  have haccount : quittingTerminalSemanticDebtSum returned =
      quittingTerminalSemanticDebtSum tail -
        quittingTerminalSemanticDebtSum tail *
          quittingRootAbsorptionMass root := by
    unfold quittingRootAbsorptionMass
    rw [hscale]
    ring
  refine ⟨hreturned, hminimumReturned, haccount, ?_⟩
  linarith

/-- The cap--Nash return-selection inequality is not merely sufficient: it
is exactly equivalent to the prefixed point entering the requested
minimum-debt neighborhood. -/
theorem capNashReturnSelection_iff_tailEscape_prefix_nearMinimum
    (minimum tail : QuittingTerminalSemanticPair iota)
    (root : iota → PMF Bool) (tolerance : ℝ)
    (hnash : IsεQuittingRootNash reward tail.2 0 root) :
    IsQuittingCapNashResetReturnSelection
        (reward := reward) minimum tail root tolerance ↔
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root tail) ≤
        quittingTerminalSemanticDebtSum minimum + tolerance := by
  have hscale : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward root tail) =
      quittingStationaryContinueMass root *
        quittingTerminalSemanticDebtSum tail :=
    quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) tail root hnash
  have haccount : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward root tail) =
      quittingTerminalSemanticDebtSum tail -
        quittingTerminalSemanticDebtSum tail *
          quittingRootAbsorptionMass root := by
    unfold quittingRootAbsorptionMass
    rw [hscale]
    ring
  constructor
  · intro hselection
    rw [haccount]
    linarith [hselection.2]
  · intro hnear
    refine ⟨hnash, ?_⟩
    rw [haccount] at hnear
    linarith

/-- **Generic strict-escape stall.**

If the shifted tail's displayed cap dominates every singleton reward, the
all-Continue root is exact cap--Nash and fixes the tail.  At a strict escape
it therefore fails every zero-tolerance return selection.  Exact Nash
existence alone supplies no return or Lyapunov contradiction. -/
theorem strictTailEscape_allContinue_stalls
    (minimum tail : QuittingTerminalSemanticPair iota)
    (hescape : quittingTerminalSemanticDebtSum minimum <
      quittingTerminalSemanticDebtSum tail)
    (hcap : ∀ player,
      reward (quittingSingletonTerminal player) player ≤ tail.2 player) :
    IsεQuittingRootNash reward tail.2 0
        (quittingAllContinueRoot : iota → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot tail =
        tail ∧
      quittingRootAbsorptionMass
          (quittingAllContinueRoot : iota → PMF Bool) = 0 ∧
      ¬ IsQuittingCapNashResetReturnSelection
          (reward := reward) minimum tail
            (quittingAllContinueRoot : iota → PMF Bool) 0 := by
  have hnash : IsεQuittingRootNash reward tail.2 0
      (quittingAllContinueRoot : iota → PMF Bool) :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward tail.2).2 hcap
  have hfixed :=
    quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap
      (reward := reward) tail hcap
  refine ⟨hnash, hfixed, quittingRootAbsorptionMass_allContinueRoot, ?_⟩
  intro hselection
  unfold IsQuittingCapNashResetReturnSelection at hselection
  rw [quittingRootAbsorptionMass_allContinueRoot] at hselection
  norm_num at hselection
  linarith [hselection.2]

end GameTheory
