/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauFractionalResetFloor
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionWindow

/-!
# Nash provenance of a macroscopic semantic atom

A non-singleton atom exposed on an actual live row already has a common
continuation: the terminal payoff of the all-Continue spine beginning at the
next date.  What need not hold is Nash provenance of that same row.

At a positive minimum semantic debt, this is not merely a missing compactness
argument.  A collision atom of mass `a` and a row which is `ε`-Nash against
its own shifted tail obey the quantitative obstruction

`a * Dmin <= tailExcess + card ι * ε`.

Consequently a macroscopic collision over a tail returning to the minimum
fiber cannot simultaneously have vanishing row-Nash error.  Any use of a
near-sure or sure-exit replacement compiler must therefore obtain its Nash
certificate before returning to the positive minimum tail, or spend a
macroscopic tail excursion.  Merely Nashifying the marked row while retaining
the atom is impossible in the relevant limiting regime.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An `ε`-Nash product root has coordinate Nash defect at most `ε`.
This is the exact bridge between the repository's root-Nash predicate and
the defect accounting used by the minimum-semantic theory. -/
theorem quittingRootCoordinateNashDefect_le_of_isεQuittingRootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (ε : ℝ)
    (hnash : IsεQuittingRootNash reward tail ε root) :
    quittingRootCoordinateNashDefect reward tail root who ≤ ε := by
  have hquit := hnash who (PMF.pure true)
  have hcontinue := hnash who (PMF.pure false)
  change quittingRootQuitPayoff reward tail root who ≤
      quittingRootSuccessorPayoff reward tail root who + ε at hquit
  change quittingRootContinuePayoff reward tail root who ≤
      quittingRootSuccessorPayoff reward tail root who + ε at hcontinue
  unfold quittingRootCoordinateNashDefect
  have hmax := max_le hquit hcontinue
  linarith

/-- Total local Nash defect of an `ε`-Nash root is at most
`card ι * ε`. -/
theorem quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (ε : ℝ)
    (hnash : IsεQuittingRootNash reward tail ε root) :
    quittingRootTotalNashDefect reward tail root ≤ Fintype.card ι * ε := by
  unfold quittingRootTotalNashDefect
  calc
    (∑ who, quittingRootCoordinateNashDefect reward tail root who) ≤
        ∑ _who : ι, ε :=
      Finset.sum_le_sum fun who _ =>
        quittingRootCoordinateNashDefect_le_of_isεQuittingRootNash
          reward tail root who ε hnash
    _ = Fintype.card ι * ε := by simp

/-- **Macroscopic-atom Nash-provenance obstruction.**  A non-singleton
coalition atom at an `ε`-Nash row is paid by the shifted tail's excess above
the minimum semantic debt, plus at most `card ι * ε` of local Nash error.

All objects are co-realized: the atom, root, and tail in the conclusion are
the very objects supplied in the hypotheses. -/
theorem coalitionMass_mul_minimumDebt_le_tailExcess_add_card_mul_nashError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum tail : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (terminal : {S : Finset ι // S.Nonempty}) (ε : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward)
    (hcollision : 1 < terminal.val.card)
    (hnash : IsεQuittingRootNash reward tail.1 ε root) :
    quittingRootCoalitionMass root terminal.val *
        quittingTerminalSemanticDebtSum minimum ≤
      (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        Fintype.card ι * ε := by
  have hatom :=
    quittingRootCoalitionMass_mul_minimumDebt_le_tailExcess_add_defect
      reward minimum tail root terminal hM hreward hminimumCarrier hminimum
        htail hcollision
  have hdefect :=
    quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
      reward tail.1 root ε hnash
  linarith

/-- A singleton atom has the complementary-face version of the same
obstruction.  Its owner does not absorb that owner's own debt, but it absorbs
every other player's debt.  Thus an approximately Nash macroscopic singleton
near the minimum fiber can persist only when the shifted-tail debt collapses
toward the singleton owner's vertex. -/
theorem singletonMass_mul_otherDebt_le_tailExcess_add_card_mul_nashError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum tail : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (owner : ι) (ε : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward tail.1 ε root) :
    quittingRootCoalitionMass root {owner} *
        (∑ who ∈ (Finset.univ : Finset ι).erase owner,
          quittingTerminalSemanticDebt tail who) ≤
      (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        Fintype.card ι * ε := by
  have htailDebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward htail
  have hcoordinate : ∀ who ∈ (Finset.univ : Finset ι).erase owner,
      quittingRootCoalitionMass root {owner} *
          quittingTerminalSemanticDebt tail who ≤
        quittingRootOpponentAbsorptionMass root who *
          quittingTerminalSemanticDebt tail who := by
    intro who hwho
    have hne : owner ≠ who := (Finset.mem_erase.mp hwho).1.symm
    exact mul_le_mul_of_nonneg_right
      (quittingRootCoalitionMass_le_opponentAbsorptionMass_of_other_mem
        root {owner} who owner (by simp) hne)
      (htailDebt who)
  have herase := Finset.sum_le_sum hcoordinate
  have hownerCharge : 0 ≤
      quittingRootOpponentAbsorptionMass root owner *
        quittingTerminalSemanticDebt tail owner :=
    mul_nonneg (quittingRootOpponentAbsorptionMass_nonneg root owner)
      (htailDebt owner)
  have heraseToFull :
      (∑ who ∈ (Finset.univ : Finset ι).erase owner,
          quittingRootOpponentAbsorptionMass root who *
            quittingTerminalSemanticDebt tail who) ≤
        ∑ who, quittingRootOpponentAbsorptionMass root who *
          quittingTerminalSemanticDebt tail who := by
    calc
      _ ≤ (∑ who ∈ (Finset.univ : Finset ι).erase owner,
            quittingRootOpponentAbsorptionMass root who *
              quittingTerminalSemanticDebt tail who) +
          quittingRootOpponentAbsorptionMass root owner *
            quittingTerminalSemanticDebt tail owner :=
        le_add_of_nonneg_right hownerCharge
      _ = _ := Finset.sum_erase_add _ _ (Finset.mem_univ owner)
  have hcharge :=
    minimumTerminalSemantic_sum_opponentAbsorption_charge_le_excess_add_defect
      reward minimum tail root hM hreward hminimumCarrier hminimum htail
  have hdefect :=
    quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
      reward tail.1 root ε hnash
  calc
    quittingRootCoalitionMass root {owner} *
        (∑ who ∈ (Finset.univ : Finset ι).erase owner,
          quittingTerminalSemanticDebt tail who) =
      ∑ who ∈ (Finset.univ : Finset ι).erase owner,
        quittingRootCoalitionMass root {owner} *
          quittingTerminalSemanticDebt tail who := by rw [Finset.mul_sum]
    _ ≤ ∑ who ∈ (Finset.univ : Finset ι).erase owner,
        quittingRootOpponentAbsorptionMass root who *
          quittingTerminalSemanticDebt tail who := herase
    _ ≤ ∑ who, quittingRootOpponentAbsorptionMass root who *
          quittingTerminalSemanticDebt tail who := heraseToFull
    _ ≤ (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        quittingRootTotalNashDefect reward tail.1 root := hcharge
    _ ≤ (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        Fintype.card ι * ε := by linarith

/-- On the minimum tail itself, a macroscopic approximately Nash singleton
forces the complementary debt face to be small. -/
theorem singletonMass_mul_minimumOtherDebt_le_card_mul_nashError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (owner : ι) (ε : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward minimum.1 ε root) :
    quittingRootCoalitionMass root {owner} *
        (∑ who ∈ (Finset.univ : Finset ι).erase owner,
          quittingTerminalSemanticDebt minimum who) ≤
      Fintype.card ι * ε := by
  simpa using singletonMass_mul_otherDebt_le_tailExcess_add_card_mul_nashError
    reward minimum minimum root owner ε hM hreward hminimumCarrier hminimum
      hminimumCarrier hnash

/-- Strictly more collision charge than tail excursion plus row-Nash error
rules out an `ε`-Nash certificate on the displayed root. -/
theorem not_isεQuittingRootNash_of_tailExcess_add_card_mul_lt_collisionDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum tail : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (terminal : {S : Finset ι // S.Nonempty}) (ε : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward)
    (hcollision : 1 < terminal.val.card)
    (hstrict :
      (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
          Fintype.card ι * ε <
        quittingRootCoalitionMass root terminal.val *
          quittingTerminalSemanticDebtSum minimum) :
    ¬ IsεQuittingRootNash reward tail.1 ε root := by
  intro hnash
  exact (not_lt_of_ge
    (coalitionMass_mul_minimumDebt_le_tailExcess_add_card_mul_nashError
      reward minimum tail root terminal ε hM hreward hminimumCarrier hminimum
        htail hcollision hnash)) hstrict

/-- Actual-profile specialization.  The live row and its next-date
all-Continue spine provide the common continuation automatically; a
macroscopic collision can be `ε`-Nash there only by paying the displayed
shifted-tail excursion. -/
theorem profileLiveRoot_coalitionMass_mul_minimumDebt_le_tailExcess_add_card_mul_nashError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (time : ℕ) (terminal : {S : Finset ι // S.Nonempty}) (ε : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hcollision : 1 < terminal.val.card)
    (hnash : IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))).1 ε
      (quittingProfileLiveRoot reward profile time)) :
    quittingRootCoalitionMass
          (quittingProfileLiveRoot reward profile time) terminal.val *
        quittingTerminalSemanticDebtSum minimum ≤
      (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1))) -
          quittingTerminalSemanticDebtSum minimum) +
        Fintype.card ι * ε := by
  apply coalitionMass_mul_minimumDebt_le_tailExcess_add_card_mul_nashError
    reward minimum
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1)))
      (quittingProfileLiveRoot reward profile time) terminal ε hM hreward
      hminimumCarrier hminimum
      (quittingTerminalSemanticPair_mem_carrier reward _) hcollision hnash

/-- **Global-deviation provenance of the same-profile obstruction.**

No local Nash hypothesis is assumed.  The collision floor first charges the
actual live root's total coordinate defect.  Each coordinate defect is then
implemented by a legal one-row behavioral deviation and bounded by that
player's initial best-response debt.  Hence the full initial terminal debt,
not an independently chosen normal-form error, pays for the atom.

The left side is the unconditional stage-cylinder mass times the positive
minimum debt.  The only other payment is the same profile's shifted-tail
excursion, weighted by its actual live mass. -/
theorem stageCoalitionMass_mul_minimumDebt_le_liveMass_mul_tailExcess_add_initialDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (time : ℕ) (terminal : {S : Finset ι // S.Nonempty}) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hcollision : 1 < terminal.val.card) :
    quittingStageCoalitionMass reward profile time terminal *
        quittingTerminalSemanticDebtSum minimum ≤
      quittingLiveMass reward profile time *
          (quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile (time + 1))) -
            quittingTerminalSemanticDebtSum minimum) +
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) := by
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  let root := quittingProfileLiveRoot reward profile time
  have htail : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have hatom :=
    quittingRootCoalitionMass_mul_minimumDebt_le_tailExcess_add_defect
      reward minimum tail root terminal hM hreward hminimumCarrier hminimum
        htail hcollision
  have hlive0 : 0 ≤ quittingLiveMass reward profile time :=
    quittingLiveMass_nonneg reward profile time
  have hscaled := mul_le_mul_of_nonneg_left hatom hlive0
  have hcoordinate : ∀ who,
      quittingLiveMass reward profile time *
          quittingRootCoordinateNashDefect reward tail.1 root who ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who := by
    intro who
    simpa only [tail, root] using
      quittingLiveMass_mul_coordinateNashDefect_le_initialDebt
        (reward := reward) profile who time hM hreward
  have htotal :
      quittingLiveMass reward profile time *
          quittingRootTotalNashDefect reward tail.1 root ≤
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) := by
    unfold quittingRootTotalNashDefect quittingTerminalSemanticDebtSum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun who _ => hcoordinate who
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  change quittingLiveMass reward profile time *
        quittingRootCoalitionMass root terminal.val *
          quittingTerminalSemanticDebtSum minimum ≤ _
  change quittingLiveMass reward profile time *
      (quittingRootCoalitionMass root terminal.val *
        quittingTerminalSemanticDebtSum minimum) ≤ _ at hscaled
  calc
    _ ≤ quittingLiveMass reward profile time *
          ((quittingTerminalSemanticDebtSum tail -
              quittingTerminalSemanticDebtSum minimum) +
            quittingRootTotalNashDefect reward tail.1 root) := by
      simpa only [mul_assoc] using hscaled
    _ = quittingLiveMass reward profile time *
          (quittingTerminalSemanticDebtSum tail -
            quittingTerminalSemanticDebtSum minimum) +
        quittingLiveMass reward profile time *
          quittingRootTotalNashDefect reward tail.1 root := by ring
    _ ≤ quittingLiveMass reward profile time *
          (quittingTerminalSemanticDebtSum tail -
            quittingTerminalSemanticDebtSum minimum) +
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) :=
      by linarith
    _ = _ := by rfl

end GameTheory
