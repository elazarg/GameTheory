/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOffDiagonalStaticOrientationDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge

/-!
# A strict insertion atom is blind or debt-budgeted at an exact prefix

The static singleton handoff supplies a player `owner`, a nonempty opponent
coalition `quitters`, and a positive insertion gap.  This file marks that atom
inside an arbitrary exact semantic prefix.  Its strategically usable part is
the minimum of

* the opponent-coalition incidence times the insertion gap;
* the owner's literal suffix debt; and
* the owner's positive net root exercise premium.

The exact survival-block identity implies that this marked use is at most the
owner's coordinate debt drop, hence at most total debt drop.  At a global
minimum it vanishes.  More sharply, every exact minimum-fiber row either gives
the atom zero incidence, or exposes it only on a zero-debt owner whose net
exercise premium is zero.

This is an architectural no-go for consuming the ambient static insertion
atom.  It does not close the singleton stopping-law leaf: the missing producer
must put the marked atom on a source-matched exact face exit or return edge.
The cap-prefix logarithmic account is not repeated here; it is already covered
by the cap-stack debt-budget no-go modules.
-/

noncomputable section

namespace GameTheory
namespace SingletonMarkedUseDebtBudgetNoGo

open Math.Probability Math.SurvivalWeightedObstruction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Probability that exactly `quitters` Quit among the opponents of `owner`.
The owner's own marginal is erased by forcing it to Continue. -/
def quittingInsertionOpponentMass
    (root : ι → PMF Bool) (owner : ι) (quitters : Finset ι) : ℝ :=
  quittingRootCoalitionMass
    (Function.update root owner (PMF.pure false)) quitters

/-- Positive reward increment attached to a strict insertion atom. -/
def quittingInsertionGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (quitters : Finset ι) (hquitters : quitters.Nonempty) : ℝ :=
  reward
      ⟨insert owner quitters, Finset.insert_nonempty owner quitters⟩ owner -
    reward ⟨quitters, hquitters⟩ owner

/-- Source-matched part of a static insertion atom at one semantic prefix.
Gross atom incidence is useful only to the extent that the same owner has
suffix debt and the exact root retains a positive net exercise premium. -/
def quittingMarkedInsertionUse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (owner : ι) (quitters : Finset ι) (hquitters : quitters.Nonempty) : ℝ :=
  min
    (quittingInsertionOpponentMass root owner quitters *
      quittingInsertionGap reward owner quitters hquitters)
    (min (quittingTerminalSemanticDebt pair owner)
      (quittingRootExercisePremium reward pair.1 root owner))

theorem quittingInsertionOpponentMass_nonneg
    (root : ι → PMF Bool) (owner : ι) (quitters : Finset ι) :
    0 ≤ quittingInsertionOpponentMass root owner quitters := by
  exact MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg _ _

theorem quittingMarkedInsertionUse_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (owner : ι) (quitters : Finset ι) (hquitters : quitters.Nonempty)
    (hgap : 0 ≤ quittingInsertionGap reward owner quitters hquitters)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair owner) :
    0 ≤ quittingMarkedInsertionUse
      reward pair root owner quitters hquitters := by
  unfold quittingMarkedInsertionUse
  apply le_min
  · exact mul_nonneg
      (quittingInsertionOpponentMass_nonneg root owner quitters) hgap
  · exact le_min hdebt
      (quittingRootExercisePremium_nonneg reward pair.1 root owner)

private theorem min_debt_charge_le_debt_sub_act
    (block : Block Unit) {debt : ℝ} (hdebt : 0 ≤ debt) :
    min debt (block.charge.value ()) ≤ debt - block.act () debt := by
  have haccount := block.debt_sub_act_eq_killed_add_min () hdebt
  have hsurvivedNonneg : 0 ≤ block.survival * debt :=
    mul_nonneg block.survival_nonneg hdebt
  have hkilledNonneg : 0 ≤ (1 - block.survival) * debt :=
    mul_nonneg (sub_nonneg.mpr block.survival_le_one) hdebt
  by_cases hdebtCharge : debt ≤ block.charge.value ()
  · have hsurvivedCharge :
        block.survival * debt ≤ block.charge.value () :=
      (mul_le_of_le_one_left hdebt block.survival_le_one).trans hdebtCharge
    rw [min_eq_left hdebtCharge]
    rw [min_eq_left hsurvivedCharge] at haccount
    linarith
  · have hchargeDebt : block.charge.value () ≤ debt :=
      le_of_not_ge hdebtCharge
    rw [min_eq_right hchargeDebt]
    by_cases hchargeSurvived :
        block.charge.value () ≤ block.survival * debt
    · rw [min_eq_right hchargeSurvived] at haccount
      linarith
    · have hsurvivedCharge :
          block.survival * debt ≤ block.charge.value () :=
        le_of_not_ge hchargeSurvived
      rw [min_eq_left hsurvivedCharge] at haccount
      have hsurvivedLeDebt : block.survival * debt ≤ debt :=
        mul_le_of_le_one_left hdebt block.survival_le_one
      linarith

/-- **Marked-use debt budget.**  At an exact root against the prescribed
suffix coordinate, the usable portion of any marked insertion atom is paid
by that owner's literal semantic-debt drop. -/
theorem quittingMarkedInsertionUse_le_coordinateDebtDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (owner : ι) (quitters : Finset ι) (hquitters : quitters.Nonempty)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair owner)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingMarkedInsertionUse reward pair root owner quitters hquitters ≤
      quittingTerminalSemanticDebt pair owner -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) owner := by
  have huse : quittingMarkedInsertionUse
      reward pair root owner quitters hquitters ≤
      min (quittingTerminalSemanticDebt pair owner)
        (quittingRootExercisePremium reward pair.1 root owner) := by
    exact min_le_right _ _
  rw [quittingTerminalSemanticDebt_prefix_eq_blockAct
    reward pair root owner hdebt hnash]
  exact huse.trans (by
    simpa [quittingTerminalSemanticDebtBlock] using
      min_debt_charge_le_debt_sub_act
        (quittingTerminalSemanticDebtBlock reward pair root owner) hdebt)

/-- The same marked use is bounded by total semantic-debt drop. -/
theorem quittingMarkedInsertionUse_le_totalDebtDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (owner : ι) (quitters : Finset ι) (hquitters : quitters.Nonempty)
    (hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingMarkedInsertionUse reward pair root owner quitters hquitters ≤
      quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root pair) := by
  have hcoordinate := quittingMarkedInsertionUse_le_coordinateDebtDrop
    reward pair root owner quitters hquitters (hdebt owner) hnash
  have hotherNonneg : ∀ who ∈ (Finset.univ : Finset ι),
      0 ≤ quittingTerminalSemanticDebt pair who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) who := by
    intro who _
    exact sub_nonneg.mpr
      (quittingTerminalSemanticDebt_prefix_le
        reward pair root who (hdebt who) hnash)
  have hcoordinateSum :
      quittingTerminalSemanticDebt pair owner -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root pair) owner ≤
        ∑ who, (quittingTerminalSemanticDebt pair who -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root pair) who) :=
    Finset.single_le_sum hotherNonneg (Finset.mem_univ owner)
  apply hcoordinate.trans
  simpa [quittingTerminalSemanticDebtSum, Finset.sum_sub_distrib] using
    hcoordinateSum

/-- On the global minimum fiber, every nonnegative marked insertion use is
zero.  Thus a strict static atom cannot itself be a positively charged exact
predecessor at the minimum. -/
theorem quittingMarkedInsertionUse_eq_zero_of_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (owner : ι) (quitters : Finset ι) (hquitters : quitters.Nonempty)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hgap : 0 ≤ quittingInsertionGap reward owner quitters hquitters) :
    quittingMarkedInsertionUse reward pair root owner quitters hquitters = 0 := by
  have hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have huseNonneg := quittingMarkedInsertionUse_nonneg
    reward pair root owner quitters hquitters hgap (hdebt owner)
  have huseDrop := quittingMarkedInsertionUse_le_coordinateDebtDrop
    reward pair root owner quitters hquitters (hdebt owner) hnash
  have heq := quittingTerminalSemanticDebt_prefix_eq_of_minimum
    reward pair root hM hreward hpair hminimum hnash owner
  rw [heq, sub_self] at huseDrop
  exact le_antisymm huseDrop huseNonneg

/-- **Minimum-fiber blindness/cancellation dichotomy.**  If the minimum total
debt is positive, every exact row sees a marked insertion coalition in only
one of two ways: its opponent incidence is zero, or the atom owner has zero
source debt and zero net exercise premium. -/
theorem insertionAtom_blind_or_zeroDebt_cancelled_of_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (owner : ι) (quitters : Finset ι) (hquitters : quitters.Nonempty)
    (howner : owner ∉ quitters)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingInsertionOpponentMass root owner quitters = 0 ∨
      (quittingTerminalSemanticDebt pair owner = 0 ∧
        quittingRootExercisePremium reward pair.1 root owner = 0) := by
  have hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  by_cases hownerDebt : 0 < quittingTerminalSemanticDebt pair owner
  · left
    obtain ⟨other, hother⟩ := hquitters
    have hotherNe : other ≠ owner := by
      intro heq
      subst other
      exact howner hother
    have hotherZero : (root other true).toReal = 0 :=
      quittingTerminalSemantic_minimum_positiveDebt_opponents_quit_eq_zero
        reward pair root hM hreward hpair hminimum hnash
          hownerDebt hotherNe
    have hmassLe : quittingInsertionOpponentMass root owner quitters ≤
        ((Function.update root owner (PMF.pure false)) other true).toReal :=
      quittingRootCoalitionMass_le_quitProbability_of_mem
        (Function.update root owner (PMF.pure false)) quitters other hother
    rw [Function.update_of_ne hotherNe, hotherZero] at hmassLe
    exact le_antisymm hmassLe
      (quittingInsertionOpponentMass_nonneg root owner quitters)
  · right
    have hownerZero : quittingTerminalSemanticDebt pair owner = 0 :=
      le_antisymm (le_of_not_gt hownerDebt) (hdebt owner)
    have hexistsPositive : ∃ who, 0 < quittingTerminalSemanticDebt pair who := by
      by_contra hnone
      push Not at hnone
      have hsumNonpos : quittingTerminalSemanticDebtSum pair ≤ 0 := by
        unfold quittingTerminalSemanticDebtSum
        exact Finset.sum_nonpos fun who _ => hnone who
      linarith
    obtain ⟨debtor, hdebtor⟩ := hexistsPositive
    have hownerNe : owner ≠ debtor := by
      intro heq
      subst debtor
      linarith
    have hownerQuitZero : (root owner true).toReal = 0 :=
      quittingTerminalSemantic_minimum_positiveDebt_opponents_quit_eq_zero
        reward pair root hM hreward hpair hminimum hnash
          hdebtor hownerNe
    have hendpoint :=
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward pair.1 root).mpr hnash
    have hdiff :=
      quittingRootEndpointDifference_nonpos_of_quitProbability_eq_zero
        reward pair.1 root owner hendpoint hownerQuitZero
    refine ⟨hownerZero, ?_⟩
    unfold quittingRootExercisePremium
    rw [max_eq_left hdiff]

end SingletonMarkedUseDebtBudgetNoGo
end GameTheory

namespace GameTheory.SingletonMarkedUseDebtBudgetNoGo

#print axioms quittingMarkedInsertionUse_le_coordinateDebtDrop
#print axioms quittingMarkedInsertionUse_le_totalDebtDrop
#print axioms quittingMarkedInsertionUse_eq_zero_of_minimum
#print axioms insertionAtom_blind_or_zeroDebt_cancelled_of_minimum

end GameTheory.SingletonMarkedUseDebtBudgetNoGo
