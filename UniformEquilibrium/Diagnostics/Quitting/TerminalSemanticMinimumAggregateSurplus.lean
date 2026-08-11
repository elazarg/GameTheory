/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment

/-!
# Aggregate singleton surplus at a minimum semantic plateau

The auxiliary-target budget gives every coordinate of a positive minimum
semantic pair a singleton margin of at least the total debt.  Summing those
margins over a player subset and paying for its debt coordinates leaves the
sharp lower bound `(|J| - 1)D` on prescribed surplus above own singleton
rewards.

Carrier provenance supplies a common terminal reward moment.  Consequently
the aggregate surplus is not merely assembled from player-dependent
best-response laws: one common terminal outcome carries the full subset
bound.  This is a finite reward-table certificate.  It does not by itself
lift that outcome to a marked minimum-semantic prefix row.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Every player subset carries at least `(|J|-1)D` prescribed surplus above
its members' own singleton rewards.  This is the summed form of the auxiliary
Nash singleton margin; the subtraction of one copy of `D` pays for all debt
coordinates in the subset. -/
theorem minimumTerminalSemantic_subset_singletonSurplus
    (pair : QuittingTerminalSemanticPair ι) (players : Finset ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) :
    ((players.card : ℝ) - 1) * quittingTerminalSemanticDebtSum pair ≤
      ∑ who ∈ players,
        (pair.1 who - reward (quittingSingletonTerminal who) who) := by
  have hdebtNonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hsubsetDebt :
      (∑ who ∈ players, quittingTerminalSemanticDebt pair who) ≤
        quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ players)
    intro who _ _
    exact hdebtNonneg who
  have hcoordinate : ∀ who ∈ players,
      quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebt pair who ≤
        pair.1 who - reward (quittingSingletonTerminal who) who := by
    intro who _
    have hmargin := minimumTerminalSemantic_singletonMargin
      (reward := reward) pair hM hreward hpair hminimum hpositive who
    unfold quittingTerminalSemanticDebt at hmargin ⊢
    linarith
  have hsum := Finset.sum_le_sum hcoordinate
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  calc
    ((players.card : ℝ) - 1) * quittingTerminalSemanticDebtSum pair ≤
        (players.card : ℝ) * quittingTerminalSemanticDebtSum pair -
          ∑ who ∈ players, quittingTerminalSemanticDebt pair who := by
      nlinarith
    _ ≤ ∑ who ∈ players,
        (pair.1 who - reward (quittingSingletonTerminal who) who) := by
      simpa [Finset.sum_sub_distrib] using hsum

/-- A reward moment cannot hide the subset surplus in different coordinates:
one common terminal outcome carries at least the prescribed aggregate. -/
theorem exists_terminalOutcome_subset_singletonSurplus_ge_prescribed
    (pair : QuittingTerminalSemanticPair ι) (players : Finset ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    ∃ outcome : QuittingTerminalOutcome ι,
      (∑ who ∈ players,
          (pair.1 who - reward (quittingSingletonTerminal who) who)) ≤
        ∑ who ∈ players,
          (quittingTerminalOutcomeReward reward outcome who -
            reward (quittingSingletonTerminal who) who) := by
  obtain ⟨mass, hmass, hmoment⟩ :=
    quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet
      reward pair hpair
  by_contra hnot
  push Not at hnot
  have hmassNe : mass ≠ 0 := by
    intro hzero
    have := hmass.2
    simp [hzero] at this
  obtain ⟨positiveOutcome, hpositiveOutcome⟩ :=
    Function.ne_iff.mp hmassNe
  have hpositiveMass : 0 < mass positiveOutcome :=
    lt_of_le_of_ne (hmass.1 positiveOutcome)
      (Ne.symm hpositiveOutcome)
  have hterm : ∀ outcome,
      mass outcome *
          (∑ who ∈ players,
            (quittingTerminalOutcomeReward reward outcome who -
              reward (quittingSingletonTerminal who) who)) ≤
        mass outcome *
          (∑ who ∈ players,
            (pair.1 who - reward (quittingSingletonTerminal who) who)) := by
    intro outcome
    exact mul_le_mul_of_nonneg_left (hnot outcome).le (hmass.1 outcome)
  have hstrict :
      mass positiveOutcome *
          (∑ who ∈ players,
            (quittingTerminalOutcomeReward reward positiveOutcome who -
              reward (quittingSingletonTerminal who) who)) <
        mass positiveOutcome *
          (∑ who ∈ players,
            (pair.1 who - reward (quittingSingletonTerminal who) who)) :=
    mul_lt_mul_of_pos_left (hnot positiveOutcome) hpositiveMass
  have hsumLt :
      (∑ outcome, mass outcome *
        (∑ who ∈ players,
          (quittingTerminalOutcomeReward reward outcome who -
            reward (quittingSingletonTerminal who) who))) <
      ∑ outcome, mass outcome *
        (∑ who ∈ players,
          (pair.1 who - reward (quittingSingletonTerminal who) who)) := by
    apply Finset.sum_lt_sum
    · intro outcome _
      exact hterm outcome
    · exact ⟨positiveOutcome, Finset.mem_univ _, hstrict⟩
  have hleft :
      (∑ outcome, mass outcome *
        (∑ who ∈ players,
          (quittingTerminalOutcomeReward reward outcome who -
            reward (quittingSingletonTerminal who) who))) =
      ∑ who ∈ players,
        (pair.1 who - reward (quittingSingletonTerminal who) who) := by
    simp_rw [Finset.mul_sum, mul_sub]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro who hwho
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass.2, one_mul]
    have hcoordinate := congrFun hmoment who
    unfold quittingTerminalRewardMoment at hcoordinate
    rw [hcoordinate]
  have hright :
      (∑ outcome, mass outcome *
        (∑ who ∈ players,
          (pair.1 who - reward (quittingSingletonTerminal who) who))) =
      ∑ who ∈ players,
        (pair.1 who - reward (quittingSingletonTerminal who) who) := by
    rw [← Finset.sum_mul, hmass.2, one_mul]
  rw [hleft, hright] at hsumLt
  exact lt_irrefl _ hsumLt

/-- Search-facing common-atom certificate for a positive minimum plateau. -/
theorem exists_terminalOutcome_subset_singletonSurplus_ge_minimumDebt
    (pair : QuittingTerminalSemanticPair ι) (players : Finset ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) :
    ∃ outcome : QuittingTerminalOutcome ι,
      ((players.card : ℝ) - 1) * quittingTerminalSemanticDebtSum pair ≤
        ∑ who ∈ players,
          (quittingTerminalOutcomeReward reward outcome who -
            reward (quittingSingletonTerminal who) who) := by
  obtain ⟨outcome, houtcome⟩ :=
    exists_terminalOutcome_subset_singletonSurplus_ge_prescribed
      (reward := reward) pair players hpair
  exact ⟨outcome,
    (minimumTerminalSemantic_subset_singletonSurplus
      (reward := reward) pair players hM hreward hpair hminimum hpositive).trans
      houtcome⟩

end GameTheory
