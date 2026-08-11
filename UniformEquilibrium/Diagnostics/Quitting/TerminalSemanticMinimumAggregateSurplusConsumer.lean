/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumAggregateSurplus
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Exact aggregate-surplus consumers at the minimum semantic plateau

The coarse subset certificate `(|J| - 1)D` pays for a whole copy of total
debt.  Before that relaxation, the auxiliary-target margin gives the sharper
quantity

`sum_{i in J} (D - d_i)`.

This matters on the critical face.  If one singleton-tight owner carries all
debt, every outsider has zero debt, so one common terminal outcome pays the
entire outsider set aggregate surplus `|J|D`.

The sure-exit compiler gives a second, logically independent consumer.  In a
counterexample every nonempty terminal coalition has a strict one-player
toggle blocker.  Hence the common outcome selected by the reward moment is
either Never, with an explicit negative singleton-budget certificate, or one
absorbing coalition carrying both the exact aggregate surplus and a strict
local instability witness.

This is a finite support alternative.  It does not turn the toggle into a
chronological Nash--Bellman edge: changing one member of an already absorbing
coalition changes the terminal atom immediately, and the other coordinates
need not preserve aggregate surplus.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## The exact subset budget -/

/-- The unrelaxed subset form of the minimum-semantic singleton margin. -/
theorem minimumTerminalSemantic_subset_singletonSurplus_exact
    (pair : QuittingTerminalSemanticPair ι) (players : Finset ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) :
    (∑ who ∈ players,
        (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebt pair who)) ≤
      ∑ who ∈ players,
        (pair.1 who - reward (quittingSingletonTerminal who) who) := by
  apply Finset.sum_le_sum
  intro who hwho
  have hmargin := minimumTerminalSemantic_singletonMargin
    (reward := reward) pair hM hreward hpair hminimum hpositive who
  unfold quittingTerminalSemanticDebt at hmargin ⊢
  linarith

/-- One common terminal outcome carries the exact debt-sensitive subset
surplus. -/
theorem exists_terminalOutcome_subset_singletonSurplus_ge_exactMinimumDebt
    (pair : QuittingTerminalSemanticPair ι) (players : Finset ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) :
    ∃ outcome : QuittingTerminalOutcome ι,
      (∑ who ∈ players,
          (quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebt pair who)) ≤
        ∑ who ∈ players,
          (quittingTerminalOutcomeReward reward outcome who -
            reward (quittingSingletonTerminal who) who) := by
  obtain ⟨outcome, houtcome⟩ :=
    exists_terminalOutcome_subset_singletonSurplus_ge_prescribed
      (reward := reward) pair players hpair
  exact ⟨outcome,
    (minimumTerminalSemantic_subset_singletonSurplus_exact
      (reward := reward) pair players hM hreward hpair hminimum hpositive).trans
      houtcome⟩

/-- The common high-surplus outcome can be selected in the positive support
of one reward-moment representation of the prescribed semantic value. -/
theorem exists_rewardMoment_supportOutcome_subset_singletonSurplus_ge_prescribed
    (pair : QuittingTerminalSemanticPair ι) (players : Finset ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    ∃ mass : QuittingTerminalOutcome ι → ℝ,
      mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) ∧
        quittingTerminalRewardMoment reward mass = pair.1 ∧
        ∃ outcome : QuittingTerminalOutcome ι,
          0 < mass outcome ∧
            (∑ who ∈ players,
                (pair.1 who -
                  reward (quittingSingletonTerminal who) who)) ≤
              ∑ who ∈ players,
                (quittingTerminalOutcomeReward reward outcome who -
                  reward (quittingSingletonTerminal who) who) := by
  obtain ⟨mass, hmass, hmoment⟩ :=
    quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet
      reward pair hpair
  refine ⟨mass, hmass, hmoment, ?_⟩
  have hmassNe : mass ≠ 0 := by
    intro hzero
    have := hmass.2
    simp [hzero] at this
  obtain ⟨positiveOutcome, hpositiveOutcome⟩ :=
    Function.ne_iff.mp hmassNe
  have hpositiveMass : 0 < mass positiveOutcome :=
    lt_of_le_of_ne (hmass.1 positiveOutcome)
      (Ne.symm hpositiveOutcome)
  by_contra hnot
  have hstrict : ∀ outcome, 0 < mass outcome →
      (∑ who ∈ players,
          (quittingTerminalOutcomeReward reward outcome who -
            reward (quittingSingletonTerminal who) who)) <
        ∑ who ∈ players,
          (pair.1 who -
            reward (quittingSingletonTerminal who) who) := by
    intro outcome houtcome
    exact lt_of_not_ge fun hge => hnot ⟨outcome, houtcome, hge⟩
  have hterm : ∀ outcome,
      mass outcome *
          (∑ who ∈ players,
            (quittingTerminalOutcomeReward reward outcome who -
              reward (quittingSingletonTerminal who) who)) ≤
        mass outcome *
          (∑ who ∈ players,
            (pair.1 who -
              reward (quittingSingletonTerminal who) who)) := by
    intro outcome
    by_cases hzero : mass outcome = 0
    · simp [hzero]
    · apply mul_le_mul_of_nonneg_left _ (hmass.1 outcome)
      exact (hstrict outcome
        (lt_of_le_of_ne (hmass.1 outcome) (Ne.symm hzero))).le
  have hstrictPositive :
      mass positiveOutcome *
          (∑ who ∈ players,
            (quittingTerminalOutcomeReward reward positiveOutcome who -
              reward (quittingSingletonTerminal who) who)) <
        mass positiveOutcome *
          (∑ who ∈ players,
            (pair.1 who -
              reward (quittingSingletonTerminal who) who)) :=
    mul_lt_mul_of_pos_left
      (hstrict positiveOutcome hpositiveMass) hpositiveMass
  have hsumLt :
      (∑ outcome, mass outcome *
        (∑ who ∈ players,
          (quittingTerminalOutcomeReward reward outcome who -
            reward (quittingSingletonTerminal who) who))) <
      ∑ outcome, mass outcome *
        (∑ who ∈ players,
          (pair.1 who -
            reward (quittingSingletonTerminal who) who)) := by
    apply Finset.sum_lt_sum
    · intro outcome _
      exact hterm outcome
    · exact ⟨positiveOutcome, Finset.mem_univ _, hstrictPositive⟩
  have hleft :
      (∑ outcome, mass outcome *
        (∑ who ∈ players,
          (quittingTerminalOutcomeReward reward outcome who -
            reward (quittingSingletonTerminal who) who))) =
      ∑ who ∈ players,
        (pair.1 who -
          reward (quittingSingletonTerminal who) who) := by
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
          (pair.1 who -
            reward (quittingSingletonTerminal who) who))) =
      ∑ who ∈ players,
        (pair.1 who -
          reward (quittingSingletonTerminal who) who) := by
    rw [← Finset.sum_mul, hmass.2, one_mul]
  rw [hleft, hright] at hsumLt
  exact lt_irrefl _ hsumLt

/-- Positive-support version of the exact minimum-debt certificate. -/
theorem exists_rewardMoment_supportOutcome_subset_singletonSurplus_ge_exactMinimumDebt
    (pair : QuittingTerminalSemanticPair ι) (players : Finset ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) :
    ∃ mass : QuittingTerminalOutcome ι → ℝ,
      mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) ∧
        quittingTerminalRewardMoment reward mass = pair.1 ∧
        ∃ outcome : QuittingTerminalOutcome ι,
          0 < mass outcome ∧
            (∑ who ∈ players,
                (quittingTerminalSemanticDebtSum pair -
                  quittingTerminalSemanticDebt pair who)) ≤
              ∑ who ∈ players,
                (quittingTerminalOutcomeReward reward outcome who -
                  reward (quittingSingletonTerminal who) who) := by
  obtain ⟨mass, hmass, hmoment, outcome, hsupport, houtcome⟩ :=
    exists_rewardMoment_supportOutcome_subset_singletonSurplus_ge_prescribed
      (reward := reward) pair players hpair
  exact ⟨mass, hmass, hmoment, outcome, hsupport,
    (minimumTerminalSemantic_subset_singletonSurplus_exact
      (reward := reward) pair players hM hreward hpair hminimum hpositive).trans
      houtcome⟩

/-! ## Sure-exit consumption -/

/-- Every nonempty pure terminal coalition in a counterexample has a strict
toggle blocker.  A member can profit by staying behind, or an outsider can
profit by joining. -/
theorem QuittingCounterexampleRegime.terminalCoalition_has_strictToggle
    (regime : QuittingCounterexampleRegime reward)
    (terminal : {S : Finset ι // S.Nonempty}) :
    (∃ member ∈ terminal.val,
        quittingSetReward reward terminal.val member <
          quittingSetReward reward (terminal.val.erase member) member) ∨
      ∃ outsider ∉ terminal.val,
        quittingSetReward reward terminal.val outsider <
          quittingSetReward reward (insert outsider terminal.val) outsider := by
  by_cases hmember : ∃ member ∈ terminal.val,
      quittingSetReward reward terminal.val member <
        quittingSetReward reward (terminal.val.erase member) member
  · exact Or.inl hmember
  by_cases houtsider : ∃ outsider ∉ terminal.val,
      quittingSetReward reward terminal.val outsider <
        quittingSetReward reward (insert outsider terminal.val) outsider
  · exact Or.inr houtsider
  exfalso
  have hsure : IsQuittingSureExitSet reward terminal.val := by
    constructor
    · intro member hmem
      exact le_of_not_gt fun hgt => hmember ⟨member, hmem, hgt⟩
    · intro outsider hout
      exact le_of_not_gt fun hgt => houtsider ⟨outsider, hout, hgt⟩
  exact regime.not_exists_uniformEquilibriumPayoff
    ⟨quittingSetReward reward terminal.val,
      isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
        reward hsure⟩

/-- Exact finite support alternative.  The moment witness is either Never,
which forces the displayed singleton-budget inequality, or an absorbing
coalition with the same aggregate surplus and a strict toggle blocker. -/
theorem QuittingCounterexampleRegime.exists_neverBudget_or_blockedCoalition_exact
    (regime : QuittingCounterexampleRegime reward)
    (pair : QuittingTerminalSemanticPair ι) (players : Finset ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) :
    (∑ who ∈ players,
        (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebt pair who)) ≤
        ∑ who ∈ players,
          (0 - reward (quittingSingletonTerminal who) who) ∨
      ∃ terminal : {S : Finset ι // S.Nonempty},
        (∑ who ∈ players,
            (quittingTerminalSemanticDebtSum pair -
              quittingTerminalSemanticDebt pair who)) ≤
            ∑ who ∈ players,
              (reward terminal who -
                reward (quittingSingletonTerminal who) who) ∧
          ((∃ member ∈ terminal.val,
              quittingSetReward reward terminal.val member <
                quittingSetReward reward (terminal.val.erase member) member) ∨
            ∃ outsider ∉ terminal.val,
              quittingSetReward reward terminal.val outsider <
                quittingSetReward reward
                  (insert outsider terminal.val) outsider) := by
  obtain ⟨outcome, houtcome⟩ :=
    exists_terminalOutcome_subset_singletonSurplus_ge_exactMinimumDebt
      (reward := reward) pair players hM hreward hpair hminimum hpositive
  cases outcome with
  | none =>
      left
      simpa [quittingTerminalOutcomeReward] using houtcome
  | some terminal =>
      right
      refine ⟨terminal, ?_, regime.terminalCoalition_has_strictToggle terminal⟩
      simpa [quittingTerminalOutcomeReward] using houtcome

/-- Support-retaining form of the finite counterexample alternative.  The
Never or coalition witness has positive mass in one explicit reward-moment
representation of the prescribed minimum value. -/
theorem QuittingCounterexampleRegime.exists_supportedNever_or_supportedBlockedCoalition_exact
    (regime : QuittingCounterexampleRegime reward)
    (pair : QuittingTerminalSemanticPair ι) (players : Finset ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) :
    ∃ mass : QuittingTerminalOutcome ι → ℝ,
      mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) ∧
        quittingTerminalRewardMoment reward mass = pair.1 ∧
        ((0 < mass none ∧
            (∑ who ∈ players,
                (quittingTerminalSemanticDebtSum pair -
                  quittingTerminalSemanticDebt pair who)) ≤
              ∑ who ∈ players,
                (0 - reward (quittingSingletonTerminal who) who)) ∨
          ∃ terminal : {S : Finset ι // S.Nonempty},
            0 < mass (some terminal) ∧
              (∑ who ∈ players,
                  (quittingTerminalSemanticDebtSum pair -
                    quittingTerminalSemanticDebt pair who)) ≤
                ∑ who ∈ players,
                  (reward terminal who -
                    reward (quittingSingletonTerminal who) who) ∧
              ((∃ member ∈ terminal.val,
                  quittingSetReward reward terminal.val member <
                    quittingSetReward reward
                      (terminal.val.erase member) member) ∨
                ∃ outsider ∉ terminal.val,
                  quittingSetReward reward terminal.val outsider <
                    quittingSetReward reward
                      (insert outsider terminal.val) outsider)) := by
  obtain ⟨mass, hmass, hmoment, outcome, hsupport, houtcome⟩ :=
    exists_rewardMoment_supportOutcome_subset_singletonSurplus_ge_exactMinimumDebt
      (reward := reward) pair players hM hreward hpair hminimum hpositive
  refine ⟨mass, hmass, hmoment, ?_⟩
  cases outcome with
  | none =>
      left
      exact ⟨hsupport, by
        simpa [quittingTerminalOutcomeReward] using houtcome⟩
  | some terminal =>
      right
      exact ⟨terminal, hsupport, by
        simpa [quittingTerminalOutcomeReward] using houtcome,
        regime.terminalCoalition_has_strictToggle terminal⟩

/-- If Never cannot pay the exact subset budget, the common witness is a
genuine absorbing coalition and necessarily has a strict toggle blocker. -/
theorem QuittingCounterexampleRegime.exists_blockedCoalition_exact_of_never_lt
    (regime : QuittingCounterexampleRegime reward)
    (pair : QuittingTerminalSemanticPair ι) (players : Finset ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnever :
      (∑ who ∈ players,
          (0 - reward (quittingSingletonTerminal who) who)) <
        ∑ who ∈ players,
          (quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebt pair who)) :
    ∃ terminal : {S : Finset ι // S.Nonempty},
      (∑ who ∈ players,
          (quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebt pair who)) ≤
          ∑ who ∈ players,
            (reward terminal who -
              reward (quittingSingletonTerminal who) who) ∧
        ((∃ member ∈ terminal.val,
            quittingSetReward reward terminal.val member <
              quittingSetReward reward (terminal.val.erase member) member) ∨
          ∃ outsider ∉ terminal.val,
            quittingSetReward reward terminal.val outsider <
              quittingSetReward reward
                (insert outsider terminal.val) outsider) := by
  rcases regime.exists_neverBudget_or_blockedCoalition_exact
      pair players hM hreward hpair hminimum hpositive with
    hneverBudget | hterminal
  · exact (not_le_of_gt hnever hneverBudget).elim
  · exact hterminal

/-! ## The critical owner face -/

/-- If one coordinate carries the whole total debt, every other coordinate
has zero debt. -/
theorem minimumTerminalSemantic_debt_eq_zero_of_ne_of_debt_eq_sum
    (pair : QuittingTerminalSemanticPair ι) (owner other : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hne : other ≠ owner)
    (howner : quittingTerminalSemanticDebt pair owner =
      quittingTerminalSemanticDebtSum pair) :
    quittingTerminalSemanticDebt pair other = 0 := by
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hpairLe : quittingTerminalSemanticDebt pair owner +
      quittingTerminalSemanticDebt pair other ≤
        quittingTerminalSemanticDebtSum pair := by
    calc
      quittingTerminalSemanticDebt pair owner +
          quittingTerminalSemanticDebt pair other =
        ∑ who ∈ ({owner, other} : Finset ι),
          quittingTerminalSemanticDebt pair who := by
            simp [Ne.symm hne]
      _ ≤ ∑ who ∈ (Finset.univ : Finset ι),
          quittingTerminalSemanticDebt pair who := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.subset_univ _
            · intro who _ _
              exact hdebtNonneg who
      _ = quittingTerminalSemanticDebtSum pair := rfl
  rw [howner] at hpairLe
  exact le_antisymm (by linarith) (hdebtNonneg other)

/-- At a singleton-tight minimum coordinate, one common terminal outcome pays
`D` of aggregate surplus for every outsider. -/
theorem exists_terminalOutcome_outsiderSurplus_ge_card_mul_minimumDebt_of_tight
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (htight : pair.1 owner =
      reward (quittingSingletonTerminal owner) owner) :
    ∃ outcome : QuittingTerminalOutcome ι,
      ((Finset.univ.erase owner).card : ℝ) *
          quittingTerminalSemanticDebtSum pair ≤
        ∑ who ∈ Finset.univ.erase owner,
          (quittingTerminalOutcomeReward reward outcome who -
            reward (quittingSingletonTerminal who) who) := by
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hownerLe : quittingTerminalSemanticDebt pair owner ≤
      quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun who _ => hdebtNonneg who) (Finset.mem_univ owner)
  have hmargin := minimumTerminalSemantic_singletonMargin
    (reward := reward) pair hM hreward hpair hminimum hpositive owner
  have hsumLeOwner : quittingTerminalSemanticDebtSum pair ≤
      quittingTerminalSemanticDebt pair owner := by
    unfold quittingTerminalSemanticDebt
    rw [htight]
    exact hmargin
  have howner : quittingTerminalSemanticDebt pair owner =
      quittingTerminalSemanticDebtSum pair :=
    le_antisymm hownerLe hsumLeOwner
  obtain ⟨outcome, houtcome⟩ :=
    exists_terminalOutcome_subset_singletonSurplus_ge_exactMinimumDebt
      (reward := reward) pair (Finset.univ.erase owner) hM hreward hpair
        hminimum hpositive
  refine ⟨outcome, ?_⟩
  have hzero : ∀ who ∈ Finset.univ.erase owner,
      quittingTerminalSemanticDebt pair who = 0 := by
    intro who hwho
    apply minimumTerminalSemantic_debt_eq_zero_of_ne_of_debt_eq_sum
      (reward := reward) pair owner who hM hreward hpair
    · exact (Finset.mem_erase.mp hwho).1
    · exact howner
  calc
    ((Finset.univ.erase owner).card : ℝ) *
        quittingTerminalSemanticDebtSum pair =
      ∑ who ∈ Finset.univ.erase owner,
        quittingTerminalSemanticDebtSum pair := by simp
    _ = ∑ who ∈ Finset.univ.erase owner,
        (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebt pair who) := by
            apply Finset.sum_congr rfl
            intro who hwho
            rw [hzero who hwho, sub_zero]
    _ ≤ _ := houtcome

/-- Counterexample form of the critical-owner certificate.  One common
outsider-funding outcome is either Never or a locally unstable absorbing
coalition. -/
theorem QuittingCounterexampleRegime.exists_neverBudget_or_blockedCoalition_of_tightOwner
    (regime : QuittingCounterexampleRegime reward)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (htight : pair.1 owner =
      reward (quittingSingletonTerminal owner) owner) :
    ((Finset.univ.erase owner).card : ℝ) *
          quittingTerminalSemanticDebtSum pair ≤
        ∑ who ∈ Finset.univ.erase owner,
          (0 - reward (quittingSingletonTerminal who) who) ∨
      ∃ terminal : {S : Finset ι // S.Nonempty},
        ((Finset.univ.erase owner).card : ℝ) *
              quittingTerminalSemanticDebtSum pair ≤
            ∑ who ∈ Finset.univ.erase owner,
              (reward terminal who -
                reward (quittingSingletonTerminal who) who) ∧
          ((∃ member ∈ terminal.val,
              quittingSetReward reward terminal.val member <
                quittingSetReward reward (terminal.val.erase member) member) ∨
            ∃ outsider ∉ terminal.val,
              quittingSetReward reward terminal.val outsider <
                quittingSetReward reward
                  (insert outsider terminal.val) outsider) := by
  obtain ⟨outcome, houtcome⟩ :=
    exists_terminalOutcome_outsiderSurplus_ge_card_mul_minimumDebt_of_tight
      (reward := reward) pair owner hM hreward hpair hminimum hpositive htight
  cases outcome with
  | none =>
      left
      simpa [quittingTerminalOutcomeReward] using houtcome
  | some terminal =>
      right
      refine ⟨terminal, ?_, regime.terminalCoalition_has_strictToggle terminal⟩
      simpa [quittingTerminalOutcomeReward] using houtcome

/-- In the first unresolved dimension and above, a tight critical owner
leaves at least three units of minimum debt in one common outsider aggregate.
The same outcome is either Never or an absorbing coalition with a strict
toggle blocker. -/
theorem QuittingCounterexampleRegime.exists_threeDebt_neverBudget_or_blockedCoalition_of_tightOwner
    (regime : QuittingCounterexampleRegime reward)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {M : ℝ}
    (hcard : 4 ≤ Fintype.card ι)
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (htight : pair.1 owner =
      reward (quittingSingletonTerminal owner) owner) :
    3 * quittingTerminalSemanticDebtSum pair ≤
        ∑ who ∈ Finset.univ.erase owner,
          (0 - reward (quittingSingletonTerminal who) who) ∨
      ∃ terminal : {S : Finset ι // S.Nonempty},
        3 * quittingTerminalSemanticDebtSum pair ≤
            ∑ who ∈ Finset.univ.erase owner,
              (reward terminal who -
                reward (quittingSingletonTerminal who) who) ∧
          ((∃ member ∈ terminal.val,
              quittingSetReward reward terminal.val member <
                quittingSetReward reward (terminal.val.erase member) member) ∨
            ∃ outsider ∉ terminal.val,
              quittingSetReward reward terminal.val outsider <
                quittingSetReward reward
                  (insert outsider terminal.val) outsider) := by
  have hcardErase : 3 ≤ (Finset.univ.erase owner).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ owner)]
    simpa using Nat.sub_le_sub_right hcard 1
  have hcardReal : (3 : ℝ) ≤ ((Finset.univ.erase owner).card : ℝ) := by
    exact_mod_cast hcardErase
  have hthree : 3 * quittingTerminalSemanticDebtSum pair ≤
      ((Finset.univ.erase owner).card : ℝ) *
        quittingTerminalSemanticDebtSum pair :=
    mul_le_mul_of_nonneg_right hcardReal hpositive.le
  rcases regime.exists_neverBudget_or_blockedCoalition_of_tightOwner
      pair owner hM hreward hpair hminimum hpositive htight with
    hnever | ⟨terminal, hterminal, htoggle⟩
  · exact Or.inl (hthree.trans hnever)
  · exact Or.inr ⟨terminal, hthree.trans hterminal, htoggle⟩

end GameTheory
