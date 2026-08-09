/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSeam
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeQuantitative
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtConservation

/-!
# Conservation and the positive phantom plateau of a counterexample tail

The canonical optimized exact-D tail of a quitting counterexample has two
complementary limiting descriptions.

First, dynamic debt is an exact survival coordinate.  At every start it is
the sum of debt surviving forever and the weighted diagonal seams discharged
at finite dates.  For the selected positive-debt owner, eventual deleted
survival is exactly a debt ratio, so the additive opponent clock has the
dimensionless ceiling `log (K / eta)`.

Second, the tail is a positive phantom plateau.  Its actual terminal payoff
from late starts tends to zero, whereas the owner's prescribed Bellman value
tends to at least the terminal exploitability gap.  The positive limiting
value therefore lives entirely on the Never boundary.  This rules out the
naive compiler “play the extracted tail” but does not itself realize the
phantom value by an absorbing suffix.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleSeamWitness

variable {regime : QuittingCounterexampleRegime reward}
    (seam : QuittingCounterexampleSeamWitness regime)

/-- The selected owner's limiting prescribed value retains the whole
counterexample margin. -/
theorem terminalGap_le_limitValue :
    regime.terminalGap ≤ seam.limit.value seam.limit.owner :=
  seam.terminalGap_le_limitDebt.trans
    (seam.limit.debt_le_value_of_debt_pos seam.limit.owner
      seam.limit.ownerDebt_pos)

/-- Every positive-debt coordinate of the optimized tail is above its
behavioral punishment floor at every date, not only at the limiting owner. -/
theorem punishmentValue_le_tailValue_of_debt_pos
    (who : ι) (time : ℕ) (hdebt : 0 < (seam.tail time).2 who) :
    quittingPunishmentValue reward who ≤ (seam.tail time).1.1 who :=
  seam.limit.punishmentValue_le_tailValue_of_debt_pos seam.tail
    seam.tail_mem seam.tail_edge seam.value_tendsto seam.debt_tendsto
      who time hdebt

/-- Every coordinate's finite exact debt conservation law on the canonical
tail. -/
theorem debt_conservation (who : ι) (start fuel : ℕ) :
    (seam.tail start).2 who =
      quittingJointSurvivalWeight
          (quittingDynamicDebtTailRoots seam.tail) start fuel *
          (seam.tail (start + fuel)).2 who +
        ∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight
              (quittingDynamicDebtTailRoots seam.tail) start offset *
            quittingDynamicDebtSeam
              (seam.tail (start + offset)) who :=
  quittingDynamicDebtTail_conservation seam.tail seam.tail_mem
    seam.tail_edge who start fuel

/-- Every coordinate's diagonal seam is summable on the optimized tail. -/
theorem dynamicDebtSeam_summable (who : ι) :
    Summable (fun time ↦ quittingDynamicDebtSeam (seam.tail time) who) := by
  apply summable_quittingDynamicDebtSeam_of_summable_absorption
    seam.tail seam.tail_mem
  change Summable (quittingDynamicDebtTailAbsorptionCharge seam.tail)
  exact seam.jointAbsorption_summable

/-- **Infinite exact debt decomposition.**  Current debt is the sum of debt
surviving on the Never event and all earlier survival-weighted diagonal
seams. -/
theorem debt_eq_survivalLimit_mul_limit_add_tsum_weightedSeam
    (who : ι) (start : ℕ) :
    (seam.tail start).2 who =
      quittingJointSurvivalLimit
          (quittingDynamicDebtTailRoots seam.tail) start *
          seam.limit.debt who +
        ∑' offset : ℕ,
          quittingJointSurvivalWeight
              (quittingDynamicDebtTailRoots seam.tail) start offset *
            quittingDynamicDebtSeam
              (seam.tail (start + offset)) who := by
  let weightedSeam : ℕ → ℝ := fun offset ↦
    quittingJointSurvivalWeight
        (quittingDynamicDebtTailRoots seam.tail) start offset *
      quittingDynamicDebtSeam (seam.tail (start + offset)) who
  have hseamShift : Summable (fun offset ↦
      quittingDynamicDebtSeam (seam.tail (start + offset)) who) := by
    have hinjective : Function.Injective (fun offset : ℕ ↦ start + offset) := by
      intro first second heq
      exact Nat.add_left_cancel heq
    exact (seam.dynamicDebtSeam_summable who).comp_injective hinjective
  have hweighted : Summable weightedSeam := by
    apply Summable.of_nonneg_of_le
    · intro offset
      exact mul_nonneg
        (quittingJointSurvivalWeight_nonneg _ start offset)
        (quittingDynamicDebtSeam_nonneg
          (state := seam.tail (start + offset))
          (seam.tail_mem (start + offset)) who)
    · intro offset
      exact mul_le_of_le_one_left
        (quittingDynamicDebtSeam_nonneg
          (state := seam.tail (start + offset))
          (seam.tail_mem (start + offset)) who)
        (quittingJointSurvivalWeight_le_one _ start offset)
    · exact hseamShift
  have hfarDebt : Tendsto
      (fun fuel ↦ (seam.tail (start + fuel)).2 who) atTop
      (nhds (seam.limit.debt who)) := by
    simpa [Function.comp_def, Nat.add_comm] using
      (seam.debt_tendsto who).comp (tendsto_add_atTop_nat start)
  have hterminal :=
    (tendsto_quittingJointSurvivalLimit
      (quittingDynamicDebtTailRoots seam.tail) start).mul hfarDebt
  have hsum : Tendsto
      (fun fuel ↦ ∑ offset ∈ Finset.range fuel, weightedSeam offset)
      atTop (nhds (∑' offset, weightedSeam offset)) :=
    hweighted.hasSum.tendsto_sum_nat
  have hrhs := hterminal.add hsum
  apply tendsto_nhds_unique
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ (seam.tail start).2 who) atTop
      (nhds ((seam.tail start).2 who)))
  apply hrhs.congr
  intro fuel
  exact (seam.debt_conservation who start fuel).symm

/-- From some date onward, the selected owner's deleted survival is an exact
debt ratio and every finite opponent-clock prefix is bounded by
`log (K / eta)`. -/
theorem exists_ownerClockStart_logBound :
    ∃ start : ℕ,
      (∀ time, start ≤ time →
        0 < (quittingDynamicDebtTailRoots seam.tail time
          seam.limit.owner false).toReal) ∧
      ∀ fuel,
        (∑ offset ∈ Finset.range fuel,
          quittingOpponentClockCharge
            (quittingDynamicDebtTailRoots seam.tail) seam.limit.owner
              (start + offset)) ≤
        Real.log
          (quittingPositiveSingletonDebtCap reward seam.limit.owner /
            regime.terminalGap) := by
  have heventually : ∀ᶠ time in atTop,
      0 < (quittingDynamicDebtTailRoots seam.tail time
        seam.limit.owner false).toReal :=
    (seam.continueProbability_tendsto_one seam.limit.owner).eventually_const_lt
      zero_lt_one
  obtain ⟨start, hstart⟩ := (eventually_atTop.1 heventually)
  refine ⟨start, hstart, ?_⟩
  intro fuel
  have hcontinue : ∀ offset, offset < fuel →
      0 < (quittingDynamicDebtTailRoots seam.tail (start + offset)
        seam.limit.owner false).toReal := fun offset _ ↦
    hstart (start + offset) (Nat.le_add_right start offset)
  have hdebtMono := monotone_quittingDynamicDebtTail_debt
    seam.tail seam.tail_mem seam.tail_edge seam.limit.owner
  have hetaStart : regime.terminalGap ≤
      (seam.tail start).2 seam.limit.owner :=
    seam.terminalGap_le_initialDebt.trans
      (hdebtMono (Nat.zero_le start))
  have hstartPos : 0 < (seam.tail start).2 seam.limit.owner :=
    regime.terminalGap_pos.trans_le hetaStart
  have hendPos : 0 < (seam.tail (start + fuel)).2 seam.limit.owner :=
    hstartPos.trans_le (hdebtMono (Nat.le_add_right start fuel))
  have hendNonneg : 0 ≤ (seam.tail (start + fuel)).2 seam.limit.owner :=
    (seam.tail_mem (start + fuel)).2.1 seam.limit.owner
  have hendCap : (seam.tail (start + fuel)).2 seam.limit.owner ≤
      quittingPositiveSingletonDebtCap reward seam.limit.owner :=
    (seam.tail_mem (start + fuel)).2.2 seam.limit.owner
  have hratio :
      (seam.tail (start + fuel)).2 seam.limit.owner /
          (seam.tail start).2 seam.limit.owner ≤
        quittingPositiveSingletonDebtCap reward seam.limit.owner /
          regime.terminalGap :=
    div_le_div₀ (le_max_left _ _) hendCap
      regime.terminalGap_pos hetaStart
  have hlog := sum_quittingOpponentClockCharge_le_log_debtRatio
    (reward := reward) seam.tail seam.tail_mem seam.tail_edge
      seam.limit.owner start fuel hcontinue hstartPos
  exact hlog.trans (Real.log_le_log (div_pos hendPos hstartPos) hratio)

private theorem tailTsum_tendsto_zero
    {f : ℕ → ℝ} (hsummable : Summable f) :
    Tendsto (fun start ↦ ∑' offset : ℕ, f (start + offset))
      atTop (nhds 0) := by
  have hprefix := hsummable.hasSum.tendsto_sum_nat
  have htailEq : ∀ start,
      (∑' offset : ℕ, f (start + offset)) =
        (∑' time : ℕ, f time) - ∑ time ∈ Finset.range start, f time := by
    intro start
    have hsplit := hsummable.sum_add_tsum_nat_add start
    rw [← hsplit]
    simp only [Nat.add_comm]
    ring
  simpa only [htailEq, sub_self] using
    ((tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ ∑' time : ℕ, f time) atTop
        (nhds (∑' time : ℕ, f time))).sub hprefix)

/-- The joint survival probability from a late start tends to one. -/
theorem jointSurvivalLimit_tendsto_one :
    Tendsto (fun start ↦ quittingJointSurvivalLimit
      (quittingDynamicDebtTailRoots seam.tail) start) atTop (nhds 1) := by
  let charge := fun time ↦ quittingRootAbsorptionMass
    (quittingDynamicDebtTailRoots seam.tail time)
  have hsummable : Summable charge := by
    change Summable (quittingDynamicDebtTailAbsorptionCharge seam.tail)
    exact seam.jointAbsorption_summable
  have htail := tailTsum_tendsto_zero hsummable
  have hgap : Tendsto (fun start ↦
      1 - quittingJointSurvivalLimit
        (quittingDynamicDebtTailRoots seam.tail) start) atTop (nhds 0) := by
    apply squeeze_zero
    · intro start
      exact sub_nonneg.mpr
        (le_of_tendsto'
          (tendsto_quittingJointSurvivalLimit
            (quittingDynamicDebtTailRoots seam.tail) start)
          (fun fuel ↦ quittingJointSurvivalWeight_le_one
            (quittingDynamicDebtTailRoots seam.tail) start fuel))
    · intro start
      have hshift : Summable (fun offset ↦
          quittingRootAbsorptionMass
            (quittingDynamicDebtTailRoots seam.tail (start + offset))) := by
        simpa [charge, Nat.add_comm] using
          ((summable_nat_add_iff start).2 hsummable)
      exact one_sub_quittingJointSurvivalLimit_le_tailCharge
        (quittingDynamicDebtTailRoots seam.tail) start
          hshift
    · exact htail
  have hrecover : Tendsto (fun start ↦ 1 -
      (1 - quittingJointSurvivalLimit
        (quittingDynamicDebtTailRoots seam.tail) start))
      atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hgap
  simpa using hrecover

/-- Actual play along later starts of the optimized root sequence delivers
asymptotically zero. -/
theorem terminalValue_tendsto_zero (who : ι) :
    Tendsto (fun start ↦ quittingRootSequenceTerminalValue reward
      (quittingDynamicDebtTailRoots seam.tail) who start)
      atTop (nhds 0) := by
  let charge := fun time ↦ quittingRootAbsorptionMass
    (quittingDynamicDebtTailRoots seam.tail time)
  have hsummable : Summable charge := by
    change Summable (quittingDynamicDebtTailAbsorptionCharge seam.tail)
    exact seam.jointAbsorption_summable
  have htail := tailTsum_tendsto_zero hsummable
  have hbound : ∀ start,
      |quittingRootSequenceTerminalValue reward
        (quittingDynamicDebtTailRoots seam.tail) who start| ≤
          quittingRewardBound reward *
            ∑' offset : ℕ, charge (start + offset) := by
    intro start
    have hshift : Summable (fun offset ↦
        quittingRootAbsorptionMass
          (quittingDynamicDebtTailRoots seam.tail (start + offset))) := by
      simpa [charge, Nat.add_comm] using
        ((summable_nat_add_iff start).2 hsummable)
    exact abs_quittingRootSequenceTerminalValue_le_tailCharge
      reward (quittingDynamicDebtTailRoots seam.tail) who start
        (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward)
        hshift
  have habs : Tendsto (fun start ↦
      |quittingRootSequenceTerminalValue reward
        (quittingDynamicDebtTailRoots seam.tail) who start|)
      atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun _ ↦ abs_nonneg _
    · exact hbound
    · simpa using htail.const_mul (quittingRewardBound reward)
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

/-- **Positive phantom plateau.**  The difference between the prescribed
owner value and honest terminal delivery converges to a limit retaining the
whole counterexample margin. -/
theorem ownerSemanticGap_tendsto_limitValue :
    Tendsto (fun start ↦
      (seam.tail start).1.1 seam.limit.owner -
        quittingRootSequenceTerminalValue reward
          (quittingDynamicDebtTailRoots seam.tail) seam.limit.owner start)
      atTop (nhds (seam.limit.value seam.limit.owner)) := by
  simpa using (seam.value_tendsto seam.limit.owner).sub
    (seam.terminalValue_tendsto_zero seam.limit.owner)

end QuittingCounterexampleSeamWitness

end GameTheory
