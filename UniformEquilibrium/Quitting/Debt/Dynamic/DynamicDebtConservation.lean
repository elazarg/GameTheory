/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtCapBridge
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtProjectiveTail
import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity

/-!
# Exact conservation and clock identities for dynamic debt

The augmented-cap seam has a second, equivalent reading directly on the
dynamic debt.  Along one exact edge,

`d_t i = c_t d_(t+1) i + p_t(i) d_t i`,

where `c_t` is joint Continue mass and `p_t(i)` is player `i`'s prescribed
Quit probability.  Iteration gives an exact weighted conservation law: the
current debt is the surviving terminal debt plus all earlier diagonal seams.
Thus the seam is not an informal discrepancy; it is the literal part of the
debt consumed by prescribed quitting.

When player `i` has positive prescribed Continue probability, the stronger
deleted-clock identity also holds:

`d_t i = c^(-i)_t d_(t+1) i`.

Consequently a positive-debt segment identifies its opponent-survival
product exactly with a debt ratio and gives a logarithmic additive-clock
bound.  These are finite identities.  This module does not claim that the
augmented cap is realized by a terminal profile or that an arbitrary cap can
be spliced onto a pre-existing prefix.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The diagonal amount of player `who`'s dynamic debt consumed at one
displayed root. -/
def quittingDynamicDebtSeam
    (state : QuittingDebtPoint ι) (who : ι) : ℝ :=
  (quittingRootOfSimplex state.1.2 who true).toReal * state.2 who

/-- One exact dynamic-debt edge satisfies literal debt conservation. -/
theorem quittingDynamicDebt_eq_continueMass_mul_add_seam
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hsuccessorDebt : 0 ≤ successor.2) (who : ι) :
    current.2 who =
      quittingStationaryContinueMass
          (quittingRootOfSimplex current.1.2) * successor.2 who +
        quittingDynamicDebtSeam current who := by
  have hcapSeam := quittingDynamicDebtCap_sub_rootSuccessorPayoff_eq
    reward current successor hedge hsuccessorDebt who
  have htail := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    reward (quittingDynamicDebtCap successor) successor.1.1
      (quittingRootOfSimplex current.1.2) who
  have hpolicy := congrFun hedge.1.1 who
  simp only [quittingDynamicDebtCap_apply] at hcapSeam htail
  unfold quittingDynamicDebtSeam
  linarith

omit [DecidableEq ι] in
/-- Dynamic debt is nonnegative on the canonical compact box. -/
theorem quittingDynamicDebtSeam_nonneg
    (state : QuittingDebtPoint ι) (hbox : state ∈ quittingDebtBox reward)
    (who : ι) :
    0 ≤ quittingDynamicDebtSeam state who :=
  mul_nonneg ENNReal.toReal_nonneg (hbox.2.1 who)

omit [DecidableEq ι] in
/-- A diagonal seam is paid for by the corresponding one-stage joint
absorption mass and the singleton debt cap. -/
theorem quittingDynamicDebtSeam_le_cap_mul_absorptionMass
    (state : QuittingDebtPoint ι) (hbox : state ∈ quittingDebtBox reward)
    (who : ι) :
    quittingDynamicDebtSeam state who ≤
      quittingPositiveSingletonDebtCap reward who *
        quittingRootAbsorptionMass (quittingRootOfSimplex state.1.2) := by
  let root := quittingRootOfSimplex state.1.2
  have hquit : (root who true).toReal ≤ quittingRootAbsorptionMass root := by
    have hcontinue : quittingStationaryContinueMass root ≤
        (root who false).toReal := by
      classical
      rw [quittingStationaryContinueMass_eq_deletedContinueMass_mul_own root who]
      exact mul_le_of_le_one_left ENNReal.toReal_nonneg
        (quittingRootDeletedContinueMass_le_one root who)
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    unfold quittingRootAbsorptionMass
    linarith
  have hcap0 : 0 ≤ quittingPositiveSingletonDebtCap reward who :=
    le_max_left _ _
  unfold quittingDynamicDebtSeam
  calc
    (root who true).toReal * state.2 who ≤
        (root who true).toReal * quittingPositiveSingletonDebtCap reward who :=
      mul_le_mul_of_nonneg_left (hbox.2.2 who) ENNReal.toReal_nonneg
    _ ≤ quittingRootAbsorptionMass root *
          quittingPositiveSingletonDebtCap reward who :=
      mul_le_mul_of_nonneg_right hquit hcap0
    _ = quittingPositiveSingletonDebtCap reward who *
          quittingRootAbsorptionMass root := mul_comm _ _

/-- Exact finite weighted conservation of one debt coordinate. -/
theorem quittingDynamicDebtTail_conservation
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start fuel : ℕ) :
    (tail start).2 who =
      quittingJointSurvivalWeight
          (quittingDynamicDebtTailRoots tail) start fuel *
          (tail (start + fuel)).2 who +
        ∑ offset ∈ Finset.range fuel,
          quittingJointSurvivalWeight
              (quittingDynamicDebtTailRoots tail) start offset *
            quittingDynamicDebtSeam (tail (start + offset)) who := by
  induction fuel with
  | zero =>
      simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  | succ fuel ih =>
      have hstep := quittingDynamicDebt_eq_continueMass_mul_add_seam
        (reward := reward) (tail (start + fuel)) (tail (start + fuel + 1))
          (hedge (start + fuel)) (hbox (start + fuel + 1)).2.1 who
      rw [Finset.sum_range_succ, quittingJointSurvivalWeight_succ]
      rw [ih, hstep]
      simp only [quittingDynamicDebtTailRoots]
      have hindex : start + fuel + 1 = start + (fuel + 1) := by omega
      rw [hindex]
      ring

omit [DecidableEq ι] in
/-- Summable joint absorption makes every player's diagonal seam summable. -/
theorem summable_quittingDynamicDebtSeam_of_summable_absorption
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hsummable : Summable (fun time ↦
      quittingRootAbsorptionMass (quittingDynamicDebtTailRoots tail time)))
    (who : ι) :
    Summable (fun time ↦ quittingDynamicDebtSeam (tail time) who) :=
  Summable.of_nonneg_of_le
    (fun time ↦ quittingDynamicDebtSeam_nonneg
      (state := tail time) (hbox time) who)
    (fun time ↦ quittingDynamicDebtSeam_le_cap_mul_absorptionMass
      (state := tail time) (hbox time) who)
    (hsummable.mul_left (quittingPositiveSingletonDebtCap reward who))

/-- Exact dynamic debt is nondecreasing along chronological exact edges. -/
theorem monotone_quittingDynamicDebtTail_debt
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) :
    Monotone (fun time ↦ (tail time).2 who) := by
  apply monotone_nat_of_le_succ
  intro time
  rw [(hedge time).2 who]
  exact quittingDynamicDebtUpdate_le_successor
    reward (tail time) (tail (time + 1)) (hedge time).1
      (hbox (time + 1)).2.1 who

/-- On a segment where the selected player assigns positive probability to
Continue, deleted survival transports its exact dynamic debt with equality. -/
theorem quittingDynamicDebtTail_eq_opponentSurvivalWeight_mul
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start fuel : ℕ)
    (hcontinue : ∀ offset, offset < fuel →
      0 < (quittingDynamicDebtTailRoots tail (start + offset) who false).toReal) :
    (tail start).2 who =
      quittingOpponentSurvivalWeight
          (quittingDynamicDebtTailRoots tail) who start fuel *
        (tail (start + fuel)).2 who := by
  induction fuel with
  | zero =>
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hlocal :=
        quittingDynamicDebt_eq_opponentContinueMass_mul_of_continue_pos
          reward (tail (start + fuel)) (tail (start + fuel + 1))
          (hedge (start + fuel)) (hbox (start + fuel + 1)).2.1 who
          (hcontinue fuel (by omega))
      rw [quittingOpponentSurvivalWeight_succ, ih (fun offset hoffset ↦
        hcontinue offset (by omega)), hlocal]
      rw [← quittingFixedOpponentsContinueMass_dynamicDebtTailRoots_eq]
      have hindex : start + fuel + 1 = start + (fuel + 1) := by omega
      rw [hindex]
      ring

/-- The exact deleted-survival product on a positive-debt segment is the
ratio of its endpoint debts. -/
theorem quittingOpponentSurvivalWeight_eq_debt_div
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start fuel : ℕ)
    (hcontinue : ∀ offset, offset < fuel →
      0 < (quittingDynamicDebtTailRoots tail (start + offset) who false).toReal)
    (hdebt : 0 < (tail (start + fuel)).2 who) :
    quittingOpponentSurvivalWeight
        (quittingDynamicDebtTailRoots tail) who start fuel =
      (tail start).2 who / (tail (start + fuel)).2 who := by
  apply (eq_div_iff hdebt.ne').2
  exact (quittingDynamicDebtTail_eq_opponentSurvivalWeight_mul
    (reward := reward) tail hbox hedge who start fuel hcontinue).symm

/-- Exact debt transport turns the standard exponential survival estimate
into a logarithmic finite opponent-clock bound. -/
theorem sum_quittingOpponentClockCharge_le_log_debtRatio
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start fuel : ℕ)
    (hcontinue : ∀ offset, offset < fuel →
      0 < (quittingDynamicDebtTailRoots tail (start + offset) who false).toReal)
    (hstartDebt : 0 < (tail start).2 who) :
    (∑ offset ∈ Finset.range fuel,
        quittingOpponentClockCharge
          (quittingDynamicDebtTailRoots tail) who (start + offset)) ≤
      Real.log ((tail (start + fuel)).2 who / (tail start).2 who) := by
  have hendDebt : 0 < (tail (start + fuel)).2 who :=
    hstartDebt.trans_le
      (monotone_quittingDynamicDebtTail_debt tail hbox hedge who
        (Nat.le_add_right start fuel))
  have hsurvivalEq := quittingOpponentSurvivalWeight_eq_debt_div
    (reward := reward) tail hbox hedge who start fuel hcontinue hendDebt
  have hsurvivalPos : 0 < quittingOpponentSurvivalWeight
      (quittingDynamicDebtTailRoots tail) who start fuel := by
    rw [hsurvivalEq]
    exact div_pos hstartDebt hendDebt
  have hexp := quittingOpponentSurvivalWeight_le_exp_neg_sum_charge
    (quittingDynamicDebtTailRoots tail) who start fuel
  have hlog := Real.log_le_log hsurvivalPos hexp
  rw [Real.log_exp] at hlog
  rw [hsurvivalEq, Real.log_div hstartDebt.ne' hendDebt.ne'] at hlog
  rw [Real.log_div hendDebt.ne' hstartDebt.ne']
  linarith

end GameTheory
