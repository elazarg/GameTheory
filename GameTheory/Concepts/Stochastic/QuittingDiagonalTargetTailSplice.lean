/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingDiagonalTargetTail
import GameTheory.Concepts.Stochastic.QuittingJointComplementarity

/-!
# Exact diagonal target-tail splice accounting

This module proves the sign-sensitive finite-prefix reinsertion estimate.
A deviator sees a terminal tail through opponent-only survival; prescribed
play sees the boundary mismatch through joint survival.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Exact sign-sensitive splice accounting -/

/-- A finite terminal-hazard recursion only reads roots before the boundary,
so splicing a tail at `cutoff` does not alter any shorter prefix value. -/
theorem quittingFiniteTerminalHazardValue_prefixThenTail_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (headRoots tail : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (terminalValue : ℝ) (cutoff : ℕ) :
    ∀ start fuel, start + fuel ≤ cutoff →
      quittingFiniteTerminalHazardValue reward
          (quittingPrefixThenTailRoots headRoots tail cutoff) who hazard
          terminalValue start fuel =
        quittingFiniteTerminalHazardValue reward headRoots who hazard
          terminalValue start fuel := by
  intro start fuel hcutoff
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      have hstart : start < cutoff := by omega
      have htailCutoff : start + 1 + fuel ≤ cutoff := by omega
      have hroot :
          quittingPrefixThenTailRoots headRoots tail cutoff start =
            headRoots start :=
        quittingPrefixThenTailRoots_of_lt headRoots tail cutoff start hstart
      have hquit :
          quittingFixedOpponentsQuitValue reward
              (quittingPrefixThenTailRoots headRoots tail cutoff) who start =
            quittingFixedOpponentsQuitValue reward headRoots who start := by
        unfold quittingFixedOpponentsQuitValue
        rw [hroot]
      have hcontinue :
          quittingFixedOpponentsContinueReward reward
              (quittingPrefixThenTailRoots headRoots tail cutoff) who start =
            quittingFixedOpponentsContinueReward reward headRoots who start := by
        unfold quittingFixedOpponentsContinueReward
        rw [hroot]
      have hmass :
          quittingFixedOpponentsContinueMass
              (quittingPrefixThenTailRoots headRoots tail cutoff) who start =
            quittingFixedOpponentsContinueMass headRoots who start := by
        unfold quittingFixedOpponentsContinueMass
        rw [hroot]
      rw [quittingFiniteTerminalHazardValue,
        quittingFiniteTerminalHazardValue, hquit, hcontinue, hmass,
        ih (start + 1) htailCutoff]

/-- The prescribed finite prefix likewise uses the original root marginal as
its hazard at every date strictly before the splice. -/
theorem quittingFiniteTerminalHazardValue_self_prefixThenTail_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (headRoots tail : ℕ → ι → PMF Bool) (who : ι)
    (terminalValue : ℝ) (cutoff : ℕ) :
    ∀ start fuel, start + fuel ≤ cutoff →
      quittingFiniteTerminalHazardValue reward
          (quittingPrefixThenTailRoots headRoots tail cutoff) who
          (fun time =>
            quittingPrefixThenTailRoots headRoots tail cutoff time who)
          terminalValue start fuel =
        quittingFiniteTerminalHazardValue reward headRoots who
          (fun time => headRoots time who) terminalValue start fuel := by
  intro start fuel hcutoff
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      have hstart : start < cutoff := by omega
      have htailCutoff : start + 1 + fuel ≤ cutoff := by omega
      have hroot :
          quittingPrefixThenTailRoots headRoots tail cutoff start =
            headRoots start :=
        quittingPrefixThenTailRoots_of_lt headRoots tail cutoff start hstart
      have hhazard :
          quittingPrefixThenTailRoots headRoots tail cutoff start who =
            headRoots start who := by rw [hroot]
      have hquit :
          quittingFixedOpponentsQuitValue reward
              (quittingPrefixThenTailRoots headRoots tail cutoff) who start =
            quittingFixedOpponentsQuitValue reward headRoots who start := by
        unfold quittingFixedOpponentsQuitValue
        rw [hroot]
      have hcontinue :
          quittingFixedOpponentsContinueReward reward
              (quittingPrefixThenTailRoots headRoots tail cutoff) who start =
            quittingFixedOpponentsContinueReward reward headRoots who start := by
        unfold quittingFixedOpponentsContinueReward
        rw [hroot]
      have hmass :
          quittingFixedOpponentsContinueMass
              (quittingPrefixThenTailRoots headRoots tail cutoff) who start =
            quittingFixedOpponentsContinueMass headRoots who start := by
        unfold quittingFixedOpponentsContinueMass
        rw [hroot]
      rw [quittingFiniteTerminalHazardValue,
        quittingFiniteTerminalHazardValue, hhazard, hquit, hcontinue, hmass,
        ih (start + 1) htailCutoff]

/-- Prescribed full-profile survival through a finite prefix is exactly the
joint survival product of that prefix. -/
theorem quittingFiniteFullSurvivalWeight_self_eq_jointSurvivalWeight
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingFiniteFullSurvivalWeight roots who
        (fun time => roots time who) start fuel =
      quittingJointSurvivalWeight roots start fuel := by
  rw [quittingFiniteFullSurvivalWeight_self_eq_product,
    quittingJointSurvivalWeight_eq_prod]

/-- **Exact sign-sensitive splice inequality.**  A deviation sees the selected
suffix through opponent-only survival `O`; the prescribed path sees its
boundary mismatch through joint survival `J`.  No common punishment tail and
no absolute-value relaxation are used here. -/
theorem quittingPrefixThenTailHazardGap_le_survival_debt_sub_joint_mismatch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (headRoots tail : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (hazard : ℕ → PMF Bool) (cutoff : ℕ)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (headRoots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (headRoots time)) :
    let fullRoots := quittingPrefixThenTailRoots headRoots tail cutoff
    let tailDeviation :=
      quittingRootSequenceHazardTerminalValue reward tail who
        (fun time => hazard (cutoff + time)) 0
    let tailPayoff := quittingRootSequenceTerminalValue reward tail who 0
    let debt := max (tailDeviation - value cutoff who) 0
    quittingRootSequenceHazardTerminalValue reward fullRoots who hazard 0 -
        quittingRootSequenceTerminalValue reward fullRoots who 0 ≤
      quittingOpponentSurvivalWeight headRoots who 0 cutoff * debt -
        quittingJointSurvivalWeight headRoots 0 cutoff *
          (tailPayoff - value cutoff who) := by
  dsimp only
  let fullRoots := quittingPrefixThenTailRoots headRoots tail cutoff
  let tailDeviation :=
    quittingRootSequenceHazardTerminalValue reward tail who
      (fun time => hazard (cutoff + time)) 0
  let tailPayoff := quittingRootSequenceTerminalValue reward tail who 0
  let debt := max (tailDeviation - value cutoff who) 0
  have hdebt0 : 0 ≤ debt := by
    exact le_max_right _ _
  have htailDeviationLe : tailDeviation ≤ value cutoff who + debt := by
    dsimp only [debt]
    linarith [le_max_left (tailDeviation - value cutoff who) 0]
  have hdeviationDecomposition :
      quittingRootSequenceHazardTerminalValue reward fullRoots who hazard 0 =
        quittingFiniteTerminalHazardValue reward headRoots who hazard
          tailDeviation 0 cutoff := by
    calc
      quittingRootSequenceHazardTerminalValue reward fullRoots who hazard 0 =
          quittingFiniteTerminalHazardValue reward fullRoots who hazard
            (quittingRootSequenceHazardTerminalValue reward fullRoots who hazard
              cutoff) 0 cutoff :=
        quittingRootSequenceHazardTerminalValue_eq_finiteTerminalHazardValue
          reward fullRoots who hazard 0 cutoff
      _ = quittingFiniteTerminalHazardValue reward fullRoots who hazard
            tailDeviation 0 cutoff := by
        rw [show quittingRootSequenceHazardTerminalValue reward fullRoots who
            hazard cutoff = tailDeviation by
          dsimp only [fullRoots, tailDeviation]
          exact quittingRootSequenceHazardTerminalValue_prefixThenTail_cutoff
            reward headRoots tail who hazard cutoff]
      _ = quittingFiniteTerminalHazardValue reward headRoots who hazard
            tailDeviation 0 cutoff :=
        quittingFiniteTerminalHazardValue_prefixThenTail_of_le
          reward headRoots tail who hazard tailDeviation cutoff 0 cutoff le_rfl
  have hdeviationUpper :
      quittingRootSequenceHazardTerminalValue reward fullRoots who hazard 0 ≤
        value 0 who +
          quittingOpponentSurvivalWeight headRoots who 0 cutoff * debt := by
    rw [hdeviationDecomposition]
    calc
      quittingFiniteTerminalHazardValue reward headRoots who hazard
            tailDeviation 0 cutoff ≤
          quittingFiniteTerminalHazardValue reward headRoots who hazard
            (value cutoff who + debt) 0 cutoff :=
        quittingFiniteTerminalHazardValue_mono_terminal reward headRoots who
          hazard htailDeviationLe 0 cutoff
      _ ≤ quittingFiniteTerminalBestResponseValue reward headRoots who
            (value cutoff who + debt) 0 cutoff :=
        quittingFiniteTerminalHazardValue_le_bestResponse reward headRoots who
          hazard (value cutoff who + debt) 0 cutoff
      _ ≤ value 0 who +
            quittingOpponentSurvivalWeight headRoots who 0 cutoff * debt :=
        quittingFiniteTerminalBestResponseValue_le_declared_add_survival
          reward headRoots value who cutoff hdebt0 hpolicy hnash 0 cutoff le_rfl
  have hprescribedDecomposition :
      quittingRootSequenceTerminalValue reward fullRoots who 0 =
        value 0 who +
          quittingJointSurvivalWeight headRoots 0 cutoff *
            (tailPayoff - value cutoff who) := by
    calc
      quittingRootSequenceTerminalValue reward fullRoots who 0 =
          quittingFiniteTerminalHazardValue reward fullRoots who
            (fun time => fullRoots time who)
            (quittingRootSequenceTerminalValue reward fullRoots who cutoff)
            0 cutoff :=
        quittingRootSequenceTerminalValue_eq_finiteTerminalHazardValue_self
          reward fullRoots who 0 cutoff
      _ = quittingFiniteTerminalHazardValue reward fullRoots who
            (fun time => fullRoots time who) tailPayoff 0 cutoff := by
        rw [show quittingRootSequenceTerminalValue reward fullRoots who cutoff =
            tailPayoff by
          dsimp only [fullRoots, tailPayoff]
          exact quittingRootSequenceTerminalValue_prefixThenTail_cutoff
            reward headRoots tail who cutoff]
      _ = quittingFiniteTerminalHazardValue reward headRoots who
            (fun time => headRoots time who) tailPayoff 0 cutoff :=
        quittingFiniteTerminalHazardValue_self_prefixThenTail_of_le
          reward headRoots tail who tailPayoff cutoff 0 cutoff le_rfl
      _ = quittingFiniteTerminalHazardValue reward headRoots who
            (fun time => headRoots time who)
            (value cutoff who + (tailPayoff - value cutoff who)) 0 cutoff := by
        ring_nf
      _ = quittingFiniteTerminalHazardValue reward headRoots who
              (fun time => headRoots time who) (value cutoff who) 0 cutoff +
            quittingFiniteFullSurvivalWeight headRoots who
              (fun time => headRoots time who) 0 cutoff *
                (tailPayoff - value cutoff who) :=
        quittingFiniteTerminalHazardValue_add reward headRoots who
          (fun time => headRoots time who) (value cutoff who)
          (tailPayoff - value cutoff who) 0 cutoff
      _ = value 0 who +
            quittingFiniteFullSurvivalWeight headRoots who
              (fun time => headRoots time who) 0 cutoff *
                (tailPayoff - value cutoff who) := by
        rw [quittingFiniteTerminalHazardValue_self_eq_declared
          reward headRoots value who cutoff hpolicy 0 cutoff le_rfl]
      _ = value 0 who +
            quittingJointSurvivalWeight headRoots 0 cutoff *
              (tailPayoff - value cutoff who) := by
        rw [quittingFiniteFullSurvivalWeight_self_eq_jointSurvivalWeight]
  rw [hprescribedDecomposition]
  linarith

/-- If the selected tail is closed for the target and its target coordinate is
the declared endpoint, the target's splice gain is nonpositive. -/
theorem quittingPrefixThenTargetTailHazardGap_le_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (headRoots tail : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (target : ι) (hazard : ℕ → PMF Bool) (cutoff : ℕ)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (headRoots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (headRoots time))
    (hclosed : IsQuittingTargetClosedAt reward tail target 0)
    (hendpoint : value cutoff target =
      quittingRootSequenceTerminalValue reward tail target 0) :
    quittingRootSequenceHazardTerminalValue reward
          (quittingPrefixThenTailRoots headRoots tail cutoff) target hazard 0 -
        quittingRootSequenceTerminalValue reward
          (quittingPrefixThenTailRoots headRoots tail cutoff) target 0 ≤ 0 := by
  have hmain :=
    quittingPrefixThenTailHazardGap_le_survival_debt_sub_joint_mismatch
      reward headRoots tail value target hazard cutoff hpolicy hnash
  have htail := hclosed (fun time => hazard (cutoff + time))
  have hdebt :
      max
          (quittingRootSequenceHazardTerminalValue reward tail target
              (fun time => hazard (cutoff + time)) 0 - value cutoff target)
          0 = 0 := by
    rw [hendpoint]
    exact max_eq_right (sub_nonpos.mpr htail)
  have hmismatch :
      quittingRootSequenceTerminalValue reward tail target 0 -
          value cutoff target = 0 := by
    rw [hendpoint]
  simpa only [hdebt, hmismatch, mul_zero, sub_zero] using hmain

/-- For any non-target coordinate, bounded rewards and a bounded declared
endpoint give the coarse but uniform `4*M*O` splice bound. -/
theorem quittingPrefixThenTailHazardGap_le_four_mul_bound_mul_survival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (headRoots tail : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (hazard : ℕ → PMF Bool) (cutoff : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hvalue : |value cutoff who| ≤ M)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (headRoots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (headRoots time)) :
    quittingRootSequenceHazardTerminalValue reward
          (quittingPrefixThenTailRoots headRoots tail cutoff) who hazard 0 -
        quittingRootSequenceTerminalValue reward
          (quittingPrefixThenTailRoots headRoots tail cutoff) who 0 ≤
      4 * M * quittingOpponentSurvivalWeight headRoots who 0 cutoff := by
  let tailDeviation :=
    quittingRootSequenceHazardTerminalValue reward tail who
      (fun time => hazard (cutoff + time)) 0
  let tailPayoff := quittingRootSequenceTerminalValue reward tail who 0
  let debt := max (tailDeviation - value cutoff who) 0
  let O := quittingOpponentSurvivalWeight headRoots who 0 cutoff
  let J := quittingJointSurvivalWeight headRoots 0 cutoff
  have hmain :=
    quittingPrefixThenTailHazardGap_le_survival_debt_sub_joint_mismatch
      reward headRoots tail value who hazard cutoff hpolicy hnash
  have htailDeviation : |tailDeviation| ≤ M := by
    dsimp only [tailDeviation, quittingRootSequenceHazardTerminalValue]
    exact abs_quittingRootSequenceTerminalValue_le reward
      (quittingRootSequenceUpdate tail who
        (fun time => hazard (cutoff + time))) who 0 hM hreward
  have htailPayoff : |tailPayoff| ≤ M := by
    exact abs_quittingRootSequenceTerminalValue_le reward tail who 0 hM hreward
  have hdebt : debt ≤ 2 * M := by
    rw [abs_le] at htailDeviation hvalue
    dsimp only [debt]
    apply max_le
    · linarith
    · linarith
  have hmismatchLower : -(2 * M) ≤ tailPayoff - value cutoff who := by
    rw [abs_le] at htailPayoff hvalue
    linarith
  have hO0 : 0 ≤ O :=
    quittingOpponentSurvivalWeight_nonneg headRoots who 0 cutoff
  have hJ0 : 0 ≤ J :=
    quittingJointSurvivalWeight_nonneg headRoots 0 cutoff
  have hJO : J ≤ O :=
    quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
      headRoots who 0 cutoff
  have hdebtScaled : O * debt ≤ O * (2 * M) :=
    mul_le_mul_of_nonneg_left hdebt hO0
  have hmismatchScaled :
      -(J * (tailPayoff - value cutoff who)) ≤ J * (2 * M) := by
    have hmul := mul_le_mul_of_nonneg_left hmismatchLower hJ0
    nlinarith
  have hjointScaled : J * (2 * M) ≤ O * (2 * M) :=
    mul_le_mul_of_nonneg_right hJO (by positivity)
  dsimp only [tailDeviation, tailPayoff, debt, O, J] at hmain ⊢
  nlinarith [hmain, hdebtScaled, hmismatchScaled, hjointScaled]

end GameTheory
