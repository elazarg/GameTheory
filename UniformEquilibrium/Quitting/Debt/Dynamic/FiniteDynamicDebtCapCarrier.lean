/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtCompiler
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtCapBridge
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorAdmissibleChargedRelation

/-!
# Finite exact-debt caps lie in the punishment-floor carrier

For a finite exact Nash--Bellman chain with zero terminal value, prescribed
value plus exact dynamic debt is the literal unilateral stopping cap against
the chain followed by all-Continue.  This module records the two intrinsic
carrier consequences of that semantics:

* every behavioral punishment value is below the augmented cap; and
* every augmented cap remains in the canonical reward box.

The statements hold at every suffix date.  The shift lemma below makes that
point explicit rather than silently treating date zero as privileged.  No
claim that augmented caps themselves form exact Nash--Bellman edges is made;
their exact diagonal edge defect is proved in `DynamicDebtCapBridge`.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Time translation -/

/-- Exact dynamic debt is covariant under translation of the root and value
sequences. -/
theorem quittingFiniteDynamicDebt_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (terminalDebt : ℝ) (start fuel : ℕ) :
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start fuel =
      quittingFiniteDynamicDebt reward (fun time => roots (start + time)) who
        (fun time => prescribed (start + time)) terminalDebt 0 fuel := by
  induction fuel generalizing start roots prescribed with
  | zero => rfl
  | succ fuel ih =>
      rw [quittingFiniteDynamicDebt_succ,
        quittingFiniteDynamicDebt_succ]
      simp only [Nat.zero_add]
      rw [ih (roots := roots) (prescribed := prescribed) (start + 1)]
      rw [ih (roots := fun time => roots (start + time))
        (prescribed := fun time => prescribed (start + time)) 1]
      simp [quittingFixedOpponentsQuitValue,
        quittingFixedOpponentsContinueReward,
        quittingFixedOpponentsContinueMass, Nat.add_assoc]

/-! ## Uniform bounds for finite stopping caps -/

/-- A finite mixed-hazard value stays in the reward box whenever its terminal
live value does. -/
theorem abs_quittingFiniteTerminalHazardValue_le_rewardBound_of_terminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (terminalValue : ℝ)
    (hterminal : |terminalValue| ≤ quittingRewardBound reward) :
    ∀ start fuel,
      |quittingFiniteTerminalHazardValue reward roots who hazard terminalValue
          start fuel| ≤ quittingRewardBound reward := by
  intro start fuel
  induction fuel generalizing start with
  | zero => exact hterminal
  | succ fuel ih =>
      rw [quittingFiniteTerminalHazardValue]
      let tail : Payoff ι := fun _ =>
        quittingFiniteTerminalHazardValue reward roots who hazard
          terminalValue (start + 1) fuel
      have hquit :
          |quittingFixedOpponentsQuitValue reward roots who start| ≤
            quittingRewardBound reward := by
        rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
          reward roots who tail start]
        exact abs_quittingRootExpectedPayoff_le_bound reward tail
          (Function.update (roots start) who (PMF.pure true)) who
          (abs_reward_le_quittingRewardBound reward) (fun _ => ih (start + 1))
      have hcontinue :
          |quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingFiniteTerminalHazardValue reward roots who hazard
                  terminalValue (start + 1) fuel| ≤
            quittingRewardBound reward := by
        rw [← quittingRootContinuePayoff_eq_fixedOpponents
          reward roots who tail start]
        exact abs_quittingRootExpectedPayoff_le_bound reward tail
          (Function.update (roots start) who (PMF.pure false)) who
          (abs_reward_le_quittingRewardBound reward) (fun _ => ih (start + 1))
      have hsum :
          (hazard start true).toReal + (hazard start false).toReal = 1 := by
        simpa [Fintype.sum_bool] using pmf_toReal_sum_one (hazard start)
      calc
        |(hazard start true).toReal *
              quittingFixedOpponentsQuitValue reward roots who start +
            (hazard start false).toReal *
              (quittingFixedOpponentsContinueReward reward roots who start +
                quittingFixedOpponentsContinueMass roots who start *
                  quittingFiniteTerminalHazardValue reward roots who hazard
                    terminalValue (start + 1) fuel)| ≤
            |(hazard start true).toReal *
                quittingFixedOpponentsQuitValue reward roots who start| +
              |(hazard start false).toReal *
                (quittingFixedOpponentsContinueReward reward roots who start +
                  quittingFixedOpponentsContinueMass roots who start *
                    quittingFiniteTerminalHazardValue reward roots who hazard
                      terminalValue (start + 1) fuel)| := abs_add_le _ _
        _ =
            (hazard start true).toReal *
                |quittingFixedOpponentsQuitValue reward roots who start| +
              (hazard start false).toReal *
                |quittingFixedOpponentsContinueReward reward roots who start +
                  quittingFixedOpponentsContinueMass roots who start *
                    quittingFiniteTerminalHazardValue reward roots who hazard
                      terminalValue (start + 1) fuel| := by
          rw [abs_mul, abs_mul,
            abs_of_nonneg ENNReal.toReal_nonneg,
            abs_of_nonneg ENNReal.toReal_nonneg]
        _ ≤ (hazard start true).toReal * quittingRewardBound reward +
              (hazard start false).toReal * quittingRewardBound reward :=
          add_le_add
            (mul_le_mul_of_nonneg_left hquit ENNReal.toReal_nonneg)
            (mul_le_mul_of_nonneg_left hcontinue ENNReal.toReal_nonneg)
        _ = quittingRewardBound reward := by
          rw [← add_mul, hsum, one_mul]

/-- The finite Bellman stopping maximum stays in the reward box whenever its
terminal live value does. -/
theorem abs_quittingFiniteTerminalBestResponseValue_le_rewardBound_of_terminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (terminalValue : ℝ)
    (hterminal : |terminalValue| ≤ quittingRewardBound reward)
    (start fuel : ℕ) :
    |quittingFiniteTerminalBestResponseValue reward roots who terminalValue
        start fuel| ≤ quittingRewardBound reward := by
  obtain ⟨hazard, hhazard⟩ :=
    exists_quittingFiniteTerminalHazardValue_eq_bestResponse
      reward roots who terminalValue start fuel
  rw [← hhazard]
  exact abs_quittingFiniteTerminalHazardValue_le_rewardBound_of_terminal
    reward roots who hazard terminalValue hterminal start fuel

omit [DecidableEq ι] in
/-- The singleton-or-Never boundary used by exact dynamic debt lies in the
canonical reward interval. -/
theorem abs_quittingPositiveSingletonDebtCap_le_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    |quittingPositiveSingletonDebtCap reward who| ≤
      quittingRewardBound reward := by
  rw [abs_of_nonneg (le_max_left _ _)]
  unfold quittingPositiveSingletonDebtCap
  apply max_le (quittingRewardBound_nonneg reward)
  exact (le_abs_self _).trans
    (abs_reward_le_quittingRewardBound reward
      (quittingSingletonTerminal who) who)

/-! ## Behavioral punishment-floor dominance -/

/-- At date zero, the augmented exact-D value dominates the complete
behavioral punishment value.  The proof uses the actual all-Continue extension
of the displayed finite root word; it does not replace the behavioral minmax
by a local stationary inequality. -/
theorem quittingPunishmentValue_le_finiteDynamicDebtCap_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (cutoff : ℕ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value cutoff = 0) :
    quittingPunishmentValue reward who ≤
      value 0 who +
        quittingFiniteDynamicDebt reward roots who
          (fun time => value time who)
          (quittingPositiveSingletonDebtCap reward who) 0 cutoff := by
  let profile := quittingInfinitePathProfile reward roots
  have hfloor := quittingPunishmentValue_le reward who profile
  apply hfloor.trans
  apply quittingBestReplyValue_le
  intro deviation
  have hdeviation :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward profile who deviation
  rw [quittingProfileLiveRoot_infinitePathProfile] at hdeviation
  rw [hdeviation]
  have hgap :=
    quittingRootSequenceHazardTerminalGap_le_finiteDynamicDebt
      reward roots value who (quittingBehaviorLiveHazard reward deviation)
        cutoff htail hterminal
  simpa only [quittingPositiveSingletonDebtCap, add_comm] using
    (sub_le_iff_le_add.mp hgap)

/-- Every suffix augmented cap of a zero-boundary finite chain dominates the
behavioral punishment value. -/
theorem quittingPunishmentValue_le_finiteDynamicDebtCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (start fuel : ℕ)
    (htail : ∀ time, start + fuel ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value (start + fuel) = 0) :
    quittingPunishmentValue reward who ≤
      value start who +
        quittingFiniteDynamicDebt reward roots who
          (fun time => value time who)
          (quittingPositiveSingletonDebtCap reward who) start fuel := by
  let shiftedRoots : ℕ → ι → PMF Bool := fun time => roots (start + time)
  let shiftedValue : ℕ → Payoff ι := fun time => value (start + time)
  have hshiftTail : ∀ time, fuel ≤ time →
      shiftedRoots time = (quittingAllContinueRoot : ι → PMF Bool) := by
    intro time htime
    exact htail (start + time) (Nat.add_le_add_left htime start)
  have hshiftTerminal : shiftedValue fuel = 0 := by
    simpa [shiftedValue] using hterminal
  have hfloor := quittingPunishmentValue_le_finiteDynamicDebtCap_zero
    reward shiftedRoots shiftedValue who fuel hshiftTail hshiftTerminal
  dsimp only [shiftedRoots, shiftedValue] at hfloor
  rw [← quittingFiniteDynamicDebt_shift reward roots who
    (fun time => value time who)
    (quittingPositiveSingletonDebtCap reward who) start fuel] at hfloor
  simpa using hfloor

/-- Every suffix augmented cap of a zero-boundary finite chain lies in the
canonical reward box. -/
theorem abs_finiteDynamicDebtCap_le_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (start fuel : ℕ)
    (hterminal : value (start + fuel) = 0) :
    |value start who +
        quittingFiniteDynamicDebt reward roots who
          (fun time => value time who)
          (quittingPositiveSingletonDebtCap reward who) start fuel| ≤
      quittingRewardBound reward := by
  change |(fun time => value time who) start +
        quittingFiniteDynamicDebt reward roots who
          (fun time => value time who)
          (quittingPositiveSingletonDebtCap reward who) start fuel| ≤
      quittingRewardBound reward
  rw [prescribed_add_quittingFiniteDynamicDebt_eq_bestResponse
    reward roots who (fun time => value time who)
      (quittingPositiveSingletonDebtCap reward who) start fuel]
  have hterminalWho : value (start + fuel) who = 0 := by
    rw [hterminal]
    rfl
  rw [hterminalWho, zero_add]
  exact abs_quittingFiniteTerminalBestResponseValue_le_rewardBound_of_terminal
    reward roots who (quittingPositiveSingletonDebtCap reward who)
      (abs_quittingPositiveSingletonDebtCap_le_rewardBound reward who)
      start fuel

/-- The augmented exact-D payoff vector belongs to the same canonical compact
carrier used by punishment-floor predecessor prefixes. -/
theorem finiteDynamicDebtCap_mem_punishmentFloorForwardCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (start fuel : ℕ) (hterminal : value (start + fuel) = 0) :
    (fun who => value start who +
      quittingFiniteDynamicDebt reward roots who
        (fun time => value time who)
        (quittingPositiveSingletonDebtCap reward who) start fuel) ∈
      quittingPunishmentFloorForwardCarrier reward := by
  constructor
  · intro who
    exact (abs_le.mp (abs_finiteDynamicDebtCap_le_rewardBound
      reward roots value who start fuel hterminal)).1
  · intro who
    exact (abs_le.mp (abs_finiteDynamicDebtCap_le_rewardBound
      reward roots value who start fuel hterminal)).2

/-- The complete carrier statement: the augmented cap is both reward-boxed
and coordinatewise above the behavioral punishment floor. -/
theorem finiteDynamicDebtCap_mem_and_punishmentFloor_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (start fuel : ℕ)
    (htail : ∀ time, start + fuel ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value (start + fuel) = 0) :
    (fun who => value start who +
      quittingFiniteDynamicDebt reward roots who
        (fun time => value time who)
        (quittingPositiveSingletonDebtCap reward who) start fuel) ∈
        quittingPunishmentFloorForwardCarrier reward ∧
      ∀ who, quittingPunishmentValue reward who ≤
        value start who +
          quittingFiniteDynamicDebt reward roots who
            (fun time => value time who)
            (quittingPositiveSingletonDebtCap reward who) start fuel := by
  exact ⟨finiteDynamicDebtCap_mem_punishmentFloorForwardCarrier
      reward roots value start fuel hterminal,
    fun who => quittingPunishmentValue_le_finiteDynamicDebtCap
      reward roots value who start fuel htail hterminal⟩

/-- Canonical embedding of an augmented finite exact-D cap into the full
boxed floor-admissible state space.  The simplex coordinate is a harmless
all-Continue marker; only the payoff coordinate is asserted to carry the
finite stopping semantics. -/
def finiteDynamicDebtCapAdmissibleState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (start fuel : ℕ)
    (htail : ∀ time, start + fuel ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value (start + fuel) = 0) :
    QuittingPunishmentFloorAdmissibleState reward := by
  let cap : Payoff ι := fun who => value start who +
    quittingFiniteDynamicDebt reward roots who
      (fun time => value time who)
      (quittingPositiveSingletonDebtCap reward who) start fuel
  have hcarrier := finiteDynamicDebtCap_mem_and_punishmentFloor_le
    reward roots value start fuel htail hterminal
  exact ⟨⟨(cap, quittingAllContinueSimplexRoot), hcarrier.1⟩, hcarrier.2⟩

/-! ## Canonical finite-chain annotations -/

/-- The augmented cap stored by the canonical exact-D annotation of any
finite zero-boundary chain lies in the reward box and dominates the complete
behavioral punishment floor.  This is the finite statement whose closed
limit is consumed by the optimized projective tail. -/
theorem quittingFiniteNashBellmanPathDynamicDebtCap_mem_and_floor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) (htime : time ≤ cutoff) :
    quittingDynamicDebtCap
        (quittingFiniteNashBellmanPathDynamicDebtPoint
          reward cutoff path time) ∈
        quittingPunishmentFloorForwardCarrier reward ∧
      ∀ who, quittingPunishmentValue reward who ≤
        quittingDynamicDebtCap
          (quittingFiniteNashBellmanPathDynamicDebtPoint
            reward cutoff path time) who := by
  let roots := quittingFiniteNashBellmanPathRoots cutoff path
  let value := quittingFiniteNashBellmanPathValue cutoff path
  have htail : ∀ liveTime, time + (cutoff - time) ≤ liveTime →
      roots liveTime = (quittingAllContinueRoot : ι → PMF Bool) := by
    intro liveTime hlive
    apply quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
    omega
  have hterminal : value (time + (cutoff - time)) = 0 := by
    have hindex : time + (cutoff - time) = cutoff := Nat.add_sub_of_le htime
    rw [hindex]
    exact quittingFiniteNashBellmanPathValue_eq_zero_of_cutoff_le
      reward cutoff path hpath cutoff le_rfl
  have hcarrier := finiteDynamicDebtCap_mem_and_punishmentFloor_le
    reward roots value time (cutoff - time) htail hterminal
  have hvalueAt : value time =
      (path ⟨time, Nat.lt_succ_of_le htime⟩).1 := by
    simp [value, quittingFiniteNashBellmanPathValue,
      Nat.lt_succ_of_le htime]
  rw [hvalueAt] at hcarrier
  have hcapApply : ∀ who,
      quittingDynamicDebtCap
          (quittingFiniteNashBellmanPathDynamicDebtPoint
            reward cutoff path time) who =
        (path ⟨time, Nat.lt_succ_of_le htime⟩).1 who +
          quittingFiniteDynamicDebt reward roots who
            (fun liveTime ↦ value liveTime who)
            (quittingPositiveSingletonDebtCap reward who)
            time (cutoff - time) := by
    intro who
    simp [quittingDynamicDebtCap,
      quittingFiniteNashBellmanPathDynamicDebtPoint, htime,
      quittingFiniteNashBellmanPathDynamicDebt, roots, value]
  constructor
  · constructor
    · intro who
      rw [hcapApply who]
      exact hcarrier.1.1 who
    · intro who
      rw [hcapApply who]
      exact hcarrier.1.2 who
  · intro who
    rw [hcapApply who]
    exact hcarrier.2 who

end GameTheory
