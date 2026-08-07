/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingPunishmentFreeReduction
import GameTheory.Concepts.Stochastic.QuittingZeroSoloDisjunct
import GameTheory.Concepts.Stochastic.QuittingOpponentActionMass

/-!
# A solved zero-sum game outside the truncated ledger-cap interface

The truncated ledger-cap package requires every player's deleted opponent
survival to be small at one common finite cutoff.  This is not merely stronger
than uniform-equilibrium existence: it already fails in a two-player game
whose exact uniform equilibrium is all-Continue.

At a singleton terminal, the quitter receives `-1` and the continuing player
receives `1`; simultaneous quitting pays `0`.  Thus all-Continue is an exact
uniform equilibrium.  But if a finite plan makes both deleted survival
probabilities small, either player can continue throughout the plan and earn
the probability that the opponent quits.  The two prescribed payoffs sum to
zero, so the two deviation inequalities force the common reach bound to be at
least `1/2`.  The package's own `reach * (5 * rewardBound)` error term at
accuracy `1/2` forces reach to be at most `1/10`.

This refutes `quittingGame_hasQuittingTruncatedLedgerCapPackage`: the missing
producer cannot target that interface without a persistent-live disjunct or a
strictly weaker, active-set-relative survival requirement.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace QuittingTruncatedLedgerCapCounterexample

/-- Two-player zero-sum anti-coordination reward.  A player receives `1` when
only the opponent quits, `-1` when they quit alone, and `0` when both quit. -/
def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun S who =>
    if who ∉ S.1 then 1
    else if S.1 = {who} then -1
    else 0

@[simp] theorem reward_singleton_self (who : Bool) :
    reward (quittingSingletonTerminal who) who = -1 := by
  simp [reward, quittingSingletonTerminal]

/-- Every terminal reward vector has zero total payoff. -/
theorem reward_false_add_true (S : {S : Finset Bool // S.Nonempty}) :
    reward S false + reward S true = 0 := by
  by_cases hfalse : false ∈ S.1
  · by_cases htrue : true ∈ S.1
    · have hneFalse : S.1 ≠ {false} := by
        intro h
        have : true ∈ ({false} : Finset Bool) := by simp [h] at htrue
        simp at this
      have hneTrue : S.1 ≠ {true} := by
        intro h
        have : false ∈ ({true} : Finset Bool) := by simp [h] at hfalse
        simp at this
      simp [reward, hfalse, htrue, hneFalse, hneTrue]
    · have hS : S.1 = {false} := by
        ext player
        cases player <;> simp [hfalse, htrue]
      simp [reward, hS]
  · have htrue : true ∈ S.1 := by
      obtain ⟨player, hplayer⟩ := S.2
      cases player with
      | false => exact (hfalse hplayer).elim
      | true => exact hplayer
    have hS : S.1 = {true} := by
      ext player
      cases player <;> simp [hfalse, htrue]
    simp [reward, hS]

/-- The game is zero-solo, hence all-Continue gives the exact uniform payoff
zero. -/
theorem isQuittingZeroSolo_reward : IsQuittingZeroSolo reward := by
  intro who
  simp

/-- The counterexample is a solved game, not a nonexistence example. -/
theorem isUniformEquilibriumPayoff_zero :
    (quittingGame reward).IsUniformEquilibriumPayoff none (0 : Payoff Bool) :=
  quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo reward
    isQuittingZeroSolo_reward

/-- Terminal payoffs remain zero-sum under every behavior profile. -/
theorem terminalPayoff_false_add_true
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile false +
        quittingTerminalPayoff reward profile true = 0 := by
  rw [quittingTerminalPayoff, quittingTerminalPayoff,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro S hS
  rw [← mul_add, reward_false_add_true, mul_zero]

/-- In particular, every supplied root sequence has prescribed values summing
to zero. -/
theorem rootSequenceTerminalValue_false_add_true
    (roots : ℕ → Bool → PMF Bool) (start : ℕ) :
    quittingRootSequenceTerminalValue reward roots false start +
        quittingRootSequenceTerminalValue reward roots true start = 0 := by
  exact terminalPayoff_false_add_true
    (quittingRootSequenceProfile reward roots start)

/-- Against a pure-Continue coordinate, the one-stage absorbing contribution
is exactly the probability that some opponent quits. -/
theorem rootAbsorbingContribution_update_pure_false
    (root : Bool → PMF Bool) (who : Bool) :
    quittingRootAbsorbingContribution reward
        (Function.update root who (PMF.pure false)) who =
      1 - quittingStationaryContinueMass
        (Function.update root who (PMF.pure false)) := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  have hexpect :
      expect (pmfPi (Function.update root who (PMF.pure false)))
          (fun action =>
            quittingRootPayoff reward (0 : Payoff Bool) action who) =
        expect (pmfPi (Function.update root who (PMF.pure false)))
          (quittingSomeOpponentQuitsIndicator who) := by
    apply Math.ProbabilityMassFunction.expect_congr_on_support
    intro action haction
    have hown : action who = false :=
      action_eq_false_of_mem_support_pmfPi_update_pure_false
        root who action haction
    by_cases hopponent : quittingSomeOpponentQuits who action
    · have hnonempty : (quittingQuitters action).Nonempty := by
        obtain ⟨other, hother, hquit⟩ := hopponent
        exact ⟨other, by simpa [quittingQuitters] using hquit⟩
      have hnotmem : who ∉ quittingQuitters action := by
        simp [quittingQuitters, hown]
      have hflag : quittingOpponentQuitFlag who action = true :=
        (quittingOpponentQuitFlag_eq_true_iff who action).2 hopponent
      simp [quittingRootPayoff, hnonempty, reward, hnotmem,
        quittingSomeOpponentQuitsIndicator, hflag]
    · have hempty : ¬(quittingQuitters action).Nonempty := by
        rw [quittingQuitters_nonempty_iff]
        rintro ⟨player, hquit⟩
        by_cases hplayer : player = who
        · subst player
          simp [hown] at hquit
        · exact hopponent ⟨player, hplayer, hquit⟩
      have hflag : quittingOpponentQuitFlag who action = false := by
        cases h : quittingOpponentQuitFlag who action with
        | false => rfl
        | true =>
            exact (hopponent
              ((quittingOpponentQuitFlag_eq_true_iff who action).1 h)).elim
      simp [quittingRootPayoff, hempty,
        quittingSomeOpponentQuitsIndicator, hflag]
  rw [hexpect]
  simpa [quittingStationaryContinueMass] using
    (expect_pmfPi_someOpponentQuits_eq_one_sub_continueMass
      root who (PMF.pure false))

/-- Specialized form used in the Bellman coefficients of a root sequence. -/
theorem fixedOpponentsContinueReward_eq_one_sub_mass
    (roots : ℕ → Bool → PMF Bool) (who : Bool) (time : ℕ) :
    quittingFixedOpponentsContinueReward reward roots who time =
      1 - quittingFixedOpponentsContinueMass roots who time := by
  simpa [quittingFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueMass] using
    (rootAbsorbingContribution_update_pure_false (roots time) who)

/-- First-opponent-quit mass telescopes to one minus deleted survival. -/
theorem sum_opponentFirstQuitMass
    (roots : ℕ → Bool → PMF Bool) (who : Bool) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
      quittingOpponentSurvivalWeight roots who 0 time *
        (1 - quittingFixedOpponentsContinueMass roots who time)) =
      1 - quittingOpponentSurvivalWeight roots who 0 cutoff := by
  induction cutoff with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ cutoff ih =>
      rw [Finset.sum_range_succ, ih,
        quittingOpponentSurvivalWeight_succ]
      simp only [Nat.zero_add]
      ring

/-- If a player always continues against a plan truncated at `cutoff`, their
terminal payoff is exactly the probability that an opponent quits before the
cutoff. -/
theorem alwaysContinueValue_truncatedRoots
    (plan : ℕ → Bool → PMF Bool) (who : Bool) (cutoff : ℕ) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingTruncatedRoots plan cutoff) who
        quittingAlwaysContinueHazard 0 =
      1 - quittingOpponentSurvivalWeight plan who 0 cutoff := by
  have htruncated :
      quittingTruncatedHazard quittingAlwaysContinueHazard cutoff =
        quittingAlwaysContinueHazard := by
    funext time
    by_cases htime : time < cutoff
    · rw [quittingTruncatedHazard_of_lt _ htime]
    · rw [quittingTruncatedHazard_of_le _ (Nat.not_lt.mp htime)]
      rfl
  have hupdate := quittingRootSequenceUpdate_quittingTruncatedRoots
    plan who quittingAlwaysContinueHazard cutoff
  rw [htruncated] at hupdate
  unfold quittingRootSequenceHazardTerminalValue
  rw [hupdate,
    quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum]
  calc
    (∑ offset ∈ Finset.range cutoff,
        quittingJointSurvivalWeight
            (quittingRootSequenceUpdate plan who
              quittingAlwaysContinueHazard) 0 offset *
          quittingRootAbsorbingContribution reward
            ((quittingRootSequenceUpdate plan who
              quittingAlwaysContinueHazard) offset) who) =
      ∑ offset ∈ Finset.range cutoff,
        quittingOpponentSurvivalWeight plan who 0 offset *
          (1 - quittingFixedOpponentsContinueMass plan who offset) := by
      apply Finset.sum_congr rfl
      intro offset hoffset
      rw [quittingJointSurvivalWeight_quittingRootSequenceUpdate_alwaysContinue]
      rw [← quittingPureTimeHazard_none_eq_quittingAlwaysContinueHazard]
      simp only [quittingRootSequenceUpdate, quittingPureTimeHazard_none]
      rw [rootAbsorbingContribution_update_pure_false]
      rfl
    _ = 1 - quittingOpponentSurvivalWeight plan who 0 cutoff :=
      sum_opponentFirstQuitMass plan who cutoff

/-- The terminal reward bound is at least one on this table. -/
theorem one_le_rewardBound : 1 ≤ quittingRewardBound reward := by
  have hbound := abs_reward_le_quittingRewardBound reward
    (quittingSingletonTerminal false) true
  simpa [reward, quittingSingletonTerminal] using hbound

/-- The reduced truncated-ledger package fails already at accuracy `1/2`. -/
theorem not_hasQuittingTruncatedLedgerCapPackage_half :
    ¬HasQuittingTruncatedLedgerCapPackage reward (1 / 2 : ℝ) := by
  rintro ⟨plan, cutoff, ledgerCap, quitRegretCap, reach,
    hquitRegretCap, hledger, hregret, hreach, herror⟩
  have hledgerCap : 0 ≤ ledgerCap := by
    simpa [quittingLedger] using hledger false 0 (Nat.zero_le cutoff)
  have hreachNonneg : 0 ≤ reach :=
    (quittingOpponentSurvivalWeight_nonneg plan false 0 cutoff).trans
      (hreach false)
  have hsmallReach : reach ≤ 1 / 10 := by
    have hbound := one_le_rewardBound
    have herr := herror false
    nlinarith [mul_nonneg hreachNonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5)
        (quittingRewardBound_nonneg reward))]
  have hcap (who : Bool) :
      quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan cutoff) who
          quittingAlwaysContinueHazard 0 ≤
        quittingRootSequenceTerminalValue reward
            (quittingTruncatedRoots plan cutoff) who 0 + (1 / 2 : ℝ) := by
    have h :=
      quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le
        reward plan who cutoff
        (quittingRewardBound_nonneg reward) hquitRegretCap
        (abs_reward_le_quittingRewardBound reward)
        (hledger who) (hregret who) (hreach who)
        quittingAlwaysContinueHazard
    linarith [h, herror who]
  have hfalse :
      1 - reach ≤
        quittingRootSequenceTerminalValue reward
          (quittingTruncatedRoots plan cutoff) false 0 + (1 / 2 : ℝ) := by
    calc
      1 - reach ≤
          1 - quittingOpponentSurvivalWeight plan false 0 cutoff := by
            linarith [hreach false]
      _ = quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan cutoff) false
          quittingAlwaysContinueHazard 0 :=
            (alwaysContinueValue_truncatedRoots plan false cutoff).symm
      _ ≤ _ := hcap false
  have htrue :
      1 - reach ≤
        quittingRootSequenceTerminalValue reward
          (quittingTruncatedRoots plan cutoff) true 0 + (1 / 2 : ℝ) := by
    calc
      1 - reach ≤
          1 - quittingOpponentSurvivalWeight plan true 0 cutoff := by
            linarith [hreach true]
      _ = quittingRootSequenceHazardTerminalValue reward
          (quittingTruncatedRoots plan cutoff) true
          quittingAlwaysContinueHazard 0 :=
            (alwaysContinueValue_truncatedRoots plan true cutoff).symm
      _ ≤ _ := hcap true
  have hzeroSum := rootSequenceTerminalValue_false_add_true
    (quittingTruncatedRoots plan cutoff) 0
  nlinarith

/-- Therefore the repository's current unconditional reduced-cap conjecture
is false, even though this game has an exact uniform equilibrium payoff. -/
theorem not_quittingGame_hasQuittingTruncatedLedgerCapPackage :
    ¬(∀ ε : ℝ, 0 < ε →
      HasQuittingTruncatedLedgerCapPackage reward ε) := by
  intro h
  exact not_hasQuittingTruncatedLedgerCapPackage_half
    (h (1 / 2) (by norm_num))

end QuittingTruncatedLedgerCapCounterexample

end GameTheory
