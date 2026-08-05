/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteDynamicDebt
import GameTheory.Concepts.Stochastic.QuittingBehaviorPureTimeExtremality

/-!
# Finite behavioral semantics of exact quitting debt

The recursion `quittingFiniteDynamicDebt` is not merely an algebraic upper
envelope.  After adding back the prescribed value it is exactly the finite
optimal-stopping value against the supplied opponent roots, with terminal
live payoff equal to the prescribed terminal value plus the supplied debt.

The stopping problem allows an arbitrary time-dependent mixed hazard.  Such
hazards are the complete behavioral deviations on the unique live history of
a quitting game.  We prove both domination of every mixed hazard and
attainment by a deterministic quit time.  Thus the resulting debt is exactly
the unrestricted finite-horizon behavioral gain for the displayed terminal
boundary.

No infinite-horizon limit or equilibrium construction is asserted here.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Terminal-boundary stopping problem -/

/-- Finite payoff of an arbitrary mixed hazard against fixed opponent roots,
with a supplied payoff if the live path survives the truncation. -/
def quittingFiniteTerminalHazardValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (terminalValue : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => terminalValue
  | start, fuel + 1 =>
      (hazard start true).toReal *
          quittingFixedOpponentsQuitValue reward roots who start +
        (hazard start false).toReal *
          (quittingFixedOpponentsContinueReward reward roots who start +
            quittingFixedOpponentsContinueMass roots who start *
              quittingFiniteTerminalHazardValue reward roots who hazard
                terminalValue (start + 1) fuel)

/-- Value of one deterministic quit time, including the last alternative
which continues throughout and receives the terminal live payoff. -/
def quittingFiniteTerminalPureTimeValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (terminalValue : ℝ)
    (start : ℕ) : (fuel : ℕ) → Fin (fuel + 1) → ℝ
  | 0, _ => terminalValue
  | fuel + 1, choice =>
      Fin.cases
        (quittingFixedOpponentsQuitValue reward roots who start)
        (fun later =>
          quittingFixedOpponentsContinueReward reward roots who start +
            quittingFixedOpponentsContinueMass roots who start *
              quittingFiniteTerminalPureTimeValue reward roots who
                terminalValue (start + 1) fuel later)
        choice

/-- Bellman maximum for the same finite terminal-boundary stopping problem. -/
def quittingFiniteTerminalBestResponseValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (terminalValue : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => terminalValue
  | start, fuel + 1 =>
      max (quittingFixedOpponentsQuitValue reward roots who start)
        (quittingFixedOpponentsContinueReward reward roots who start +
          quittingFixedOpponentsContinueMass roots who start *
            quittingFiniteTerminalBestResponseValue reward roots who
              terminalValue (start + 1) fuel)

@[simp] theorem quittingFiniteTerminalHazardValue_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (terminalValue : ℝ) (start : ℕ) :
    quittingFiniteTerminalHazardValue reward roots who hazard terminalValue
      start 0 = terminalValue := rfl

@[simp] theorem quittingFiniteTerminalBestResponseValue_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (terminalValue : ℝ) (start : ℕ) :
    quittingFiniteTerminalBestResponseValue reward roots who terminalValue
      start 0 = terminalValue := rfl

/-! ## Exact optimality -/

/-- Every deterministic quit-time alternative is below the Bellman maximum. -/
theorem quittingFiniteTerminalPureTimeValue_le_bestResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (terminalValue : ℝ) :
    ∀ start fuel (choice : Fin (fuel + 1)),
      quittingFiniteTerminalPureTimeValue reward roots who terminalValue
          start fuel choice ≤
        quittingFiniteTerminalBestResponseValue reward roots who
          terminalValue start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro choice
      rfl
  | succ fuel ih =>
      intro choice
      refine Fin.cases ?_ (fun later => ?_) choice
      · exact le_max_left _ _
      · have hmass :
            0 ≤ quittingFixedOpponentsContinueMass roots who start :=
          quittingStationaryContinueMass_nonneg
            (Function.update (roots start) who (PMF.pure false))
        have hscaled := mul_le_mul_of_nonneg_left (ih (start + 1) later) hmass
        have hcontinue :
            quittingFixedOpponentsContinueReward reward roots who start +
                  quittingFixedOpponentsContinueMass roots who start *
                    quittingFiniteTerminalPureTimeValue reward roots who
                      terminalValue (start + 1) fuel later ≤
              quittingFixedOpponentsContinueReward reward roots who start +
                  quittingFixedOpponentsContinueMass roots who start *
                    quittingFiniteTerminalBestResponseValue reward roots who
                      terminalValue (start + 1) fuel := by
          linarith
        exact hcontinue.trans (le_max_right _ _)

/-- The finite Bellman maximum is attained by one deterministic quit-time
alternative (where the last alternative means never within the truncation). -/
theorem exists_quittingFiniteTerminalPureTimeValue_eq_bestResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (terminalValue : ℝ) :
    ∀ start fuel,
      ∃ choice : Fin (fuel + 1),
        quittingFiniteTerminalPureTimeValue reward roots who terminalValue
            start fuel choice =
          quittingFiniteTerminalBestResponseValue reward roots who
            terminalValue start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      exact ⟨0, rfl⟩
  | succ fuel ih =>
      obtain ⟨later, hlater⟩ := ih (start + 1)
      by_cases hcontinue :
          quittingFixedOpponentsQuitValue reward roots who start ≤
            quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingFiniteTerminalBestResponseValue reward roots who
                  terminalValue (start + 1) fuel
      · refine ⟨Fin.succ later, ?_⟩
        rw [quittingFiniteTerminalBestResponseValue,
          max_eq_right hcontinue]
        change
          quittingFixedOpponentsContinueReward reward roots who start +
                quittingFixedOpponentsContinueMass roots who start *
                  quittingFiniteTerminalPureTimeValue reward roots who
                    terminalValue (start + 1) fuel later =
            quittingFixedOpponentsContinueReward reward roots who start +
                quittingFixedOpponentsContinueMass roots who start *
                  quittingFiniteTerminalBestResponseValue reward roots who
                    terminalValue (start + 1) fuel
        rw [hlater]
      · refine ⟨0, ?_⟩
        rw [quittingFiniteTerminalBestResponseValue,
          max_eq_left (le_of_not_ge hcontinue)]
        rfl

/-- Every arbitrary mixed hazard is dominated by the finite Bellman maximum. -/
theorem quittingFiniteTerminalHazardValue_le_bestResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (terminalValue : ℝ) :
    ∀ start fuel,
      quittingFiniteTerminalHazardValue reward roots who hazard terminalValue
          start fuel ≤
        quittingFiniteTerminalBestResponseValue reward roots who terminalValue
          start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => exact le_rfl
  | succ fuel ih =>
      let quitValue := quittingFixedOpponentsQuitValue reward roots who start
      let continueValue :=
        quittingFixedOpponentsContinueReward reward roots who start +
          quittingFixedOpponentsContinueMass roots who start *
            quittingFiniteTerminalBestResponseValue reward roots who
              terminalValue (start + 1) fuel
      have hmass : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      have hcontinue :
          quittingFixedOpponentsContinueReward reward roots who start +
                quittingFixedOpponentsContinueMass roots who start *
                  quittingFiniteTerminalHazardValue reward roots who hazard
                    terminalValue (start + 1) fuel ≤
            continueValue := by
        dsimp only [continueValue]
        have hscaled := mul_le_mul_of_nonneg_left (ih (start + 1)) hmass
        linarith
      have hsum :
          (hazard start true).toReal + (hazard start false).toReal = 1 := by
        simpa [Fintype.sum_bool] using pmf_toReal_sum_one (hazard start)
      rw [quittingFiniteTerminalHazardValue,
        quittingFiniteTerminalBestResponseValue]
      change
        (hazard start true).toReal * quitValue +
            (hazard start false).toReal *
              (quittingFixedOpponentsContinueReward reward roots who start +
                quittingFixedOpponentsContinueMass roots who start *
                  quittingFiniteTerminalHazardValue reward roots who hazard
                    terminalValue (start + 1) fuel) ≤
          max quitValue continueValue
      calc
        (hazard start true).toReal * quitValue +
              (hazard start false).toReal *
                (quittingFixedOpponentsContinueReward reward roots who start +
                  quittingFixedOpponentsContinueMass roots who start *
                    quittingFiniteTerminalHazardValue reward roots who hazard
                      terminalValue (start + 1) fuel) ≤
            (hazard start true).toReal * max quitValue continueValue +
              (hazard start false).toReal * max quitValue continueValue := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (le_max_left quitValue continueValue) ENNReal.toReal_nonneg)
            (mul_le_mul_of_nonneg_left
              (hcontinue.trans (le_max_right quitValue continueValue))
              ENNReal.toReal_nonneg)
        _ = max quitValue continueValue := by
          rw [← add_mul, hsum, one_mul]

/-! ## Deterministic-hazard realization -/

/-- A nonterminal deterministic quit-time alternative is realized by the
explicit pure hazard which quits at its displayed absolute date. -/
theorem quittingFiniteTerminalPureTimeValue_castSucc_eq_hazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (terminalValue : ℝ) :
    ∀ (start fuel : ℕ) (choice : Fin fuel),
      quittingFiniteTerminalPureTimeValue reward roots who terminalValue
          start fuel choice.castSucc =
        quittingFiniteTerminalHazardValue reward roots who
          (quittingPureTimeHazard (some (start + choice.val))) terminalValue
          start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => exact fun choice => Fin.elim0 choice
  | succ fuel ih =>
      intro choice
      refine Fin.cases ?_ (fun later => ?_) choice
      · rw [quittingFiniteTerminalPureTimeValue,
          quittingFiniteTerminalHazardValue]
        simp
      · rw [quittingFiniteTerminalPureTimeValue,
          quittingFiniteTerminalHazardValue]
        simp only [Fin.castSucc_succ, Fin.cases_succ]
        have hne : start ≠ start + (Fin.succ later).val := by
          simp [Fin.val_succ]
        have htime :
            start + (Fin.succ later).val = (start + 1) + later.val := by
          simp [Fin.val_succ, Nat.add_comm, Nat.add_left_comm]
        rw [quittingPureTimeHazard_some_of_ne hne]
        simp only [PMF.pure_apply,
          if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
          if_true, ENNReal.toReal_one, zero_mul, one_mul]
        rw [ih (start + 1) later]
        rw [htime]
        simp only [zero_add]

/-- The last deterministic alternative is realized by the explicit hazard
which never quits during the truncation. -/
theorem quittingFiniteTerminalPureTimeValue_last_eq_neverHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (terminalValue : ℝ) :
    ∀ start fuel,
      quittingFiniteTerminalPureTimeValue reward roots who terminalValue
          start fuel (Fin.last fuel) =
        quittingFiniteTerminalHazardValue reward roots who
          (quittingPureTimeHazard none) terminalValue start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [show Fin.last (fuel + 1) = (Fin.last fuel).succ by rfl]
      rw [quittingFiniteTerminalPureTimeValue,
        quittingFiniteTerminalHazardValue]
      simp only [Fin.cases_succ, quittingPureTimeHazard_none,
        PMF.pure_apply, if_neg (by decide : (true : Bool) ≠ false),
        ENNReal.toReal_zero, if_true, ENNReal.toReal_one, zero_mul, one_mul]
      rw [ih (start + 1)]
      simp only [zero_add]

/-- The Bellman maximum is attained by an actual deterministic hazard, not
only by an abstract value in the finite quit-time list. -/
theorem exists_quittingFiniteTerminalHazardValue_eq_bestResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (terminalValue : ℝ)
    (start fuel : ℕ) :
    ∃ hazard : ℕ → PMF Bool,
      quittingFiniteTerminalHazardValue reward roots who hazard terminalValue
          start fuel =
        quittingFiniteTerminalBestResponseValue reward roots who terminalValue
          start fuel := by
  obtain ⟨choice, hchoice⟩ :=
    exists_quittingFiniteTerminalPureTimeValue_eq_bestResponse
      reward roots who terminalValue start fuel
  by_cases hlast : choice = Fin.last fuel
  · subst choice
    refine ⟨quittingPureTimeHazard none, ?_⟩
    rw [← quittingFiniteTerminalPureTimeValue_last_eq_neverHazard]
    exact hchoice
  · obtain ⟨earlier, hchoiceCast⟩ := choice.eq_castSucc_of_ne_last hlast
    subst hchoiceCast
    refine ⟨quittingPureTimeHazard (some (start + earlier.val)), ?_⟩
    rw [← quittingFiniteTerminalPureTimeValue_castSucc_eq_hazard]
    exact hchoice

/-! ## Identification with dynamic debt -/

/-- Adding back the prescribed value identifies dynamic debt exactly with
the finite Bellman maximum whose live terminal payoff is the prescribed
terminal value plus the supplied terminal debt.  No policy-evaluation or
sign hypothesis is needed for this algebraic identity. -/
theorem prescribed_add_quittingFiniteDynamicDebt_eq_bestResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (terminalDebt : ℝ) :
    ∀ start fuel,
      prescribed start +
          quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
            start fuel =
        quittingFiniteTerminalBestResponseValue reward roots who
          (prescribed (start + fuel) + terminalDebt) start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp
  | succ fuel ih =>
      have htail := ih (start + 1)
      rw [show start + (fuel + 1) = start + 1 + fuel by omega]
      rw [quittingFiniteDynamicDebt_succ,
        quittingFiniteTerminalBestResponseValue]
      rw [← htail]
      ring

/-- Exact semantic upper bound: the gain of every finite mixed behavioral
hazard, with the matching terminal live value, is at most dynamic debt. -/
theorem quittingFiniteTerminalHazardGain_le_dynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (terminalDebt : ℝ)
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) :
    quittingFiniteTerminalHazardValue reward roots who hazard
          (prescribed (start + fuel) + terminalDebt) start fuel -
        prescribed start ≤
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start fuel := by
  have hupper := quittingFiniteTerminalHazardValue_le_bestResponse
    reward roots who hazard (prescribed (start + fuel) + terminalDebt)
      start fuel
  rw [← prescribed_add_quittingFiniteDynamicDebt_eq_bestResponse
    reward roots who prescribed terminalDebt start fuel] at hupper
  linarith

/-- Exact semantic attainment: dynamic debt is the gain of one deterministic
quit time (or never) in the matching finite terminal-boundary problem. -/
theorem exists_quittingFiniteTerminalPureTimeGain_eq_dynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (terminalDebt : ℝ)
    (start fuel : ℕ) :
    ∃ choice : Fin (fuel + 1),
      quittingFiniteTerminalPureTimeValue reward roots who
            (prescribed (start + fuel) + terminalDebt) start fuel choice -
          prescribed start =
        quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel := by
  obtain ⟨choice, hchoice⟩ :=
    exists_quittingFiniteTerminalPureTimeValue_eq_bestResponse
      reward roots who (prescribed (start + fuel) + terminalDebt) start fuel
  refine ⟨choice, ?_⟩
  rw [hchoice, ← prescribed_add_quittingFiniteDynamicDebt_eq_bestResponse
    reward roots who prescribed terminalDebt start fuel]
  ring

/-- Strong semantic attainment form: one actual deterministic hazard has
gain exactly equal to the dynamic debt. -/
theorem exists_quittingFiniteTerminalHazardGain_eq_dynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (terminalDebt : ℝ)
    (start fuel : ℕ) :
    ∃ hazard : ℕ → PMF Bool,
      quittingFiniteTerminalHazardValue reward roots who hazard
            (prescribed (start + fuel) + terminalDebt) start fuel -
          prescribed start =
        quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start fuel := by
  obtain ⟨hazard, hhazard⟩ :=
    exists_quittingFiniteTerminalHazardValue_eq_bestResponse
      reward roots who (prescribed (start + fuel) + terminalDebt) start fuel
  refine ⟨hazard, ?_⟩
  rw [hhazard, ← prescribed_add_quittingFiniteDynamicDebt_eq_bestResponse
    reward roots who prescribed terminalDebt start fuel]
  ring

/-! ## Standard zero-boundary and behavior-profile adapters -/

/-- With zero terminal live value, the terminal-boundary hazard recursion is
the existing finite quitting payoff. -/
theorem quittingFiniteTerminalHazardValue_zero_eq_finiteRootPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) :
    quittingFiniteTerminalHazardValue reward roots who hazard 0 start fuel =
      quittingFiniteRootPayoff reward roots who hazard start fuel := by
  rw [quittingFiniteRootPayoff_eq_hazardValue]
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [quittingFiniteTerminalHazardValue, quittingFiniteHazardValue,
        ih (start + 1)]

/-- Replacing a root sequence's own coordinate by the very same hazard does
not change its finite payoff; the player's original coordinate is ignored
when fixed opponents are formed. -/
theorem quittingFiniteRootPayoff_rootSequenceUpdate_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) :
    ∀ start fuel,
      quittingFiniteRootPayoff reward
          (quittingRootSequenceUpdate roots who hazard) who hazard start fuel =
        quittingFiniteRootPayoff reward roots who hazard start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [quittingFiniteRootPayoff, quittingFiniteRootPayoff,
        ih (start + 1)]
      unfold quittingRootSequenceUpdate
      rw [Function.update_idem]

/-- Every unrestricted behavioral deviation has the finite payoff of its
induced live-path hazard against the original opponents' live roots. -/
theorem expectedStagePayoff_update_eq_finiteRootPayoff_liveHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    (fuel : ℕ) :
    (quittingGame reward).expectedStagePayoff
        (Function.update profile who deviation) none fuel who =
      quittingFiniteRootPayoff reward
        (quittingProfileLiveRoot reward profile) who
        (quittingBehaviorLiveHazard reward deviation) 0 fuel := by
  let updated := Function.update profile who deviation
  have hspine :=
    quittingFiniteRootPayoff_profileSpine_eq_expectedStagePayoff
      reward updated who 0 fuel
  rw [quittingProfileSpineRoot_eq_profileLiveRoot] at hspine
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate] at hspine
  rw [show quittingAllContinueProfileSpine reward updated 0 = updated by rfl]
    at hspine
  have hself :
      (fun time ↦
        quittingRootSequenceUpdate (quittingProfileLiveRoot reward profile)
          who (quittingBehaviorLiveHazard reward deviation) time who) =
        quittingBehaviorLiveHazard reward deviation := by
    funext time
    simp [quittingRootSequenceUpdate]
  rw [hself] at hspine
  change
    quittingFiniteRootPayoff reward
        (quittingRootSequenceUpdate (quittingProfileLiveRoot reward profile)
          who (quittingBehaviorLiveHazard reward deviation))
        who (quittingBehaviorLiveHazard reward deviation) 0 fuel =
      (quittingGame reward).expectedStagePayoff updated none fuel who at hspine
  rw [quittingFiniteRootPayoff_rootSequenceUpdate_self] at hspine
  exact hspine.symm

/-- Zero-terminal dynamic debt is exactly the unrestricted finite-horizon
behavioral deviation gain above a zero prescribed endpoint. -/
theorem expectedStagePayoff_update_sub_prescribed_le_dynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    (prescribed : ℕ → ℝ) (fuel : ℕ)
    (hterminal : prescribed fuel = 0) :
    (quittingGame reward).expectedStagePayoff
          (Function.update profile who deviation) none fuel who -
        prescribed 0 ≤
      quittingFiniteDynamicDebt reward
        (quittingProfileLiveRoot reward profile) who prescribed 0 0 fuel := by
  rw [expectedStagePayoff_update_eq_finiteRootPayoff_liveHazard]
  rw [← quittingFiniteTerminalHazardValue_zero_eq_finiteRootPayoff]
  simpa only [Nat.zero_add, hterminal, zero_add] using
    quittingFiniteTerminalHazardGain_le_dynamicDebt reward
      (quittingProfileLiveRoot reward profile) who prescribed 0
      (quittingBehaviorLiveHazard reward deviation) 0 fuel

/-- Conversely, when the displayed prescribed endpoint is zero, an actual
behavior strategy attains the zero-terminal dynamic debt at that finite
horizon.  Together with the preceding upper bound this identifies dynamic
debt with the unrestricted finite-horizon behavioral deviation gain. -/
theorem exists_expectedStagePayoff_update_sub_prescribed_eq_dynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (prescribed : ℕ → ℝ) (fuel : ℕ)
    (hterminal : prescribed fuel = 0) :
    ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      (quittingGame reward).expectedStagePayoff
            (Function.update profile who deviation) none fuel who -
          prescribed 0 =
        quittingFiniteDynamicDebt reward
          (quittingProfileLiveRoot reward profile) who prescribed 0 0 fuel := by
  obtain ⟨hazard, hhazard⟩ :=
    exists_quittingFiniteTerminalHazardGain_eq_dynamicDebt reward
      (quittingProfileLiveRoot reward profile) who prescribed 0 0 fuel
  have hhazardZero :
      quittingFiniteTerminalHazardValue reward
            (quittingProfileLiveRoot reward profile) who hazard 0 0 fuel -
          prescribed 0 =
        quittingFiniteDynamicDebt reward
          (quittingProfileLiveRoot reward profile) who prescribed 0 0 fuel := by
    simpa only [Nat.zero_add, hterminal, zero_add] using hhazard
  let deviation : (quittingGame reward).BehaviorStrategy who :=
    fun time _history => hazard time
  refine ⟨deviation, ?_⟩
  rw [expectedStagePayoff_update_eq_finiteRootPayoff_liveHazard]
  have hlive : quittingBehaviorLiveHazard reward deviation = hazard := by
    funext time
    rfl
  rw [hlive, ← quittingFiniteTerminalHazardValue_zero_eq_finiteRootPayoff]
  exact hhazardZero

end GameTheory
