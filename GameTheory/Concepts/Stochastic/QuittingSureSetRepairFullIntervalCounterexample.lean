/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSureSetRepairCounterexample
import GameTheory.Concepts.Stochastic.QuittingSureSetOwnerRepair

/-!
# A full-interval obstruction to sure-set owner repair

This three-player table strengthens the zero-hazard calibration in
`QuittingSureSetRepairCounterexample`.  Its uniform half--half--half root is
an exact zero-tail Nash root with positive exact debt only for player zero;
the same full two-opponent atom carries positive owner advantage, and every
owner-solo rate has a joining obstruction.  More strongly, every stationary
architecture in which player zero uses any positive hazard and an arbitrary
subset of the other two players Quits surely has exact terminal
exploitability at least `1/3`.

Every direct pure First set also fails.  These are architecture
counterexamples only: no claim is made about optimized positive debt or
about arbitrary time-inhomogeneous or behavioral profiles.  Indeed the final
section gives an exact mixed stationary repair with one sure quitter and two
nontrivial hazard coordinates, sharply delimiting the negative result.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

namespace QuittingSureSetRepairFullIntervalCounterexample

abbrev Player := Fin 3
abbrev Terminal := {S : Finset Player // S.Nonempty}

@[simp] theorem player_zero_ne_one : (0 : Player) ≠ 1 := by decide
@[simp] theorem player_zero_ne_two : (0 : Player) ≠ 2 := by decide
@[simp] theorem player_one_ne_zero : (1 : Player) ≠ 0 := by decide
@[simp] theorem player_one_ne_two : (1 : Player) ≠ 2 := by decide
@[simp] theorem player_two_ne_zero : (2 : Player) ≠ 0 := by decide
@[simp] theorem player_two_ne_one : (2 : Player) ≠ 1 := by decide

/-- Payoff rows on `{0},{1},{2},{0,1},{0,2},{1,2},{0,1,2}` are

* player zero: `1,0,0,1,1,4,1`;
* player one: `-1,0,5,1,0,0,3`;
* player two: `0,1,0,0,0,0,1`.
-/
def reward (S : Terminal) : Payoff Player :=
  fun who ↦
    if who = 0 then
      if 0 ∈ S.1 then 1 else if 1 ∈ S.1 ∧ 2 ∈ S.1 then 4 else 0
    else if who = 1 then
      if 2 ∈ S.1 ∧ 0 ∉ S.1 ∧ 1 ∉ S.1 then 5
      else if 0 ∈ S.1 ∧ 1 ∈ S.1 then
        if 2 ∈ S.1 then 3 else 1
      else if 0 ∈ S.1 ∧ 1 ∉ S.1 ∧ 2 ∉ S.1 then -1
      else 0
    else
      if (1 ∈ S.1 ∧ 0 ∉ S.1 ∧ 2 ∉ S.1) ∨
          (0 ∈ S.1 ∧ 1 ∈ S.1 ∧ 2 ∈ S.1) then 1 else 0

@[simp] theorem reward_0 (h : ({0} : Finset Player).Nonempty) :
    reward ⟨{0}, h⟩ = ![1, -1, 0] := by
  funext who
  fin_cases who <;> simp [reward]

@[simp] theorem reward_1 (h : ({1} : Finset Player).Nonempty) :
    reward ⟨{1}, h⟩ = ![0, 0, 1] := by
  funext who
  fin_cases who <;> simp [reward]

@[simp] theorem reward_2 (h : ({2} : Finset Player).Nonempty) :
    reward ⟨{2}, h⟩ = ![0, 5, 0] := by
  funext who
  fin_cases who <;> simp [reward]

@[simp] theorem reward_01 (h : ({0, 1} : Finset Player).Nonempty) :
    reward ⟨{0, 1}, h⟩ = ![1, 1, 0] := by
  funext who
  fin_cases who <;> simp [reward]

@[simp] theorem reward_02 (h : ({0, 2} : Finset Player).Nonempty) :
    reward ⟨{0, 2}, h⟩ = ![1, 0, 0] := by
  funext who
  fin_cases who <;> simp [reward]

@[simp] theorem reward_12 (h : ({1, 2} : Finset Player).Nonempty) :
    reward ⟨{1, 2}, h⟩ = ![4, 0, 0] := by
  funext who
  fin_cases who <;> simp [reward]

@[simp] theorem reward_012 (h : ({0, 1, 2} : Finset Player).Nonempty) :
    reward ⟨{0, 1, 2}, h⟩ = ![1, 3, 1] := by
  funext who
  fin_cases who <;> simp [reward]

/-- Both actions have probability one half for every player. -/
def root : Player → PMF Bool := fun _ ↦ PMF.uniformOfFintype Bool

def value : Payoff Player := ![1, 1, 1 / 4]
def positiveContinueValue : Payoff Player := ![5 / 4, 1, 1 / 4]

theorem expect_pmfPi_fin3_bool (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) fun a ↦
        expect (sigma 1) fun b ↦
          expect (sigma 2) fun c ↦ f ![a, b, c] :=
  QuittingSureSetRepairCounterexample.expect_pmfPi_fin3_bool sigma f

@[simp] theorem expect_uniform_bool (f : Bool → ℝ) :
    expect (PMF.uniformOfFintype Bool) f = (f false + f true) / 2 :=
  QuittingSureSetRepairCounterexample.expect_uniform_bool f

@[simp] theorem quitters_vector (a b c : Bool) :
    quittingQuitters (![a, b, c] : Player → Bool) =
      (if a then {0} else ∅) ∪ (if b then {1} else ∅) ∪
        (if c then {2} else ∅) :=
  QuittingSureSetRepairCounterexample.quitters_vector a b c

/-! ## Exact root, debt, and marked packet -/

theorem quitPayoff_eq_value (who : Player) :
    quittingRootQuitPayoff reward (0 : Payoff Player) root who = value who := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [root, quittingRootPayoff, reward, value] <;>
      norm_num

theorem continuePayoff_eq_value (who : Player) :
    quittingRootContinuePayoff reward (0 : Payoff Player) root who = value who := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [root, quittingRootPayoff, reward, value] <;>
      norm_num

theorem root_isEndpointNash_zero :
    IsεQuittingRootEndpointNash reward (0 : Payoff Player) 0 root := by
  intro who
  rw [quittingRootEndpointDifference, quitPayoff_eq_value,
    continuePayoff_eq_value]
  norm_num

theorem root_isNash_zero :
    IsεQuittingRootNash reward (0 : Payoff Player) 0 root := by
  exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward (0 : Payoff Player) root).1 root_isEndpointNash_zero

theorem root_successor_zero :
    quittingRootSuccessorPayoff reward (0 : Payoff Player) root = value := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    quitPayoff_eq_value, continuePayoff_eq_value]
  simp [root, PMF.uniformOfFintype_apply]
  ring

@[simp] theorem positiveSingletonDebtCap_zero :
    quittingPositiveSingletonDebtCap reward 0 = 1 := by
  norm_num [quittingPositiveSingletonDebtCap, reward,
    quittingSingletonTerminal]

@[simp] theorem positiveSingletonDebtCap_one :
    quittingPositiveSingletonDebtCap reward 1 = 0 := by
  norm_num [quittingPositiveSingletonDebtCap, reward,
    quittingSingletonTerminal]

@[simp] theorem positiveSingletonDebtCap_two :
    quittingPositiveSingletonDebtCap reward 2 = 0 := by
  norm_num [quittingPositiveSingletonDebtCap, reward,
    quittingSingletonTerminal]

theorem positiveContinuePayoff_eq (who : Player) :
    quittingCutoffOnePositiveContinuePayoff reward root who =
      positiveContinueValue who := by
  unfold quittingCutoffOnePositiveContinuePayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [root, quittingRootPayoff, reward,
      positiveContinueValue] <;> norm_num

/-- Again only player zero has positive exact cutoff-one debt. -/
theorem cutoffOneDynamicDebt_eq (who : Player) :
    quittingCutoffOneDynamicDebt reward root who =
      (![1 / 4, 0, 0] : Payoff Player) who := by
  rw [quittingCutoffOneDynamicDebt_eq, quitPayoff_eq_value,
    positiveContinuePayoff_eq]
  have hvalue := congrFun root_successor_zero who
  rw [hvalue]
  fin_cases who <;> norm_num [value, positiveContinueValue]

theorem owner_exactDebt_pos :
    0 < quittingCutoffOneDynamicDebt reward root 0 := by
  rw [cutoffOneDynamicDebt_eq]
  norm_num

def markedAction : Player → Bool := ![false, true, true]

theorem markedAction_mass :
    ((pmfPi (Function.update root 0 (PMF.pure false))) markedAction).toReal =
      1 / 4 := by
  rw [pmfPi_apply, Fin.prod_univ_three]
  simp [root, markedAction, PMF.uniformOfFintype_apply]
  norm_num

theorem markedAction_terminalAdvantage :
    quittingTerminalOpponentAdvantage reward 0 markedAction = 3 := by
  have hupdate : Function.update markedAction 0 true =
      (![true, true, true] : Player → Bool) := by
    funext who
    fin_cases who <;> simp [markedAction]
  unfold quittingTerminalOpponentAdvantage
  rw [hupdate]
  norm_num [quittingRootPayoff, markedAction, quitters_vector, reward,
    quittingSingletonTerminal]

/-- The obstruction is even strict at zero scale: player one's owner-solo
payoff is `-1`, while its immediate-Quit mixture is `p`. -/
theorem universal_ownerSolo_obstruction :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      QuittingSoloJoiningObstruction reward 0 p := by
  intro p hp _
  refine ⟨1, by decide, ?_⟩
  norm_num [quittingSoloReward, quittingSingletonCollisionReward, reward]
  linarith

theorem sureSetOwnerRoot_empty_eq_solo
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingSureSetOwnerRoot (∅ : Finset Player) 0 p hp0 hp1 =
      quittingSoloStationaryRoot 0 (quittingHazardCoin p hp0 hp1) := by
  unfold quittingSureSetOwnerRoot quittingSoloStationaryRoot
  congr 1

/-- The empty-sure-set chart is quantitatively worse: player one's Quit-now
deviation gains `p + 1`, hence more than one at every positive hazard. -/
theorem not_isεAsymptoticNash_sureSetOwnerRoot_empty
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 0 < p)
    (ε : ℝ) (hε : ε < 1) :
    ¬ (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward
          (quittingSureSetOwnerRoot ∅ 0 p hp0 hp1)) := by
  intro hnash
  rw [sureSetOwnerRoot_empty_eq_solo p hp0 hp1] at hnash
  have hquit := hnash 1
    (quittingPureTimeBehaviorStrategy reward 1 (some 0))
  have hhazard :
      0 < ((quittingHazardCoin p hp0 hp1) true).toReal := by
    simpa using hp
  rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue,
    quittingProfileLiveRoot_stationary,
    quittingTerminalPayoff_soloStationary reward 0 1
      (quittingHazardCoin p hp0 hp1) hhazard,
    quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
      reward (by decide) (quittingHazardCoin p hp0 hp1)] at hquit
  norm_num [quittingSoloReward, quittingSingletonCollisionReward,
    reward] at hquit
  linarith

/-! ## A uniform gap for every nonempty sure-set owner repair -/

private theorem nonempty_without_zero_cases (T : Finset Player)
    (hne : T.Nonempty) (hzero : 0 ∉ T) :
    T = {1} ∨ T = {2} ∨ T = {1, 2} := by
  by_cases h1 : 1 ∈ T
  · by_cases h2 : 2 ∈ T
    · right; right
      ext who
      fin_cases who <;> simp [hzero, h1, h2]
    · left
      ext who
      fin_cases who <;> simp [hzero, h1, h2]
  · by_cases h2 : 2 ∈ T
    · right; left
      ext who
      fin_cases who <;> simp [hzero, h1, h2]
    · obtain ⟨who, hwho⟩ := hne
      fin_cases who <;> simp_all

/-- At every positive owner hazard, one player has exact stationary
unilateral gain at least `1/3`.  This theorem covers every nonempty sure set
of the two nonowners, including the full-rate endpoint `p = 1`. -/
theorem exists_exactCap_gap_nonempty
    (T : Finset Player) (hT : T.Nonempty) (howner : 0 ∉ T)
    (p : ℝ) (hp : 0 < p) :
    ∃ who : Player,
      quittingSureSetOwnerValue reward T 0 p who + 1 / 3 ≤
        quittingSureSetOwnerExactCap reward T 0 p who := by
  rcases nonempty_without_zero_cases T hT howner with hT | hT | hT
  · subst T
    by_cases hsmall : p ≤ 2 / 3
    · refine ⟨0, ?_⟩
      norm_num [quittingSureSetOwnerValue,
        quittingSureSetOwnerExactCap, quittingSetReward, reward]
      linarith
    · refine ⟨2, ?_⟩
      norm_num [quittingSureSetOwnerValue,
        quittingSureSetOwnerExactCap, quittingSetReward, reward]
      linarith
  · subst T
    by_cases hsmall : p ≤ 2 / 3
    · refine ⟨0, ?_⟩
      norm_num [quittingSureSetOwnerValue,
        quittingSureSetOwnerExactCap, quittingSetReward, reward]
      linarith
    · refine ⟨1, ?_⟩
      norm_num [quittingSureSetOwnerValue,
        quittingSureSetOwnerExactCap, quittingSetReward, reward]
      linarith
  · subst T
    by_cases hlarge : 1 / 9 ≤ p
    · refine ⟨0, ?_⟩
      norm_num [quittingSureSetOwnerValue,
        quittingSureSetOwnerExactCap, quittingSetReward, reward]
      linarith
    · refine ⟨1, ?_⟩
      norm_num [quittingSureSetOwnerValue,
        quittingSureSetOwnerExactCap, quittingSetReward, reward]
      linarith

/-- Consequently no nonempty sure-set owner architecture on this table is a
terminal `ε`-Nash equilibrium below the uniform `1/3` threshold. -/
theorem not_isεAsymptoticNash_sureSetOwnerRoot
    (T : Finset Player) (hT : T.Nonempty) (howner : 0 ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 0 < p)
    (ε : ℝ) (hε : ε < 1 / 3) :
    ¬ (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward
          (quittingSureSetOwnerRoot T 0 p hp0 hp1)) := by
  intro hnash
  have hcap :=
    (isεAsymptoticNash_sureSetOwnerRoot_iff_exactCap_le
      reward hT howner p hp0 hp1 hp ε).1 hnash
  obtain ⟨who, hgap⟩ :=
    exists_exactCap_gap_nonempty T hT howner p hp
  have hwho := hcap who
  rw [terminalPayoff_sureSetOwnerRoot
    reward hT howner p hp0 hp1 who] at hwho
  linarith

/-- Uniform semantic exclusion of the entire owner-zero/sure-set grammar,
including its owner-solo (`T = ∅`) chart. -/
theorem not_isεAsymptoticNash_sureSetOwnerRoot_all
    (T : Finset Player) (howner : 0 ∉ T)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 0 < p)
    (ε : ℝ) (hε : ε < 1 / 3) :
    ¬ (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward
          (quittingSureSetOwnerRoot T 0 p hp0 hp1)) := by
  by_cases hT : T.Nonempty
  · exact not_isεAsymptoticNash_sureSetOwnerRoot
      T hT howner p hp0 hp1 hp ε hε
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst T
    exact not_isεAsymptoticNash_sureSetOwnerRoot_empty
      p hp0 hp1 hp ε (by linarith)

/-! ## Direct pure First profiles -/

theorem terminalPayoff_pureSetRoot
    (S : Finset Player) (hS : S.Nonempty) (who : Player) :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward (quittingPureSetRoot S)) who =
      quittingSetReward reward S who := by
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
  · rw [quittingRootAbsorbingContribution_pureSetRoot,
      stationaryContinueMass_pureSetRoot_of_nonempty hS]
    norm_num
  · rw [stationaryContinueMass_pureSetRoot_of_nonempty hS]
    norm_num

theorem fixedOpponentsQuitValue_pureSetRoot
    (S : Finset Player) (who : Player) :
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingPureSetRoot S) who =
      quittingSetReward reward (insert who S) who := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue
  rw [update_quittingPureSetRoot_true,
    quittingRootAbsorbingContribution_pureSetRoot]

theorem fixedOpponentsContinueReward_pureSetRoot
    (S : Finset Player) (who : Player) :
    quittingStationaryFixedOpponentsContinueReward reward
        (quittingPureSetRoot S) who =
      quittingSetReward reward (S.erase who) who := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward
  rw [update_quittingPureSetRoot_false,
    quittingRootAbsorbingContribution_pureSetRoot]

theorem fixedOpponentsContinueMass_pureSetRoot_of_erase_nonempty
    (S : Finset Player) (who : Player) (hS : (S.erase who).Nonempty) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingPureSetRoot S) who = 0 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [update_quittingPureSetRoot_false,
    stationaryContinueMass_pureSetRoot_of_nonempty hS]

theorem not_isεAsymptoticNash_pureSetRoot_of_quitNow_gain
    (S : Finset Player) (hS : S.Nonempty) (who : Player)
    (ε : ℝ)
    (hgain : quittingSetReward reward S who + ε <
      quittingSetReward reward (insert who S) who) :
    ¬ (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward (quittingPureSetRoot S)) := by
  intro hnash
  have hquit := hnash who
    (quittingPureTimeBehaviorStrategy reward who (some 0))
  rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue,
    quittingProfileLiveRoot_stationary,
    fixedOpponentsQuitValue_pureSetRoot,
    terminalPayoff_pureSetRoot S hS who] at hquit
  exact (not_lt_of_ge hquit) hgain

theorem not_isεAsymptoticNash_pureSetRoot_of_never_gain
    (S : Finset Player) (hS : S.Nonempty) (who : Player)
    (herase : (S.erase who).Nonempty) (ε : ℝ)
    (hgain : quittingSetReward reward S who + ε <
      quittingSetReward reward (S.erase who) who) :
    ¬ (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward (quittingPureSetRoot S)) := by
  intro hnash
  have hmass := fixedOpponentsContinueMass_pureSetRoot_of_erase_nonempty
    S who herase
  have hcontracts : quittingStationaryFixedOpponentsContinueMass
      (quittingPureSetRoot S) who < 1 := by
    rw [hmass]
    norm_num
  have hnever := hnash who
    (quittingPureTimeBehaviorStrategy reward who none)
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingProfileLiveRoot_stationary,
    quittingRootSequencePureTimeTerminalValue_const_none
      reward (quittingPureSetRoot S) who hcontracts 0,
    fixedOpponentsContinueReward_pureSetRoot, hmass,
    terminalPayoff_pureSetRoot S hS who] at hnever
  norm_num [quittingStationaryNeverValue] at hnever
  exact (not_lt_of_ge hnever) hgain

private theorem nonempty_fin3_cases (S : Finset Player)
    (hS : S.Nonempty) :
    S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {0, 1} ∨
      S = {0, 2} ∨ S = {1, 2} ∨ S = {0, 1, 2} := by
  by_cases h0 : 0 ∈ S
  · by_cases h1 : 1 ∈ S
    · by_cases h2 : 2 ∈ S
      · right; right; right; right; right; right
        ext who
        fin_cases who <;> simp [h0, h1, h2]
      · right; right; right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
    · by_cases h2 : 2 ∈ S
      · right; right; right; right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
      · left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
  · by_cases h1 : 1 ∈ S
    · by_cases h2 : 2 ∈ S
      · right; right; right; right; right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
      · right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
    · by_cases h2 : 2 ∈ S
      · right; right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
      · obtain ⟨who, hwho⟩ := hS
        fin_cases who <;> simp_all

/-- Every nonempty pure First profile has an actual unilateral gain of at
least one.  The first five witnesses Quit immediately; on `{1,2}` player one
Never quits, and on `{0,1,2}` player zero Never quits. -/
theorem not_isεAsymptoticNash_directPureSet
    (S : Finset Player) (hS : S.Nonempty)
    (ε : ℝ) (hε : ε < 1) :
    ¬ (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingStationaryProfile reward (quittingPureSetRoot S)) := by
  rcases nonempty_fin3_cases S hS with
      hS | hS | hS | hS | hS | hS | hS
  · subst S
    apply not_isεAsymptoticNash_pureSetRoot_of_quitNow_gain
      {0} (by simp) 1 ε
    norm_num [quittingSetReward, reward]
    linarith
  · subst S
    apply not_isεAsymptoticNash_pureSetRoot_of_quitNow_gain
      {1} (by simp) 0 ε
    norm_num [quittingSetReward, reward]
    linarith
  · subst S
    apply not_isεAsymptoticNash_pureSetRoot_of_quitNow_gain
      {2} (by simp) 0 ε
    norm_num [quittingSetReward, reward]
    linarith
  · subst S
    apply not_isεAsymptoticNash_pureSetRoot_of_quitNow_gain
      {0, 1} (by simp) 2 ε
    norm_num [quittingSetReward, reward]
    linarith
  · subst S
    apply not_isεAsymptoticNash_pureSetRoot_of_quitNow_gain
      {0, 2} (by simp) 1 ε
    norm_num [quittingSetReward, reward]
    linarith
  · subst S
    apply not_isεAsymptoticNash_pureSetRoot_of_never_gain
      {1, 2} (by simp) 1 (by simp) ε
    norm_num [quittingSetReward, reward]
    linarith
  · subst S
    apply not_isεAsymptoticNash_pureSetRoot_of_never_gain
      {0, 1, 2} (by simp) 0 (by simp) ε
    norm_num [quittingSetReward, reward]
    linarith

/-! ## Scope calibration: an exact mixed stationary repair -/

@[simp] theorem expect_hazardCoin
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (quittingHazardCoin p hp0 hp1) f =
      (1 - p) * f false + p * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

def halfCoin : PMF Bool :=
  quittingHazardCoin (1 / 2) (by norm_num) (by norm_num)

def quarterCoin : PMF Bool :=
  quittingHazardCoin (1 / 4) (by norm_num) (by norm_num)

/-- Player-zero quits with probability `1/2`, player one quits surely, and
player two quits with probability `1/4`. -/
def stationaryRepairRoot : Player → PMF Bool :=
  ![halfCoin, PMF.pure true, quarterCoin]

def stationaryRepairValue : Payoff Player := ![1, 3 / 4, 1 / 2]
def stationaryRepairContinueReward : Payoff Player := ![1, 1 / 4, 1 / 2]
def stationaryRepairOpponentContinueMass : Payoff Player := ![0, 3 / 8, 0]

theorem stationaryRepairRoot_hasSureQuitter :
    QuittingRootHasSureQuitter stationaryRepairRoot := by
  exact ⟨1, by simp [stationaryRepairRoot]⟩

@[simp] theorem stationaryRepairRoot_continueMass :
    quittingStationaryContinueMass stationaryRepairRoot = 0 := by
  change ((pmfPi stationaryRepairRoot)
    (fun _ : Player ↦ false)).toReal = 0
  rw [(quittingRootHasSureQuitter_iff_allContinue_mass_zero
    stationaryRepairRoot).mp stationaryRepairRoot_hasSureQuitter]
  simp

theorem stationaryRepairRoot_absorbingContribution (who : Player) :
    quittingRootAbsorbingContribution reward stationaryRepairRoot who =
      stationaryRepairValue who := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [stationaryRepairRoot, halfCoin, quarterCoin,
      expect_hazardCoin,
      quittingRootPayoff, stationaryRepairValue, reward] <;>
    norm_num

theorem stationaryRepairRoot_terminalPayoff (who : Player) :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward stationaryRepairRoot) who =
      stationaryRepairValue who := by
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
  · rw [stationaryRepairRoot_absorbingContribution,
      stationaryRepairRoot_continueMass]
    norm_num
  · rw [stationaryRepairRoot_continueMass]
    norm_num

theorem stationaryRepairRoot_fixedOpponentsQuitValue (who : Player) :
    quittingStationaryFixedOpponentsQuitValue reward
        stationaryRepairRoot who =
      stationaryRepairValue who := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [stationaryRepairRoot, halfCoin, quarterCoin,
      expect_hazardCoin, quittingRootPayoff,
      stationaryRepairValue, reward] ;
    norm_num

theorem stationaryRepairRoot_fixedOpponentsContinueReward
    (who : Player) :
    quittingStationaryFixedOpponentsContinueReward reward
        stationaryRepairRoot who =
      stationaryRepairContinueReward who := by
  unfold quittingStationaryFixedOpponentsContinueReward
    quittingFixedOpponentsContinueReward quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [stationaryRepairRoot, halfCoin, quarterCoin,
      expect_hazardCoin, quittingRootPayoff,
      stationaryRepairContinueReward, reward] <;>
    norm_num

theorem stationaryRepairRoot_fixedOpponentsContinueMass
    (who : Player) :
    quittingStationaryFixedOpponentsContinueMass
        stationaryRepairRoot who =
      stationaryRepairOpponentContinueMass who := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  rw [pmfPi_apply, Fin.prod_univ_three]
  fin_cases who <;>
    simp [stationaryRepairRoot, halfCoin, quarterCoin,
      stationaryRepairOpponentContinueMass,
      quittingAllContinueAction] ;
    norm_num

theorem stationaryRepairRoot_unilateralCap (who : Player) :
    quittingStationaryUnilateralCap reward stationaryRepairRoot who =
      stationaryRepairValue who := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [stationaryRepairRoot_fixedOpponentsQuitValue,
    stationaryRepairRoot_fixedOpponentsContinueReward,
    stationaryRepairRoot_fixedOpponentsContinueMass]
  fin_cases who <;>
    norm_num [stationaryRepairValue, stationaryRepairContinueReward,
      stationaryRepairOpponentContinueMass]

theorem stationaryRepairRoot_fixedOpponents_contracts (who : Player) :
    quittingStationaryFixedOpponentsContinueMass
        stationaryRepairRoot who < 1 := by
  rw [stationaryRepairRoot_fixedOpponentsContinueMass]
  fin_cases who <;>
    norm_num [stationaryRepairOpponentContinueMass]

/-- The mixed root is an exact terminal Nash equilibrium against arbitrary
behavioral unilateral deviations. -/
theorem stationaryRepairRoot_isNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward stationaryRepairRoot) := by
  apply isεAsymptoticNash_stationary_of_unilateralCap_le
  · exact stationaryRepairRoot_fixedOpponents_contracts
  · intro who
    rw [stationaryRepairRoot_unilateralCap,
      stationaryRepairRoot_terminalPayoff]
    norm_num

/-- Hence `(1,3/4,1/2)` is an exact stationary uniform-equilibrium payoff.
The counterexample separates the narrower static repair grammar; it does not
force a dynamic or memory-bearing architecture. -/
theorem stationaryRepairValue_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      stationaryRepairValue := by
  have huniform :=
    quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
      reward (quittingStationaryProfile reward stationaryRepairRoot)
      stationaryRepairRoot_isNash
  have hpayoff : quittingTerminalPayoff reward
      (quittingStationaryProfile reward stationaryRepairRoot) =
        stationaryRepairValue := by
    funext who
    exact stationaryRepairRoot_terminalPayoff who
  rw [hpayoff] at huniform
  exact huniform

end QuittingSureSetRepairFullIntervalCounterexample

end GameTheory
