/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtSemantics
import UniformEquilibrium.Quitting.Debt.Dynamic.DebtAugmentedEdge

/-!
# Relaxed-trace stress test and one-row append repair

This is a small permanent regression for the audited three-player relaxed
trace witness.  Player `0` values exactly one quitter among players `0,1` at
`1`, values both at `-1`, and otherwise receives `0`; players `1,2` receive
zero everywhere.  The source row has quit rates `(0, 1/2, 0)`.  With the
zero-boundary prescribed recursion player `0` receives `1/2`, while the
finite deviation recursion receives player `0`'s singleton-or-Never terminal
boundary `1` and receives `1`, giving exact gain `1/2`.

Appending the row `(1,0,0)` makes the prescribed value of player `0` equal to
`1`; every player then has singleton-capped finite deviation gain zero.  The
statements use the finite terminal hazard and best-response recursions.  No
generic identification with unrestricted terminal-game exploitability is
claimed.
No neighborhood or compactness claim is made here.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

namespace RelaxedTraceStressTest

abbrev Player := Fin 3
abbrev Terminal := {S : Finset Player // S.Nonempty}

/-- The audited three-player reward table. -/
def reward (S : Terminal) : Payoff Player :=
  fun who =>
    if who = 0 then
      if 0 ∈ S.1 then
        if 1 ∈ S.1 then -1 else 1
      else if 1 ∈ S.1 then 1 else 0
    else 0

/-- The source row has quit rates `(0,1/2,0)`. -/
def sourceRoot : Player → PMF Bool := fun who =>
  ![PMF.pure false, PMF.uniformOfFintype Bool, PMF.pure false] who

/-- The exact append row `(1,0,0)`. -/
def appendRoot : Player → PMF Bool := fun who =>
  ![PMF.pure true, PMF.pure false, PMF.pure false] who

def allContinueRoot : Player → PMF Bool := fun _ => PMF.pure false

def sourceRoots : ℕ → Player → PMF Bool := fun time =>
  if time = 0 then sourceRoot else allContinueRoot

def repairedRoots : ℕ → Player → PMF Bool := fun time =>
  if time = 0 then sourceRoot else appendRoot

@[simp] theorem sourceRoot_update_zero_at_two (b : Bool) :
    Function.update sourceRoot 0 (PMF.pure b) 2 = PMF.pure false := by
  simp [Function.update, sourceRoot]

@[simp] theorem appendRoot_update_zero_at_two (b : Bool) :
    Function.update appendRoot 0 (PMF.pure b) 2 = PMF.pure false := by
  simp [Function.update, appendRoot]

/-- Prescribed finite value with the player's displayed root as hazard. -/
def prescribedValue (roots : ℕ → Player → PMF Bool)
    (who : Player) (fuel : ℕ) : ℝ :=
  quittingFiniteTerminalHazardValue reward roots who
    (fun time => roots time who) 0 0 fuel

/-- Finite all-behavior best-response value against fixed opponents. -/
def bestResponseValue (roots : ℕ → Player → PMF Bool)
    (who : Player) (fuel : ℕ) : ℝ :=
  quittingFiniteTerminalBestResponseValue reward roots who
    (quittingPositiveSingletonDebtCap reward who) 0 fuel

/-- Singleton-capped finite deviation/compiler gain. -/
def singletonCappedGain (roots : ℕ → Player → PMF Bool)
    (who : Player) (fuel : ℕ) : ℝ :=
  bestResponseValue roots who fuel - prescribedValue roots who fuel

@[simp] theorem positiveSingletonDebtCap_zero :
    quittingPositiveSingletonDebtCap reward 0 = 1 := by
  norm_num [quittingPositiveSingletonDebtCap, reward, quittingSingletonTerminal]

@[simp] theorem positiveSingletonDebtCap_one :
    quittingPositiveSingletonDebtCap reward 1 = 0 := by
  norm_num [quittingPositiveSingletonDebtCap, reward]

@[simp] theorem positiveSingletonDebtCap_two :
    quittingPositiveSingletonDebtCap reward 2 = 0 := by
  simp [quittingPositiveSingletonDebtCap, reward]

@[simp] theorem vector3_quitters_nonempty (a b c : Bool) :
    ({who | ![a, b, c] who = true} : Finset Player).Nonempty ↔
      a = true ∨ b = true ∨ c = true := by
  constructor
  · rintro ⟨who, hwho⟩
    fin_cases who <;> simp_all
  · rintro (ha | hb | hc)
    · exact ⟨0, by simp [ha]⟩
    · exact ⟨1, by simp [hb]⟩
    · exact ⟨2, by simp [hc]⟩

/-- Fubini expansion used to make the three-player rows transparent. -/
theorem expect_pmfPi_fin3_bool (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) (fun a =>
        expect (sigma 1) (fun b =>
          expect (sigma 2) (fun c => f ![a, b, c]))) := by
  classical
  have h0 : Function.update sigma 0 (sigma 0) = sigma :=
    Function.update_eq_self 0 sigma
  rw [← h0, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 0))
  funext a
  have h1 : Function.update (Function.update sigma 0 (PMF.pure a))
      1 (sigma 1) = Function.update sigma 0 (PMF.pure a) := by
    funext who
    fin_cases who <;> simp
  rw [← h1, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 1))
  funext b
  have h2 : Function.update
      (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
      2 (sigma 2) =
      Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b) := by
    funext who
    fin_cases who <;> simp
  rw [← h2, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 2))
  funext c
  have hpure : Function.update
      (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
      2 (PMF.pure c) = fun who => PMF.pure (![a, b, c] who) := by
    funext who
    fin_cases who <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

theorem source_quit_value_player_zero :
    quittingFixedOpponentsQuitValue reward sourceRoots 0 0 = 0 := by
  unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [show sourceRoots 0 = sourceRoot by rfl, expect_pmfPi_fin3_bool]
  norm_num [sourceRoot, reward, quittingRootPayoff, quittingQuitters,
    vector3_quitters_nonempty,
    PMF.uniformOfFintype_apply,
    expect_eq_sum, Fintype.sum_bool]

theorem source_continue_value_player_zero :
    quittingFixedOpponentsContinueReward reward sourceRoots 0 0 =
      (1 / 2 : ℝ) := by
  unfold quittingFixedOpponentsContinueReward quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [show sourceRoots 0 = sourceRoot by rfl, expect_pmfPi_fin3_bool]
  norm_num [sourceRoot, reward, quittingRootPayoff, quittingQuitters,
    vector3_quitters_nonempty,
    PMF.uniformOfFintype_apply,
    expect_eq_sum, Fintype.sum_bool]

theorem source_continue_mass_player_zero :
    quittingFixedOpponentsContinueMass sourceRoots 0 0 =
      (1 / 2 : ℝ) := by
  unfold quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  rw [show sourceRoots 0 = sourceRoot by rfl]
  rw [pmfPi_apply, ENNReal.toReal_prod]
  simp [sourceRoot,
    quittingAllContinueAction, Fin.prod_univ_succ]

theorem append_quit_value_player_zero :
    quittingFixedOpponentsQuitValue reward repairedRoots 0 1 = 1 := by
  unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [show repairedRoots 1 = appendRoot by rfl, expect_pmfPi_fin3_bool]
  simp [appendRoot, reward, quittingRootPayoff, quittingQuitters,
    vector3_quitters_nonempty, PMF.pure_apply, expect_eq_sum]

theorem append_continue_value_player_zero :
    quittingFixedOpponentsContinueReward reward repairedRoots 0 1 = 0 := by
  unfold quittingFixedOpponentsContinueReward quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [show repairedRoots 1 = appendRoot by rfl, expect_pmfPi_fin3_bool]
  simp [appendRoot, reward, quittingRootPayoff, quittingQuitters,
    vector3_quitters_nonempty, PMF.pure_apply, expect_eq_sum]

/- With player `0` forced to continue, both appended-row opponents continue
   surely; this is the fixed-opponents continuation mass, not player `0`'s
   own survival probability. -/
theorem append_continue_mass_player_zero :
    quittingFixedOpponentsContinueMass repairedRoots 0 1 = 1 := by
  unfold quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  rw [show repairedRoots 1 = appendRoot by rfl]
  rw [pmfPi_apply, ENNReal.toReal_prod]
  rw [Fin.prod_univ_three]
  simp [appendRoot, Function.update, quittingAllContinueAction,
    PMF.pure_apply]

theorem repaired_row_zero_quit_value_player_zero :
    quittingFixedOpponentsQuitValue reward repairedRoots 0 0 = 0 := by
  unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [show repairedRoots 0 = sourceRoot by rfl, expect_pmfPi_fin3_bool]
  norm_num [sourceRoot, reward, quittingRootPayoff, quittingQuitters,
    vector3_quitters_nonempty, PMF.uniformOfFintype_apply,
    expect_eq_sum, Fintype.sum_bool]

theorem repaired_row_zero_continue_value_player_zero :
    quittingFixedOpponentsContinueReward reward repairedRoots 0 0 =
      (1 / 2 : ℝ) := by
  unfold quittingFixedOpponentsContinueReward quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [show repairedRoots 0 = sourceRoot by rfl, expect_pmfPi_fin3_bool]
  norm_num [sourceRoot, reward, quittingRootPayoff, quittingQuitters,
    vector3_quitters_nonempty, PMF.uniformOfFintype_apply,
    expect_eq_sum, Fintype.sum_bool]

theorem repaired_row_zero_continue_mass_player_zero :
    quittingFixedOpponentsContinueMass repairedRoots 0 0 =
      (1 / 2 : ℝ) := by
  unfold quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  rw [show repairedRoots 0 = sourceRoot by rfl]
  rw [pmfPi_apply, ENNReal.toReal_prod]
  simp [sourceRoot, quittingAllContinueAction, Fin.prod_univ_succ]

theorem source_one_row_prescribed_player_zero :
    prescribedValue sourceRoots 0 1 = (1 / 2 : ℝ) := by
  unfold prescribedValue
  rw [quittingFiniteTerminalHazardValue]
  rw [source_quit_value_player_zero, source_continue_value_player_zero,
    source_continue_mass_player_zero]
  norm_num [sourceRoots, sourceRoot, PMF.uniformOfFintype_apply]

theorem source_one_row_best_response_player_zero :
    bestResponseValue sourceRoots 0 1 = 1 := by
  unfold bestResponseValue
  rw [quittingFiniteTerminalBestResponseValue]
  rw [source_quit_value_player_zero, source_continue_value_player_zero,
    source_continue_mass_player_zero]
  norm_num

/- The source row's exact player-`0` singleton-capped finite debt. -/
theorem source_one_row_gain_player_zero :
    singletonCappedGain sourceRoots 0 1 = (1 / 2 : ℝ) := by
  rw [singletonCappedGain, source_one_row_best_response_player_zero,
    source_one_row_prescribed_player_zero]
  norm_num

theorem repaired_two_row_prescribed_player_zero :
    prescribedValue repairedRoots 0 2 = 1 := by
  unfold prescribedValue
  rw [quittingFiniteTerminalHazardValue,
    quittingFiniteTerminalHazardValue]
  rw [repaired_row_zero_quit_value_player_zero,
    repaired_row_zero_continue_value_player_zero,
    repaired_row_zero_continue_mass_player_zero,
    append_quit_value_player_zero, append_continue_value_player_zero,
    append_continue_mass_player_zero]
  norm_num [repairedRoots, sourceRoot, appendRoot,
    PMF.uniformOfFintype_apply]

theorem repaired_two_row_best_response_player_zero :
    bestResponseValue repairedRoots 0 2 = 1 := by
  unfold bestResponseValue
  rw [quittingFiniteTerminalBestResponseValue,
    quittingFiniteTerminalBestResponseValue]
  rw [repaired_row_zero_quit_value_player_zero,
    repaired_row_zero_continue_value_player_zero,
    repaired_row_zero_continue_mass_player_zero,
    append_quit_value_player_zero, append_continue_value_player_zero,
    append_continue_mass_player_zero]
  norm_num [repairedRoots, sourceRoot, appendRoot,
    PMF.uniformOfFintype_apply]

theorem repaired_two_row_player_zero_gain :
    singletonCappedGain repairedRoots 0 2 = 0 := by
  rw [singletonCappedGain, repaired_two_row_best_response_player_zero,
    repaired_two_row_prescribed_player_zero]
  norm_num

theorem repaired_two_row_other_prescribed (who : Player) (hwho : who ≠ 0) :
    prescribedValue repairedRoots who 2 = 0 := by
  unfold prescribedValue
  rw [quittingFiniteTerminalHazardValue,
    quittingFiniteTerminalHazardValue]
  fin_cases who <;> simp_all [quittingFixedOpponentsQuitValue,
    quittingFixedOpponentsContinueReward, quittingFixedOpponentsContinueMass,
    quittingStationaryContinueMass, quittingRootAbsorbingContribution,
    quittingRootExpectedPayoff, quittingRootPayoff, quittingQuitters,
    repairedRoots, reward, expect_eq_sum]

theorem repaired_two_row_other_best_response (who : Player) (hwho : who ≠ 0) :
    bestResponseValue repairedRoots who 2 = 0 := by
  unfold bestResponseValue
  rw [quittingFiniteTerminalBestResponseValue,
    quittingFiniteTerminalBestResponseValue]
  fin_cases who <;> simp_all [quittingFixedOpponentsQuitValue,
    quittingFixedOpponentsContinueReward, quittingFixedOpponentsContinueMass,
    quittingStationaryContinueMass, quittingRootAbsorbingContribution,
    quittingRootExpectedPayoff, quittingRootPayoff, quittingQuitters,
    repairedRoots, reward, expect_eq_sum]

theorem repaired_two_row_other_gain (who : Player) (hwho : who ≠ 0) :
    singletonCappedGain repairedRoots who 2 = 0 := by
  rw [singletonCappedGain, repaired_two_row_other_best_response who hwho,
    repaired_two_row_other_prescribed who hwho]
  norm_num

/- Appending `(1,0,0)` produces zero singleton-capped finite deviation gain
   for every player in the two-row truncation. -/
theorem repaired_two_row_gain_zero (who : Player) :
    singletonCappedGain repairedRoots who 2 = 0 := by
  fin_cases who
  · exact repaired_two_row_player_zero_gain
  · exact repaired_two_row_other_gain 1 (by decide)
  · exact repaired_two_row_other_gain 2 (by decide)

end RelaxedTraceStressTest

end GameTheory
