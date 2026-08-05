/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCutoffOneSafety
import GameTheory.Concepts.Stochastic.QuittingPositiveDynamicDebtProvenance

/-!
# A three-player obstruction to sure-set owner repair

This file isolates the first genuinely multi-player gap in the
positive-debt repair program.  At the uniform three-player zero-tail root,
player zero has positive exact cutoff-one debt.  Its positive terminal
packet is carried by the full opponent set `{1, 2}`, and every positive
owner-solo rate has a joining obstruction.  Nevertheless no nonempty sure
quitting set satisfies all zero-hazard limiting credibility inequalities:
the singleton sets fail the owner's inequality, while `{1, 2}` has an
internal leaver.

This is only a counterexample to the implication

`positive packet + universal owner-solo obstruction -> sure-set repair`.

It does not establish a positive optimized debt plateau, exclude other
stationary or nonstationary repairs, or give a global nonexistence theorem.
In fact, the sure coalition `{0,1}` is an exact direct First certificate;
this is proved explicitly below.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

namespace QuittingSureSetRepairCounterexample

abbrev Player := Fin 3
abbrev Terminal := {S : Finset Player // S.Nonempty}

@[simp] theorem player_zero_ne_one : (0 : Player) ≠ 1 := by decide
@[simp] theorem player_zero_ne_two : (0 : Player) ≠ 2 := by decide
@[simp] theorem player_one_ne_zero : (1 : Player) ≠ 0 := by decide
@[simp] theorem player_one_ne_two : (1 : Player) ≠ 2 := by decide
@[simp] theorem player_two_ne_zero : (2 : Player) ≠ 0 := by decide
@[simp] theorem player_two_ne_one : (2 : Player) ≠ 1 := by decide

/-- The seven terminal payoff vectors, in player order `0,1,2`. -/
def reward (S : Terminal) : Payoff Player :=
  fun who ↦
    if who = 0 then
      if 0 ∈ S.1 then 1 else if 1 ∈ S.1 ∧ 2 ∈ S.1 then 4 else 0
    else if who = 1 then
      if (2 ∈ S.1 ∧ 0 ∉ S.1 ∧ 1 ∉ S.1) ∨
          (0 ∈ S.1 ∧ 1 ∈ S.1 ∧ 2 ∉ S.1) then 1 else 0
    else 0

@[simp] theorem reward_0 (h : ({0} : Finset Player).Nonempty) :
    reward ⟨{0}, h⟩ = ![1, 0, 0] := by
  funext who
  fin_cases who <;> simp [reward]

@[simp] theorem reward_1 (h : ({1} : Finset Player).Nonempty) :
    reward ⟨{1}, h⟩ = ![0, 0, 0] := by
  funext who
  fin_cases who <;> simp [reward]

@[simp] theorem reward_2 (h : ({2} : Finset Player).Nonempty) :
    reward ⟨{2}, h⟩ = ![0, 1, 0] := by
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
    reward ⟨{0, 1, 2}, h⟩ = ![1, 0, 0] := by
  funext who
  fin_cases who <;> simp [reward]

/-- Every player independently Quits with probability one half. -/
def root : Player → PMF Bool := fun _ => PMF.uniformOfFintype Bool

/-- The exact zero-tail root payoff. -/
def value : Payoff Player := ![1, 1 / 4, 0]

/-- The positive-boundary Continue endpoint. -/
def positiveContinueValue : Payoff Player := ![5 / 4, 1 / 4, 0]

/-- Fubini expansion of a product of three Boolean marginals. -/
theorem expect_pmfPi_fin3_bool (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) fun a ↦
        expect (sigma 1) fun b ↦
          expect (sigma 2) fun c ↦ f ![a, b, c] := by
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
      2 (PMF.pure c) = fun who ↦ PMF.pure (![a, b, c] who) := by
    funext who
    fin_cases who <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

@[simp] theorem expect_uniform_bool (f : Bool → ℝ) :
    expect (PMF.uniformOfFintype Bool) f = (f false + f true) / 2 := by
  rw [expect_eq_sum, Fintype.sum_bool]
  norm_num [PMF.uniformOfFintype_apply]
  ring

@[simp] theorem quitters_vector (a b c : Bool) :
    quittingQuitters (![a, b, c] : Player → Bool) =
      (if a then {0} else ∅) ∪ (if b then {1} else ∅) ∪
        (if c then {2} else ∅) := by
  ext who
  fin_cases who <;> cases a <;> cases b <;> cases c <;>
    simp [quittingQuitters]

/-! ## Exact root and exact dynamic debt -/

theorem quitPayoff_eq_value (who : Player) :
    quittingRootQuitPayoff reward (0 : Payoff Player) root who = value who := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [root, quittingRootPayoff, reward, quitters_vector, value]
  all_goals norm_num

theorem continuePayoff_eq_value (who : Player) :
    quittingRootContinuePayoff reward (0 : Payoff Player) root who = value who := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [root, quittingRootPayoff, reward, quitters_vector, value] <;>
      norm_num

/-- Every player is exactly indifferent between its two endpoints. -/
theorem root_isEndpointNash_zero :
    IsεQuittingRootEndpointNash reward (0 : Payoff Player) 0 root := by
  intro who
  rw [quittingRootEndpointDifference, quitPayoff_eq_value,
    continuePayoff_eq_value]
  norm_num

/-- The uniform root is an exact Nash root of the zero-tail stage game. -/
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
  simp [quittingPositiveSingletonDebtCap, reward]

theorem positiveContinuePayoff_eq (who : Player) :
    quittingCutoffOnePositiveContinuePayoff reward root who =
      positiveContinueValue who := by
  unfold quittingCutoffOnePositiveContinuePayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [root, quittingRootPayoff, reward, quitters_vector,
      positiveContinueValue] <;> norm_num

/-- The exact cutoff-one dynamic debt is `(1/4,0,0)`. -/
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

/-! ## The full-set packet and universal solo obstruction -/

/-- The marked action has the owner Continue and both opponents Quit. -/
def markedAction : Player → Bool := ![false, true, true]

theorem markedAction_mass :
    ((pmfPi (Function.update root 0 (PMF.pure false))) markedAction).toReal =
      1 / 4 := by
  rw [pmfPi_apply]
  rw [Fin.prod_univ_three]
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

/-- Every positive owner-solo rate is obstructed by player one. -/
theorem universal_ownerSolo_obstruction :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      QuittingSoloJoiningObstruction reward 0 p := by
  intro p hp _
  refine ⟨1, by decide, ?_⟩
  simpa [quittingSoloReward, quittingSingletonCollisionReward] using hp

/-! ## No credible sure-set/small-owner limit -/

/-- Extend the terminal table by zero at the empty set for limiting
one-stage comparisons. -/
def boundaryReward (S : Finset Player) (who : Player) : ℝ :=
  if h : S.Nonempty then reward ⟨S, h⟩ who else 0

/-- Necessary zero-hazard inequalities for a stationary repair in which
player zero uses a small positive hazard, every member of `T` Quits surely,
and every other player Continues.  The singleton member has the exceptional
Never value `r_j({0})`; a member of a larger set compares with leaving `T`;
outsiders compare with joining `T`. -/
def SureSetSmallOwnerLimitCertificate (T : Finset Player) : Prop :=
  T.Nonempty ∧ 0 ∉ T ∧
  boundaryReward (insert 0 T) 0 ≤ boundaryReward T 0 ∧
  (∀ j ∈ T,
    (T = {j} → boundaryReward {0} j ≤ boundaryReward {j} j) ∧
    (T ≠ {j} →
      boundaryReward (T.erase j) j ≤ boundaryReward T j)) ∧
  (∀ outsider, outsider ≠ 0 → outsider ∉ T →
    boundaryReward (insert outsider T) outsider ≤
      boundaryReward T outsider)

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

/-- No nonempty sure-quitting set satisfies the limiting credibility
conditions for a vanishing-hazard owner-zero repair. -/
theorem no_sureSetSmallOwnerLimitCertificate :
    ¬ ∃ T : Finset Player, SureSetSmallOwnerLimitCertificate T := by
  rintro ⟨T, hT⟩
  rcases hT with ⟨hne, hzero, howner, hinternal, _⟩
  rcases nonempty_without_zero_cases T hne hzero with hT | hT | hT
  · subst T
    norm_num [boundaryReward, reward] at howner
  · subst T
    norm_num [boundaryReward, reward] at howner
  · subst T
    have hleaver := (hinternal 1 (by simp)).2 (by decide)
    norm_num [boundaryReward, reward] at hleaver

/-! ## Scope calibration: a direct First repair exists -/

/-- Players zero and one Quit surely; player two Continues. -/
def firstRoot : Player → PMF Bool :=
  fun who ↦ PMF.pure (![true, true, false] who)

/-- The direct First payoff `(1,1,0)`. -/
def firstValue : Payoff Player := ![1, 1, 0]

theorem firstRoot_quitPayoff (who : Player) :
    quittingRootQuitPayoff reward (0 : Payoff Player) firstRoot who =
      firstValue who := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [firstRoot, quittingRootPayoff, reward, quitters_vector,
      firstValue]

theorem firstRoot_continuePayoff (who : Player) :
    quittingRootContinuePayoff reward (0 : Payoff Player) firstRoot who = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [firstRoot, quittingRootPayoff, reward, quitters_vector]

theorem firstRoot_isEndpointNash_zero :
    IsεQuittingRootEndpointNash reward (0 : Payoff Player) 0 firstRoot := by
  intro who
  rw [quittingRootEndpointDifference, firstRoot_quitPayoff,
    firstRoot_continuePayoff]
  fin_cases who <;> norm_num [firstRoot, firstValue]

theorem firstRoot_isNash_zero :
    IsεQuittingRootNash reward (0 : Payoff Player) 0 firstRoot := by
  exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward (0 : Payoff Player) firstRoot).1 firstRoot_isEndpointNash_zero

theorem firstRoot_successor_zero :
    quittingRootSuccessorPayoff reward (0 : Payoff Player) firstRoot =
      firstValue := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix, firstRoot_quitPayoff,
    firstRoot_continuePayoff]
  fin_cases who <;> norm_num [firstRoot, firstValue]

theorem firstRoot_positiveContinuePayoff (who : Player) :
    quittingCutoffOnePositiveContinuePayoff reward firstRoot who = 0 := by
  unfold quittingCutoffOnePositiveContinuePayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases who <;>
    simp [firstRoot, quittingRootPayoff, reward, quitters_vector]

/-- The `{0,1}` direct First profile is an exact terminal equilibrium. -/
theorem firstProfile_isZeroAsymptoticNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingInfinitePathProfile reward
        (quittingCutoffOneRoots firstRoot)) := by
  apply cutoffOneProfile_isZeroAsymptoticNash_of_safe
    reward firstRoot firstRoot_isNash_zero
  intro who
  rw [firstRoot_positiveContinuePayoff]
  have hvalue := congrFun firstRoot_successor_zero who
  rw [hvalue]
  fin_cases who <;> norm_num [firstValue]

/-- Consequently the table does have a uniform-equilibrium payoff; the
regression only rejects the vanishing-owner sure-opponent repair rung. -/
theorem firstValue_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none firstValue := by
  have huniform := quittingGame_isUniformEquilibriumPayoff_of_cutoffOneSafeRoot
    reward firstRoot firstRoot_isNash_zero (fun who ↦ by
      rw [firstRoot_positiveContinuePayoff]
      have hvalue := congrFun firstRoot_successor_zero who
      rw [hvalue]
      fin_cases who <;> norm_num [firstValue])
  rwa [firstRoot_successor_zero] at huniform

end QuittingSureSetRepairCounterexample

end GameTheory
