/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingPureTimeExtremality
import GameTheory.Concepts.Stochastic.QuittingTerminalUniformization
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue

/-!
# An exact stationary equilibrium in a cyclic four-player quitting game

This file formalizes the positive certificate from Question 116.  The game
has the explicit fifteen-row terminal table below.  A common quit
probability is selected as the unique root of a rational polynomial in a
small rational interval; at that root, Quit and Continue have exactly the
same continuation value for every player.

The algebraic parameter is selected only after proving existence and
uniqueness.  No decimal approximation enters the construction.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace CyclicFourPlayerQuitting

open Filter Math.Probability Math.PMFProduct StochasticGame

/-- The four cyclic players. -/
abbrev Player := Fin 4

/-- A nonempty terminal quitter set. -/
abbrev Terminal := {S : Finset Player // S.Nonempty}

/-- The complete fifteen-row terminal table from Question 116. -/
def terminalReward (S : Terminal) : Payoff Player :=
  match decide (0 ∈ S.1), decide (1 ∈ S.1),
      decide (2 ∈ S.1), decide (3 ∈ S.1) with
  | true, false, false, false => ![1, -2, 2, 2]
  | false, true, false, false => ![2, 1, -2, 2]
  | true, true, false, false => ![-1, 0, -1, 3]
  | false, false, true, false => ![2, 2, 1, -2]
  | true, false, true, false => ![-1, -1, -1, -1]
  | false, true, true, false => ![3, -1, 0, -1]
  | true, true, true, false => ![-4, -3, -3, 0]
  | false, false, false, true => ![-2, 2, 2, 1]
  | true, false, false, true => ![0, -1, 3, -1]
  | false, true, false, true => ![-1, -1, -1, -1]
  | true, true, false, true => ![-3, -3, 0, -4]
  | false, false, true, true => ![-1, 3, -1, 0]
  | true, false, true, true => ![-3, 0, -4, -3]
  | false, true, true, true => ![0, -4, -3, -3]
  | true, true, true, true => ![-6, -6, -6, -6]
  | false, false, false, false => ![0, 0, 0, 0]

/-- The polynomial selecting the exact symmetric stationary root. -/
def stationaryPolynomial (x : ℝ) : ℝ :=
  x ^ 5 - 6 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 - 15 * x + 1

theorem stationaryPolynomial_one_fifteenth :
    stationaryPolynomial ((1 : ℝ) / 15) = 21736 / 759375 := by
  norm_num [stationaryPolynomial]

theorem stationaryPolynomial_seven_hundredths :
    stationaryPolynomial ((7 : ℝ) / 100) =
      -183413793 / 10000000000 := by
  norm_num [stationaryPolynomial]

/-- The derivative has the displayed polynomial form. -/
theorem deriv_stationaryPolynomial (x : ℝ) :
    deriv stationaryPolynomial x =
      5 * x ^ 4 - 24 * x ^ 3 + 21 * x ^ 2 + 12 * x - 15 := by
  change deriv (fun y : ℝ =>
    y ^ 5 - 6 * y ^ 4 + 7 * y ^ 3 + 6 * y ^ 2 - 15 * y + 1) x = _
  have h := (((((hasDerivAt_pow 5 x).sub
      ((hasDerivAt_pow 4 x).const_mul (6 : ℝ))).add
      ((hasDerivAt_pow 3 x).const_mul (7 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (6 : ℝ))).sub
      ((hasDerivAt_id x).const_mul (15 : ℝ))).add_const (1 : ℝ)
  convert h.deriv using 1
  all_goals norm_num
  all_goals ring

/-- The selecting polynomial is strictly decreasing on the interval needed
for the exact root certificate. -/
theorem stationaryPolynomial_strictAntiOn :
    StrictAntiOn stationaryPolynomial (Set.Icc (0 : ℝ) (1 / 10)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) (1 / 10))
    (by unfold stationaryPolynomial; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_stationaryPolynomial]
  have hx0 : 0 ≤ x := hx.1.le
  have hx1 : x ≤ (1 : ℝ) / 10 := hx.2.le
  have hx2nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hx2 : x ^ 2 ≤ ((1 : ℝ) / 10) ^ 2 := by
    nlinarith [sq_nonneg (x - (1 : ℝ) / 10)]
  have hx3nonneg : 0 ≤ x ^ 3 := by positivity
  have hx4 : x ^ 4 ≤ ((1 : ℝ) / 10) ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2 - ((1 : ℝ) / 10) ^ 2)]
  norm_num at hx2 hx4 ⊢
  nlinarith

/-- There is exactly one selected root in the rational interval
`(1/15, 7/100)`. -/
theorem existsUnique_stationaryParameter :
    ∃! s : ℝ,
      s ∈ Set.Ioo ((1 : ℝ) / 15) (7 / 100) ∧
        stationaryPolynomial s = 0 := by
  have hleftPos : 0 < stationaryPolynomial ((1 : ℝ) / 15) := by
    rw [stationaryPolynomial_one_fifteenth]
    norm_num
  have hrightNeg : stationaryPolynomial ((7 : ℝ) / 100) < 0 := by
    rw [stationaryPolynomial_seven_hundredths]
    norm_num
  have hcontinuous : ContinuousOn stationaryPolynomial
      (Set.Icc ((1 : ℝ) / 15) (7 / 100)) := by
    unfold stationaryPolynomial
    fun_prop
  obtain ⟨s, hsIcc, hsroot⟩ :=
    (convex_Icc ((1 : ℝ) / 15) (7 / 100)).isPreconnected.intermediate_value
      (Set.right_mem_Icc.mpr (by norm_num : (1 : ℝ) / 15 ≤ 7 / 100))
      (Set.left_mem_Icc.mpr (by norm_num : (1 : ℝ) / 15 ≤ 7 / 100))
      hcontinuous ⟨hrightNeg.le, hleftPos.le⟩
  have hs : s ∈ Set.Ioo ((1 : ℝ) / 15) (7 / 100) := by
    refine ⟨lt_of_le_of_ne hsIcc.1 ?_, lt_of_le_of_ne hsIcc.2 ?_⟩
    · intro heq
      subst s
      linarith
    · intro heq
      subst s
      linarith
  refine ⟨s, ⟨hs, hsroot⟩, ?_⟩
  intro y hy
  have hsLarge : s ∈ Set.Icc (0 : ℝ) (1 / 10) := by
    constructor <;> norm_num at hs ⊢ <;> linarith
  have hyLarge : y ∈ Set.Icc (0 : ℝ) (1 / 10) := by
    constructor <;> norm_num at hy ⊢ <;> linarith [hy.1.1, hy.1.2]
  exact (stationaryPolynomial_strictAntiOn.injOn hsLarge hyLarge
    (hsroot.trans hy.2.symm)).symm

/-- The exact symmetric quit probability. -/
def stationaryParameter : ℝ :=
  Classical.choose existsUnique_stationaryParameter

theorem stationaryParameter_mem :
    stationaryParameter ∈ Set.Ioo ((1 : ℝ) / 15) (7 / 100) :=
  (Classical.choose_spec existsUnique_stationaryParameter).1.1

theorem stationaryParameter_root :
    stationaryPolynomial stationaryParameter = 0 :=
  (Classical.choose_spec existsUnique_stationaryParameter).1.2

theorem stationaryParameter_pos : 0 < stationaryParameter := by
  have := stationaryParameter_mem.1
  norm_num at this ⊢
  linarith

theorem stationaryParameter_lt_one : stationaryParameter < 1 := by
  have := stationaryParameter_mem.2
  norm_num at this ⊢
  linarith

/-- The exact common continuation payoff. -/
def stationaryPayoff : ℝ :=
  1 - 5 * stationaryParameter - 3 * stationaryParameter ^ 2 +
    stationaryParameter ^ 3

theorem stationaryPayoff_gt_47_hundredths :
    (47 : ℝ) / 100 < stationaryPayoff := by
  have hs0 := stationaryParameter_pos.le
  have hs1 : stationaryParameter < (1 : ℝ) / 10 := by
    have := stationaryParameter_mem.2
    norm_num at this ⊢
    linarith
  unfold stationaryPayoff
  have hs2 : stationaryParameter ^ 2 < ((1 : ℝ) / 10) ^ 2 := by
    nlinarith [sq_nonneg (stationaryParameter - (1 : ℝ) / 10)]
  have hs3 : 0 ≤ stationaryParameter ^ 3 := by positivity
  norm_num at hs2 ⊢
  nlinarith

theorem stationaryPayoff_lt_one : stationaryPayoff < 1 := by
  have hs := stationaryParameter_pos
  have hslt : stationaryParameter < (1 : ℝ) / 10 := by
    have := stationaryParameter_mem.2
    norm_num at this ⊢
    linarith
  unfold stationaryPayoff
  have hfactor : 0 < 5 + 3 * stationaryParameter - stationaryParameter ^ 2 := by
    nlinarith [sq_nonneg (stationaryParameter - (1 : ℝ) / 10)]
  nlinarith

/-! ## The exact product root -/

/-- A Boolean law which quits with probability `p`. -/
def quitCoin (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  PMF.ofFintype
    (fun quit => if quit then ENNReal.ofReal p else ENNReal.ofReal (1 - p))
    (by
      rw [Fintype.sum_bool]
      simp only [if_true, if_false, Bool.false_eq_true]
      rw [← ENNReal.ofReal_add hp0 (by linarith)]
      norm_num)

@[simp] theorem quitCoin_apply_true_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (quitCoin p hp0 hp1 true).toReal = p := by
  simp [quitCoin, PMF.ofFintype_apply, ENNReal.toReal_ofReal hp0]

@[simp] theorem quitCoin_apply_false_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (quitCoin p hp0 hp1 false).toReal = 1 - p := by
  simp [quitCoin, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp1)]

@[simp] theorem expect_quitCoin
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (quitCoin p hp0 hp1) f = (1 - p) * f false + p * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

/-- Fubini expansion of a product of four Boolean mixed actions. -/
theorem expect_pmfPi_fin4_bool (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) fun a ↦
        expect (sigma 1) fun b ↦
          expect (sigma 2) fun c ↦
            expect (sigma 3) fun d ↦ f ![a, b, c, d] := by
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
  have h3 : Function.update
      (Function.update
        (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
        2 (PMF.pure c)) 3 (sigma 3) =
      Function.update
        (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
        2 (PMF.pure c) := by
    funext who
    fin_cases who <;> simp
  rw [← h3, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 3))
  funext d
  have hpure : Function.update
      (Function.update
        (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
        2 (PMF.pure c)) 3 (PMF.pure d) =
      fun who ↦ PMF.pure (![a, b, c, d] who) := by
    funext who
    fin_cases who <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

/-- A concrete four-coordinate Boolean action has a quitter exactly when one
of its four displayed coordinates is true. -/
@[simp] theorem vector4_quitters_nonempty (a b c d : Bool) :
    ({who | ![a, b, c, d] who = true} : Finset Player).Nonempty ↔
      a = true ∨ b = true ∨ c = true ∨ d = true := by
  constructor
  · rintro ⟨who, hwho⟩
    fin_cases who <;> simp_all
  · rintro (ha | hb | hc | hd)
    · exact ⟨0, by simp [ha]⟩
    · exact ⟨1, by simp [hb]⟩
    · exact ⟨2, by simp [hc]⟩
    · exact ⟨3, by simp [hd]⟩

/-- The symmetric product action at the selected algebraic parameter. -/
def stationaryRoot : Player → PMF Bool :=
  fun _ => quitCoin stationaryParameter stationaryParameter_pos.le
    stationaryParameter_lt_one.le

/-- The constant tail vector at the selected payoff. -/
def stationaryTail : Payoff Player := fun _ => stationaryPayoff

@[simp] theorem stationaryRoot_true_toReal (who : Player) :
    (stationaryRoot who true).toReal = stationaryParameter := by
  simp [stationaryRoot]

@[simp] theorem stationaryRoot_false_toReal (who : Player) :
    (stationaryRoot who false).toReal = 1 - stationaryParameter := by
  simp [stationaryRoot]

/-- Every player's pure-Quit value at the symmetric root is `ω`. -/
theorem stationaryRoot_quitPayoff (who : Player) :
    quittingRootQuitPayoff terminalReward stationaryTail stationaryRoot who =
      stationaryPayoff := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4_bool]
  fin_cases who <;>
    simp [stationaryRoot, stationaryTail, quittingRootPayoff,
      quittingQuitters, terminalReward, stationaryPayoff] <;>
    ring

/-- The unconditional absorbing contribution when a player continues. -/
theorem stationaryRoot_continueReward (who : Player) :
    quittingRootAbsorbingContribution terminalReward
        (Function.update stationaryRoot who (PMF.pure false)) who =
      2 * stationaryParameter - 3 * stationaryParameter ^ 2 +
        stationaryParameter ^ 3 := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4_bool]
  fin_cases who <;>
    simp [stationaryRoot, quittingRootPayoff, quittingQuitters,
      terminalReward] <;>
    ring

/-- The three opponents all continue with probability `(1-s)^3`. -/
theorem stationaryRoot_opponentContinueMass (who : Player) :
    quittingStationaryContinueMass
        (Function.update stationaryRoot who (PMF.pure false)) =
      (1 - stationaryParameter) ^ 3 := by
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  fin_cases who <;>
    simp [stationaryRoot, quittingAllContinueAction, Fin.prod_univ_succ] <;>
    ring

/-- The selected polynomial root is exactly the stationary continuation
balance identity. -/
theorem stationary_continue_balance :
    2 * stationaryParameter - 3 * stationaryParameter ^ 2 +
          stationaryParameter ^ 3 +
        (1 - stationaryParameter) ^ 3 * stationaryPayoff =
      stationaryPayoff := by
  apply sub_eq_zero.mp
  calc
    (2 * stationaryParameter - 3 * stationaryParameter ^ 2 +
          stationaryParameter ^ 3 +
        (1 - stationaryParameter) ^ 3 * stationaryPayoff) -
          stationaryPayoff =
        -stationaryParameter * stationaryPolynomial stationaryParameter := by
          unfold stationaryPayoff stationaryPolynomial
          ring
    _ = 0 := by rw [stationaryParameter_root, mul_zero]

/-- Every player's pure-Continue value at the symmetric root is also `ω`. -/
theorem stationaryRoot_continuePayoff (who : Player) :
    quittingRootContinuePayoff terminalReward stationaryTail stationaryRoot who =
      stationaryPayoff := by
  unfold quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    stationaryRoot_continueReward, stationaryRoot_opponentContinueMass]
  exact stationary_continue_balance

/-- The stationary product root is exactly indifferent for every player. -/
theorem stationaryRoot_endpointDifference (who : Player) :
    quittingRootEndpointDifference terminalReward stationaryTail
        stationaryRoot who = 0 := by
  rw [quittingRootEndpointDifference, stationaryRoot_quitPayoff,
    stationaryRoot_continuePayoff, sub_self]

/-- The selected root has current payoff equal to its declared tail. -/
theorem stationaryRoot_fixedPoint (who : Player) :
    quittingRootSuccessorPayoff terminalReward stationaryTail stationaryRoot who =
      stationaryPayoff := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    stationaryRoot_quitPayoff, stationaryRoot_continuePayoff]
  have hsum := quittingRoot_continueProbability_add_quitProbability
    stationaryRoot who
  rw [← add_mul, add_comm, hsum, one_mul]

end CyclicFourPlayerQuitting
end GameTheory
