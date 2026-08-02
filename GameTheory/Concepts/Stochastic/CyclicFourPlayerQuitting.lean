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
  if S.1 = {0} then ![1, -2, 2, 2]
  else if S.1 = {1} then ![2, 1, -2, 2]
  else if S.1 = {0, 1} then ![-1, 0, -1, 3]
  else if S.1 = {2} then ![2, 2, 1, -2]
  else if S.1 = {0, 2} then ![-1, -1, -1, -1]
  else if S.1 = {1, 2} then ![3, -1, 0, -1]
  else if S.1 = {0, 1, 2} then ![-4, -3, -3, 0]
  else if S.1 = {3} then ![-2, 2, 2, 1]
  else if S.1 = {0, 3} then ![0, -1, 3, -1]
  else if S.1 = {1, 3} then ![-1, -1, -1, -1]
  else if S.1 = {0, 1, 3} then ![-3, -3, 0, -4]
  else if S.1 = {2, 3} then ![-1, 3, -1, 0]
  else if S.1 = {0, 2, 3} then ![-3, 0, -4, -3]
  else if S.1 = {1, 2, 3} then ![0, -4, -3, -3]
  else ![-6, -6, -6, -6]

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

end CyclicFourPlayerQuitting
end GameTheory
