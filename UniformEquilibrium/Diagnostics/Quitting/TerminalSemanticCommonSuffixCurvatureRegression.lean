/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawTransferBalanceRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn

/-!
# A common live suffix does not turn flat debt height into a Nash return

This file realizes the elementary curvature obstruction inside a literal
three-player quitting game.  Player `2` quits surely at the displayed root,
so every profile below absorbs immediately.  The continuation after that
root is nevertheless fixed literally, not merely semantically.

For root Quit probabilities `x` and `y` of players `0` and `1`, player `0`
is paid only by the joint event `{0,1}`, while player `1` is paid only when
the sure quitter exits without either of them.  Their full behavioral debts
are both `(1-x)y`.  Player `2` has constant debt one.  Hence the positive
minimum of total debt on this common-suffix root face is `1`, attained when
`x = 1` or `y = 0`.

Along `x = 1-lambda`, `y = lambda`, the debt height above that face is
`2 lambda^2`, but both active best-response coordinates equal `lambda`.
Every point of the exact minimum face has at least one of those two envelope
coordinates equal to zero.  Thus its envelope distance from the curved
profile is at least `lambda`, despite the literal common continuation.

This is a face-level regression, not a counterexample to global strategic
reprojection.  A reprojected profile may change the root face or introduce a
different chronology.  What is ruled out is the inference from debt height
and common suffix alone to a same-face Nash return at the reset scale.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

namespace QuittingCommonSuffixCurvatureRegression

abbrev Player := Fin 3

abbrev left : Player := 0
abbrev right : Player := 1
abbrev anchor : Player := 2

/-- The active players carry the two complementary one-stage rewards.  The
anchor receives `-1` whenever it quits and zero otherwise. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who =>
    if who = left then
      if left ∈ terminal.val ∧ right ∈ terminal.val then 1 else 0
    else if who = right then
      if left ∉ terminal.val ∧ right ∉ terminal.val then 1 else 0
    else if anchor ∈ terminal.val then -1 else 0

theorem abs_reward_le_one
    (terminal : {S : Finset Player // S.Nonempty}) (who : Player) :
    |reward terminal who| ≤ 1 := by
  unfold reward
  split_ifs <;> norm_num

/-- Root face with an always-quitting anchor and two free hazards. -/
def root (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Player → PMF Bool := fun who =>
  if who = left then quittingHazardCoin x hx0 hx1
  else if who = right then quittingHazardCoin y hy0 hy1
  else PMF.pure true

/-- The common post-root continuation is all-Continue forever. -/
def continuation : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot ∅)

/-- One root from the face, followed by the literal common continuation. -/
def profile (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward
    (root x y hx0 hx1 hy0 hy1) continuation

/-- All profiles on the face have exactly the same live roots after their
displayed root. -/
theorem profile_common_live_suffix
    (x y x' y' : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hx0' : 0 ≤ x') (hx1' : x' ≤ 1)
    (hy0' : 0 ≤ y') (hy1' : y' ≤ 1) (time : ℕ) :
    quittingProfileLiveRoot reward (profile x y hx0 hx1 hy0 hy1)
        (time + 1) =
      quittingProfileLiveRoot reward (profile x' y' hx0' hx1' hy0' hy1')
        (time + 1) := by
  rfl

/-! ## Explicit product-root calculations -/

/-- Three-coordinate Fubini expansion for Boolean product roots. -/
theorem expect_pmfPi_fin3 (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma left) (fun a =>
        expect (sigma right) (fun b =>
          expect (sigma anchor) (fun c => f ![a, b, c]))) := by
  classical
  have hleft : Function.update sigma left (sigma left) = sigma :=
    Function.update_eq_self left sigma
  rw [← hleft, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma left))
  funext a
  have hright : Function.update (Function.update sigma left (PMF.pure a))
      right (sigma right) = Function.update sigma left (PMF.pure a) := by
    funext who
    fin_cases who <;> simp [left, right]
  rw [← hright, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma right))
  funext b
  have hanchor : Function.update
      (Function.update (Function.update sigma left (PMF.pure a))
        right (PMF.pure b)) anchor (sigma anchor) =
      Function.update (Function.update sigma left (PMF.pure a))
        right (PMF.pure b) := by
    funext who
    fin_cases who <;> simp [left, right, anchor]
  rw [← hanchor, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma anchor))
  funext c
  have hpure : Function.update
      (Function.update (Function.update sigma left (PMF.pure a))
        right (PMF.pure b)) anchor (PMF.pure c) =
      fun who => PMF.pure (![a, b, c] who) := by
    funext who
    fin_cases who <;> simp [left, right, anchor]
  rw [hpure, pmfPi_pure, expect_pure]

@[simp] theorem quittingQuitters_vec3 (a b c : Bool) :
    quittingQuitters ![a, b, c] =
      (if a then {left} else ∅) ∪
        (if b then {right} else ∅) ∪
          (if c then {anchor} else ∅) := by
  ext who
  fin_cases who <;> cases a <;> cases b <;> cases c <;>
    simp [quittingQuitters, left, right, anchor]

@[simp] theorem root_left_true
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ((root x y hx0 hx1 hy0 hy1 left) true).toReal = x := by
  simp [root, left]

@[simp] theorem root_left_false
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ((root x y hx0 hx1 hy0 hy1 left) false).toReal = 1 - x := by
  simp [root, left]

@[simp] theorem root_right_true
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ((root x y hx0 hx1 hy0 hy1 right) true).toReal = y := by
  simp [root, left, right]

@[simp] theorem root_right_false
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ((root x y hx0 hx1 hy0 hy1 right) false).toReal = 1 - y := by
  simp [root, left, right]

@[simp] theorem root_anchor_true
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ((root x y hx0 hx1 hy0 hy1 anchor) true).toReal = 1 := by
  simp [root, left, right, anchor]

@[simp] theorem root_anchor_false
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ((root x y hx0 hx1 hy0 hy1 anchor) false).toReal = 0 := by
  simp [root, left, right, anchor]

/-! ## Exact payoff and envelope data -/

@[simp] theorem continuation_payoff (who : Player) :
    quittingTerminalPayoff reward continuation who = 0 := by
  unfold continuation
  rw [quittingTerminalPayoff_pureSetRoot]
  simp

@[simp] theorem continuation_envelope (who : Player) :
    quittingContinuationBestResponseValue reward continuation who = 0 := by
  unfold continuation
  rw [quittingContinuationBestResponseValue_pureSetRoot_eq
    reward ∅ who (by norm_num) abs_reward_le_one]
  fin_cases who <;>
    norm_num [quittingSetReward, reward, left, right, anchor, Fin.ext_iff]

theorem root_quitPayoff_left
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingRootQuitPayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) left = y := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, left, right, anchor,
    expect_eq_sum]

theorem root_continuePayoff_left
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingRootContinuePayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) left = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, left, right, anchor,
    expect_eq_sum]

theorem root_quitPayoff_right
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingRootQuitPayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) right = 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, left, right, anchor,
    expect_eq_sum]

theorem root_continuePayoff_right
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingRootContinuePayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) right = 1 - x := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, left, right, anchor,
    expect_eq_sum]

theorem root_quitPayoff_anchor
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingRootQuitPayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) anchor = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, left, right, anchor,
    expect_eq_sum]

theorem root_continuePayoff_anchor
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingRootContinuePayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) anchor = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, left, right, anchor,
    expect_eq_sum]

theorem root_successorPayoff_left
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingRootSuccessorPayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) left = x * y := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    root_quitPayoff_left, root_continuePayoff_left]
  simp

theorem root_successorPayoff_right
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingRootSuccessorPayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) right = (1 - x) * (1 - y) := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    root_quitPayoff_right, root_continuePayoff_right]
  simp
  ring

theorem root_successorPayoff_anchor
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingRootSuccessorPayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) anchor = -1 := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    root_quitPayoff_anchor, root_continuePayoff_anchor]
  simp

theorem profile_payoff_left
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingTerminalPayoff reward (profile x y hx0 hx1 hy0 hy1) left =
      x * y := by
  unfold profile
  rw [quittingTerminalPayoff_rootThenContinuation_eq]
  change quittingRootSuccessorPayoff reward
      (fun who => quittingTerminalPayoff reward continuation who)
      (root x y hx0 hx1 hy0 hy1) left = _
  simp only [continuation_payoff]
  exact root_successorPayoff_left x y hx0 hx1 hy0 hy1

theorem profile_payoff_right
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingTerminalPayoff reward (profile x y hx0 hx1 hy0 hy1) right =
      (1 - x) * (1 - y) := by
  unfold profile
  rw [quittingTerminalPayoff_rootThenContinuation_eq]
  change quittingRootSuccessorPayoff reward
      (fun who => quittingTerminalPayoff reward continuation who)
      (root x y hx0 hx1 hy0 hy1) right = _
  simp only [continuation_payoff]
  exact root_successorPayoff_right x y hx0 hx1 hy0 hy1

theorem profile_payoff_anchor
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingTerminalPayoff reward (profile x y hx0 hx1 hy0 hy1) anchor =
      -1 := by
  unfold profile
  rw [quittingTerminalPayoff_rootThenContinuation_eq]
  change quittingRootSuccessorPayoff reward
      (fun who => quittingTerminalPayoff reward continuation who)
      (root x y hx0 hx1 hy0 hy1) anchor = _
  simp only [continuation_payoff]
  exact root_successorPayoff_anchor x y hx0 hx1 hy0 hy1

theorem profile_envelope_left
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingContinuationBestResponseValue reward
        (profile x y hx0 hx1 hy0 hy1) left = y := by
  unfold profile
  rw [quittingContinuationBestResponseValue_rootThenContinuation_eq_max
    reward (root x y hx0 hx1 hy0 hy1) continuation left
      (by norm_num) abs_reward_le_one]
  simp only [continuation_payoff, continuation_envelope]
  rw [Function.update_eq_self]
  change max
    (quittingRootQuitPayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) left)
    (quittingRootContinuePayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) left) = y
  rw [root_quitPayoff_left, root_continuePayoff_left, max_eq_left hy0]

theorem profile_envelope_right
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingContinuationBestResponseValue reward
        (profile x y hx0 hx1 hy0 hy1) right = 1 - x := by
  unfold profile
  rw [quittingContinuationBestResponseValue_rootThenContinuation_eq_max
    reward (root x y hx0 hx1 hy0 hy1) continuation right
      (by norm_num) abs_reward_le_one]
  simp only [continuation_payoff, continuation_envelope]
  rw [Function.update_eq_self]
  change max
    (quittingRootQuitPayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) right)
    (quittingRootContinuePayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) right) = 1 - x
  rw [root_quitPayoff_right, root_continuePayoff_right,
    max_eq_right (sub_nonneg.mpr hx1)]

theorem profile_envelope_anchor
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingContinuationBestResponseValue reward
        (profile x y hx0 hx1 hy0 hy1) anchor = 0 := by
  unfold profile
  rw [quittingContinuationBestResponseValue_rootThenContinuation_eq_max
    reward (root x y hx0 hx1 hy0 hy1) continuation anchor
      (by norm_num) abs_reward_le_one]
  simp only [continuation_payoff, continuation_envelope]
  rw [Function.update_eq_self]
  change max
    (quittingRootQuitPayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) anchor)
    (quittingRootContinuePayoff reward (0 : Payoff Player)
      (root x y hx0 hx1 hy0 hy1) anchor) = 0
  rw [root_quitPayoff_anchor, root_continuePayoff_anchor]
  norm_num

theorem profile_debt_left
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (profile x y hx0 hx1 hy0 hy1)) left =
      (1 - x) * y := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change quittingContinuationBestResponseValue reward
      (profile x y hx0 hx1 hy0 hy1) left -
    quittingTerminalPayoff reward (profile x y hx0 hx1 hy0 hy1) left = _
  rw [profile_envelope_left, profile_payoff_left]
  ring

theorem profile_debt_right
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (profile x y hx0 hx1 hy0 hy1)) right =
      (1 - x) * y := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change quittingContinuationBestResponseValue reward
      (profile x y hx0 hx1 hy0 hy1) right -
    quittingTerminalPayoff reward (profile x y hx0 hx1 hy0 hy1) right = _
  rw [profile_envelope_right, profile_payoff_right]
  ring

theorem profile_debt_anchor
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (profile x y hx0 hx1 hy0 hy1)) anchor = 1 := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change quittingContinuationBestResponseValue reward
      (profile x y hx0 hx1 hy0 hy1) anchor -
    quittingTerminalPayoff reward (profile x y hx0 hx1 hy0 hy1) anchor = _
  rw [profile_envelope_anchor, profile_payoff_anchor]
  norm_num

/-- Total semantic debt on the common-suffix root face. -/
theorem profile_debtSum
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (profile x y hx0 hx1 hy0 hy1)) =
      1 + 2 * ((1 - x) * y) := by
  unfold quittingTerminalSemanticDebtSum
  rw [Fin.sum_univ_three]
  change
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (profile x y hx0 hx1 hy0 hy1)) left +
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (profile x y hx0 hx1 hy0 hy1)) right +
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (profile x y hx0 hx1 hy0 hy1)) anchor = _
  rw [profile_debt_left, profile_debt_right, profile_debt_anchor]
  ring

/-- The face has positive minimum debt one. -/
theorem one_le_profile_debtSum
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 ≤ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (profile x y hx0 hx1 hy0 hy1)) := by
  rw [profile_debtSum]
  have hproduct : 0 ≤ (1 - x) * y :=
    mul_nonneg (sub_nonneg.mpr hx1) hy0
  linarith

/-- Exact minimum roots on this face lie on the union of the two coordinate
faces `x = 1` and `y = 0`. -/
theorem profile_debtSum_eq_one_iff
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (profile x y hx0 hx1 hy0 hy1)) = 1 ↔
      x = 1 ∨ y = 0 := by
  rw [profile_debtSum]
  constructor
  · intro h
    have hproduct : (1 - x) * y = 0 := by linarith
    rcases mul_eq_zero.mp hproduct with hx | hy
    · exact Or.inl (by linarith)
    · exact Or.inr hy
  · rintro (rfl | rfl) <;> ring

/-! ## Quadratic height versus linear same-face displacement -/

/-- The curved root has total debt `1 + 2 lambda^2`. -/
theorem curved_profile_debtSum
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (profile (1 - lambda) lambda
            (sub_nonneg.mpr hlambda1) (by linarith)
            hlambda0 hlambda1)) =
      1 + 2 * lambda ^ 2 := by
  rw [profile_debtSum]
  ring

/-- Both active envelope coordinates of the curved root equal the reset
scale. -/
theorem curved_profile_active_envelopes
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    let curved := profile (1 - lambda) lambda
      (sub_nonneg.mpr hlambda1) (by linarith) hlambda0 hlambda1
    (quittingTerminalSemanticPair reward curved).2 left = lambda ∧
      (quittingTerminalSemanticPair reward curved).2 right = lambda := by
  dsimp only
  constructor
  · change quittingContinuationBestResponseValue reward
      (profile (1 - lambda) lambda
        (sub_nonneg.mpr hlambda1) (by linarith) hlambda0 hlambda1) left =
        lambda
    exact profile_envelope_left _ _ _ _ _ _
  · change quittingContinuationBestResponseValue reward
      (profile (1 - lambda) lambda
        (sub_nonneg.mpr hlambda1) (by linarith) hlambda0 hlambda1) right =
        lambda
    simpa using profile_envelope_right (1 - lambda) lambda
      (sub_nonneg.mpr hlambda1) (by linarith) hlambda0 hlambda1

/-- **Linear separation from the exact minimum face.**  Every same-suffix
root on the exact face differs from the curved root by at least `lambda` in
one of the two active envelope coordinates. -/
theorem lambda_le_activeEnvelopeDistance_of_faceMinimum
    (lambda x y : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hminimum : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (profile x y hx0 hx1 hy0 hy1)) = 1) :
    let curved := profile (1 - lambda) lambda
      (sub_nonneg.mpr hlambda1) (by linarith) hlambda0 hlambda1
    let returned := profile x y hx0 hx1 hy0 hy1
    lambda ≤ max
      |(quittingTerminalSemanticPair reward curved).2 left -
        (quittingTerminalSemanticPair reward returned).2 left|
      |(quittingTerminalSemanticPair reward curved).2 right -
        (quittingTerminalSemanticPair reward returned).2 right| := by
  dsimp only
  change lambda ≤ max
    |quittingContinuationBestResponseValue reward
        (profile (1 - lambda) lambda
          (sub_nonneg.mpr hlambda1) (by linarith) hlambda0 hlambda1) left -
      quittingContinuationBestResponseValue reward
        (profile x y hx0 hx1 hy0 hy1) left|
    |quittingContinuationBestResponseValue reward
        (profile (1 - lambda) lambda
          (sub_nonneg.mpr hlambda1) (by linarith) hlambda0 hlambda1) right -
      quittingContinuationBestResponseValue reward
        (profile x y hx0 hx1 hy0 hy1) right|
  rw [profile_envelope_left, profile_envelope_right,
    profile_envelope_left, profile_envelope_right]
  rcases (profile_debtSum_eq_one_iff x y hx0 hx1 hy0 hy1).mp hminimum with
    rfl | rfl
  · have hright : |1 - (1 - lambda) - (1 - 1)| = lambda := by
      rw [show 1 - (1 - lambda) - (1 - 1) = lambda by ring,
        abs_of_nonneg hlambda0]
    rw [hright]
    exact le_max_right _ _
  · rw [sub_zero, abs_of_nonneg hlambda0]
    exact le_max_left _ _



end QuittingCommonSuffixCurvatureRegression

end GameTheory
