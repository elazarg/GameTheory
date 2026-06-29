/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.MultiRound.Syntax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Absent-Minded Driver

A compact finite formalization of the absent-minded-driver phenomenon.  The
protocol has one player and two indistinguishable decision rounds.  The payoff
calculus records the standard values: exiting at the first intersection gives
`0`, exiting at the second gives `4`, and continuing past both gives `1`.

The file is deliberately small.  It does not try to rebuild all extensive-form
machinery around the example; instead it connects the example to the
MultiRound no-absent-mindedness predicate and proves the real-valued
optimization facts that make the puzzle a time-consistency pathology.
-/

namespace GameTheory
namespace MultiRound

noncomputable section

/-! ## Protocol shape -/

/-- The driver's physical state. -/
inductive AMDState where
  | atFirst
  | atSecond
  | tookFirstExit
  | tookSecondExit
  | missedBoth
deriving DecidableEq, Repr

/-- The single observation seen at either intersection. -/
inductive AMDView where
  | intersection
deriving DecidableEq, Repr

/-- The driver's substantive actions.  In `MultiRound`, these are wrapped in
`Option`, with `none` treated like continuing for this example. -/
inductive AMDAction where
  | exit
  | continue
deriving DecidableEq, Repr

/-- The first indistinguishable intersection. -/
noncomputable def absentMindedRound₁ : Round 1 AMDState AMDView AMDAction Unit where
  signal := fun _ => PMF.pure fun _ => ()
  view := fun _ _ _ => AMDView.intersection
  transition := fun s a =>
    match s, a 0 with
    | AMDState.atFirst, some AMDAction.exit => AMDState.tookFirstExit
    | AMDState.atFirst, _ => AMDState.atSecond
    | _, _ => s

/-- The second indistinguishable intersection. -/
noncomputable def absentMindedRound₂ : Round 1 AMDState AMDView AMDAction Unit where
  signal := fun _ => PMF.pure fun _ => ()
  view := fun _ _ _ => AMDView.intersection
  transition := fun s a =>
    match s, a 0 with
    | AMDState.atSecond, some AMDAction.exit => AMDState.tookSecondExit
    | AMDState.atSecond, _ => AMDState.missedBoth
    | _, _ => s

/-- The two-round absent-minded-driver protocol. -/
noncomputable def absentMindedProtocol :
    MultiRoundGame 1 AMDState AMDView AMDAction Unit where
  init := AMDState.atFirst
  rounds := [absentMindedRound₁, absentMindedRound₂]

/-- The protocol violates the `ViewDeterminesRound` no-absent-mindedness
condition: both rounds can produce the same player view. -/
theorem absentMindedProtocol_not_viewDeterminesRound :
    ¬ absentMindedProtocol.ViewDeterminesRound := by
  intro h
  let k₁ : Fin absentMindedProtocol.rounds.length := ⟨0, by simp [absentMindedProtocol]⟩
  let k₂ : Fin absentMindedProtocol.rounds.length := ⟨1, by simp [absentMindedProtocol]⟩
  have hk : k₁ = k₂ := by
    exact h 0 k₁ k₂ AMDState.atFirst AMDState.atSecond () () (by
      simp [k₁, k₂, absentMindedProtocol, absentMindedRound₁, absentMindedRound₂])
  have hval : (0 : Nat) = 1 := congrArg Fin.val hk
  norm_num at hval

/-! ## Payoff calculus -/

/-- Payoff from terminal states in the standard absent-minded-driver example. -/
def absentMindedPayoff : AMDState → ℝ
  | AMDState.tookFirstExit => 0
  | AMDState.tookSecondExit => 4
  | AMDState.missedBoth => 1
  | AMDState.atFirst => 0
  | AMDState.atSecond => 0

/-- Ex-ante value when the driver continues at each indistinguishable
intersection with probability `p`. -/
def exAnteValue (p : ℝ) : ℝ :=
  4 * p - 3 * p ^ 2

/-- Path-probability form of `exAnteValue`: continue then exit at the second
intersection, or continue past both. -/
theorem exAnteValue_eq_path_sum (p : ℝ) :
    exAnteValue p = p * (1 - p) * 4 + p ^ 2 := by
  unfold exAnteValue
  ring_nf

/-- The ex-ante optimal continuation probability. -/
def exAnteOptimalContinue : ℝ := 2 / 3

/-- The ex-ante value is globally maximized at continuation probability `2/3`. -/
theorem exAnteValue_le_optimal (p : ℝ) :
    exAnteValue p ≤ exAnteValue exAnteOptimalContinue := by
  have hsq : 0 ≤ 3 * (p - exAnteOptimalContinue) ^ 2 := by
    nlinarith [sq_nonneg (p - exAnteOptimalContinue)]
  have hdiff :
      exAnteValue exAnteOptimalContinue - exAnteValue p =
        3 * (p - exAnteOptimalContinue) ^ 2 := by
    unfold exAnteValue exAnteOptimalContinue
    ring_nf
  have hnonneg : 0 ≤ exAnteValue exAnteOptimalContinue - exAnteValue p := by
    rw [hdiff]
    exact hsq
  linarith

/-- `2/3` is the *unique* ex-ante maximizer: any other continuation probability is
strictly worse (the optimality gap is `3·(p − 2/3)²`). -/
theorem exAnteValue_lt_optimal {p : ℝ} (hp : p ≠ exAnteOptimalContinue) :
    exAnteValue p < exAnteValue exAnteOptimalContinue := by
  have hdiff :
      exAnteValue exAnteOptimalContinue - exAnteValue p =
        3 * (p - exAnteOptimalContinue) ^ 2 := by
    unfold exAnteValue exAnteOptimalContinue
    ring_nf
  have hne : p - exAnteOptimalContinue ≠ 0 := sub_ne_zero.mpr hp
  have hpos : 0 < 3 * (p - exAnteOptimalContinue) ^ 2 := by positivity
  linarith

@[simp] theorem exAnteValue_optimal_value :
    exAnteValue exAnteOptimalContinue = 4 / 3 := by
  norm_num [exAnteValue, exAnteOptimalContinue]

/-- Decision-time value.  The first argument `p` is the continuation
probability used to form the arrival odds at the information set; the second
argument `q` is the continuation probability chosen for the indistinguishable
information set at decision time. -/
def decisionValue (p q : ℝ) : ℝ :=
  (exAnteValue q + p * (4 - 3 * q)) / (1 + p)

/-- The decision-time optimal continuation probability, given arrival odds
generated by prior continuation probability `p`. -/
def decisionOptimalContinue (p : ℝ) : ℝ :=
  (4 - 3 * p) / 6

/-- For positive arrival denominator, the decision-time value is maximized at
`decisionOptimalContinue p`. -/
theorem decisionValue_le_optimal {p q : ℝ} (hp : -1 < p) :
    decisionValue p q ≤ decisionValue p (decisionOptimalContinue p) := by
  have hden : 0 ≤ 1 + p := by linarith
  have hsq : 0 ≤ 3 * (q - decisionOptimalContinue p) ^ 2 := by
    nlinarith [sq_nonneg (q - decisionOptimalContinue p)]
  have hdiff :
      (exAnteValue (decisionOptimalContinue p) +
          p * (4 - 3 * decisionOptimalContinue p)) -
        (exAnteValue q + p * (4 - 3 * q)) =
          3 * (q - decisionOptimalContinue p) ^ 2 := by
    unfold exAnteValue decisionOptimalContinue
    ring_nf
  have hnum :
      exAnteValue q + p * (4 - 3 * q) ≤
        exAnteValue (decisionOptimalContinue p) +
          p * (4 - 3 * decisionOptimalContinue p) := by
    have hnonneg :
        0 ≤
          (exAnteValue (decisionOptimalContinue p) +
              p * (4 - 3 * decisionOptimalContinue p)) -
            (exAnteValue q + p * (4 - 3 * q)) := by
      rw [hdiff]
      exact hsq
    linarith
  unfold decisionValue
  exact div_le_div_of_nonneg_right hnum hden

/-- For positive arrival denominator, `decisionOptimalContinue p` is the *unique*
decision-time maximizer: any other `q` is strictly worse. -/
theorem decisionValue_lt_optimal {p q : ℝ} (hp : -1 < p)
    (hq : q ≠ decisionOptimalContinue p) :
    decisionValue p q < decisionValue p (decisionOptimalContinue p) := by
  have hden : 0 < 1 + p := by linarith
  have hden0 : (1 + p) ≠ 0 := ne_of_gt hden
  have hne : q - decisionOptimalContinue p ≠ 0 := sub_ne_zero.mpr hq
  have hsq : 0 < 3 * (q - decisionOptimalContinue p) ^ 2 := by positivity
  have key : decisionValue p (decisionOptimalContinue p) - decisionValue p q
      = 3 * (q - decisionOptimalContinue p) ^ 2 / (1 + p) := by
    unfold decisionValue exAnteValue decisionOptimalContinue
    field_simp
    ring
  have hpos : 0 < 3 * (q - decisionOptimalContinue p) ^ 2 / (1 + p) := div_pos hsq hden
  linarith

@[simp] theorem decisionOptimalContinue_at_exAnteOptimal :
    decisionOptimalContinue exAnteOptimalContinue = 1 / 3 := by
  norm_num [decisionOptimalContinue, exAnteOptimalContinue]

/-- The absent-minded-driver inconsistency: the ex-ante optimal continuation
probability is not the decision-time optimum induced by its own arrival odds. -/
theorem exAnteOptimalContinue_ne_decisionOptimal :
    exAnteOptimalContinue ≠ decisionOptimalContinue exAnteOptimalContinue := by
  norm_num [exAnteOptimalContinue, decisionOptimalContinue]

@[simp] theorem decisionValue_at_exAnte_and_decisionOptimal :
    decisionValue exAnteOptimalContinue (decisionOptimalContinue exAnteOptimalContinue) =
      9 / 5 := by
  norm_num [decisionValue, exAnteValue, exAnteOptimalContinue, decisionOptimalContinue]

@[simp] theorem decisionValue_at_exAnte_and_exAnteOptimal :
    decisionValue exAnteOptimalContinue exAnteOptimalContinue = 8 / 5 := by
  norm_num [decisionValue, exAnteValue, exAnteOptimalContinue]

/-- At the decision point, re-optimizing the indistinguishable information-set
mixture strictly improves over reusing the ex-ante optimum. -/
theorem decisionValue_exAnteOptimal_lt_decisionOptimal :
    decisionValue exAnteOptimalContinue exAnteOptimalContinue <
      decisionValue exAnteOptimalContinue
        (decisionOptimalContinue exAnteOptimalContinue) := by
  norm_num [decisionValue, exAnteValue, exAnteOptimalContinue, decisionOptimalContinue]

end

end MultiRound
end GameTheory
